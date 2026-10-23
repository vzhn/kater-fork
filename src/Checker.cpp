/*
 * KATER -- Automating Weak Memory Model Metatheory
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, you can access it online at
 * http://www.gnu.org/licenses/gpl-3.0.html.
 */

#include "Checker.hpp"

#include "Constraint.hpp"
#include "Counterexample.hpp"
#include "Error.hpp"
#include "KatModule.hpp"
#include "Logger.hpp"
#include "NFA.hpp"
#include "NFAUtils.hpp"
#include "Predicate.hpp"
#include "RegExp.hpp"
#include "RegExpUtils.hpp"
#include "Relation.hpp"
#include "Saturation.hpp"
#include "Statement.hpp"
#include "Utils.hpp"
#include "VSet.hpp"
#include "Visitor.hpp"

#include <algorithm>
#include <cassert>
#include <cstddef>
#include <cstdint>
#include <deque>
#include <execution>
#include <iostream>
#include <map>
#include <memory>
#include <optional>
#include <ranges>
#include <string>
#include <utility>
#include <vector>

#define DEBUG_TYPE "checker"

/*************************************************************
 *              Types and generic utils functions
 ************************************************************/

/* Allowed LHS of comp scheme: [A];po;[B] */
struct CompSchemeLHS {
	std::optional<PredicateSet> pre;
	std::optional<PredicateSet> post;
};

/* Allowed RHS of comp scheme: [A];po;[C];po;[B] */
struct CompSchemeRHS {
	std::optional<PredicateSet> pre;
	PredicateSet fence;
	std::optional<PredicateSet> post;
};

/*************************************************************
 *              Regexp utilities
 ************************************************************/

void expandRfs(SubsetConstraint &subsetC, const KatModule &module)
{
	/* We will expand rf on the LHS, but only if the RHS uses rfe/rfi */
	auto rhsHasRfiRfe = false;
	visitRE(subsetC.getRHSRef(), [&](auto &re) {
		auto *charRE = dynamic_cast<const CharRE *>(&*re);
		if (charRE && charRE->getLabel().getRelation().has_value() &&
		    (charRE->getLabel().getRelation()->getID() ==
			     Relation::createBuiltin(Relation::BuiltinID::rfe).getID() ||
		     charRE->getLabel().getRelation()->getID() ==
			     Relation::createBuiltin(Relation::BuiltinID::rfi).getID()))
			rhsHasRfiRfe = true;
	});
	if (!rhsHasRfiRfe)
		return;

	auto rf = module.getRegisteredRE("rf");

	auto rfe = module.getRegisteredRE("rfe")->clone();
	auto rfi = module.getRegisteredRE("rfi")->clone();
	auto alt = AltRE::createOpt(std::move(rfe), std::move(rfi));
	replaceREWith(subsetC.getLHSRef(), rf, &*alt);
}

std::pair<PredicateSet, unsigned> collectPredicateKids(const RegExp *re, unsigned startIdx)
{
	PredicateSet result;

	auto i = startIdx;
	while (i < re->getNumKids() && re->getKid(i)->isPredicate()) {
		if (i == 0)
			result = dynamic_cast<const CharRE *>(re->getKid(i))
					 ->getLabel()
					 .getPreChecks();
		else
			result.insert(dynamic_cast<const CharRE *>(re->getKid(i))
					      ->getLabel()
					      .getPreChecks());
		++i;
	}
	return {result, i};
}

/*************************************************************
 *              NFA utilities
 ************************************************************/

void removeConsecutivePredicates(NFA &nfa, const Theory &theory)
{
	std::for_each(nfa.states_begin(), nfa.states_end(), [&](auto &s) {
		nfa.removeTransitionsIf(
			&*s, [&](auto &t) { return t.dest == &*s && t.label.isPredicate(); });
	});

	/* Collect states w/ incoming both preds + rels */
	std::vector<NFA::State *> toDuplicate;
	std::for_each(nfa.states_begin(), nfa.states_end(), [&](auto &s) {
		if (std::any_of(s->in_begin(), s->in_end(),
				[&](auto &t) { return t.label.isPredicate(); }) &&
		    std::any_of(s->in_begin(), s->in_end(),
				[&](auto &t) { return !t.label.isPredicate(); })) {
			toDuplicate.push_back(&*s);
		}
	});

	std::for_each(toDuplicate.begin(), toDuplicate.end(), [&](auto &s) {
		nfa.splitState(s, [&](auto &t) { return t.label.isPredicate(); });
	});

	addTransitivePredicateEdges(nfa, theory);

	std::for_each(nfa.states_begin(), nfa.states_end(), [&](auto &s) {
		nfa.removeTransitionsIf(
			&*s, [&](auto &t) { return t.dest == &*s && t.label.isPredicate(); });
	});

	/* NF: ensure that if S -ε-> S' and S' is final, S is final too */
	for (auto &sUP : nfa.states()) {
		for (auto &t : sUP->outs() | std::views::filter([&](auto &t) {
				       return t.dest->isAccepting() && t.label.isTruePredicate();
			       })) {
			nfa.makeAccepting(&*sUP);
		}
	}
}

void normalize(NFA &nfa, const Theory &theory)
{
	simplify(nfa, theory);
	saturateDomains(nfa, theory);
	breakToParts(nfa);
	removeConsecutivePredicates(nfa, theory);
	removeDeadStates(nfa);
}

void reduce(NFA &nfa, const Theory &theory)
{
	simplify(nfa, theory);
	std::for_each(nfa.accept_begin(), nfa.accept_end(), [&](auto &s) {
		nfa.removeTransitionsIf(&*s, [&](const NFA::Transition &t) {
			return std::any_of(nfa.start_begin(), nfa.start_end(),
					   [&](auto &q) { return q->hasOutgoingTo(t.dest); });
		});
	});
	simplify(nfa, theory);
}

void pruneNFA(NFA &nfa, const NFA &other, const Theory &theory)
{
	std::vector<Relation> orels;
	std::vector<PredicateSet> opreds;
	std::for_each(other.states_begin(), other.states_end(), [&](auto &s) {
		std::for_each(s->out_begin(), s->out_end(), [&](auto &t) {
			if (!t.label.isPredicate()) {
				orels.push_back(*t.label.getRelation());
			} else {
				opreds.push_back(t.label.getPreChecks());
			}
		});
	});

	std::sort(opreds.begin(), opreds.end());
	opreds.erase(std::unique(opreds.begin(), opreds.end()), opreds.end());
	std::sort(orels.begin(), orels.end());
	orels.erase(std::unique(orels.begin(), orels.end()), orels.end());

	std::for_each(nfa.states_begin(), nfa.states_end(), [&](auto &s) {
		nfa.removeTransitionsIf(&*s, [&](auto &t) {
			return (t.label.isRelation() &&
				std::none_of(orels.begin(), orels.end(),
					     [&](auto &r) {
						     return theory.isIncludedIn(
							     r, *t.label.getRelation());
					     })) ||
			       (t.label.isPredicate() &&
				std::none_of(t.label.getPreChecks().begin(),
					     t.label.getPreChecks().end(),
					     [&](auto &p) { return p.isComplement(); }) &&
				std::none_of(opreds.begin(), opreds.end(), [&](auto &p) {
					return theory.isIncludedIn(p, t.label.getPreChecks());
				}));
		});
	});
}

/*************************************************************
 *             Assumption expanding/saturation
 ************************************************************/

std::pair<bool, CompSchemeLHS> extractCompLHSInfo(const RegExp *lRE, const RegExp *poRE)
{
	CompSchemeLHS result;

	auto *seqRE = dynamic_cast<const SeqRE *>(lRE);
	if (!seqRE)
		return {false, result};

	auto i = 0U;
	auto [pre, i1] = collectPredicateKids(seqRE, i);
	if (i1 > i)
		result.pre = pre;
	i = i1;

	if (i >= seqRE->getNumKids() || *seqRE->getKid(i) != *poRE)
		return {false, result};
	++i;

	auto [post, i2] = collectPredicateKids(seqRE, i);
	if (i2 > i)
		result.post = post;
	i = i2;
	return {true, result};
}

std::pair<bool, CompSchemeRHS> extractCompRHSInfo(const RegExp *rRE, const RegExp *poRE)
{
	CompSchemeRHS result;

	auto *seqRE = dynamic_cast<const SeqRE *>(rRE);
	if (!seqRE)
		return {false, result};

	auto i = 0U;
	auto [pre, i1] = collectPredicateKids(seqRE, i);
	if (i1 > i)
		result.pre = pre;
	i = i1;

	if (i >= seqRE->getNumKids() || *seqRE->getKid(i) != *poRE) {
		return {false, result};
	}
	++i;

	auto [fence, i2] = collectPredicateKids(seqRE, i);
	if (i == i2)
		return {false, result};
	result.fence = fence;
	i = i2;

	if (i >= seqRE->getNumKids() || *seqRE->getKid(i) != *poRE) {
		return {false, result};
	}
	++i;

	auto [post, i3] = collectPredicateKids(seqRE, i);
	if (i3 > i)
		result.post = post;
	i = i3;
	return {true, result};
}

std::pair<bool, CompSchemeRHS> isSupportedCompScheme(const SubsetConstraint *assm,
						     const RegExp *poRE)
{
	auto [lok, lhs] = extractCompLHSInfo(assm->getLHS(), poRE);
	auto [rok, rhs] = extractCompRHSInfo(assm->getRHS(), poRE);

	if (!lok || !rok)
		return {false, rhs};
	if (rhs.pre.has_value() && lhs.pre != rhs.pre)
		return {false, rhs};
	if (rhs.post.has_value() && lhs.post != rhs.post)
		return {false, rhs};

	rhs.pre = lhs.pre;
	rhs.post = lhs.post;
	return {true, rhs};
}

NFA createCompilationNFA(const CompSchemeRHS &rhs, const Theory &theory)
{
	std::vector<std::unique_ptr<RegExp>> disj;
	for (auto &p : rhs.fence) {
		auto pc = p;
		pc.complement();
		disj.push_back(CharRE::create(TransLabel(std::nullopt, {pc})));
	}
	assert(!disj.empty());
	auto fenceExp = disj.size() == 1 ? std::move(disj[0]) : AltRE::create(std::move(disj));
	auto po = CharRE::create(TransLabel(Relation::createBuiltin(Relation::BuiltinID::po)));
	PredicateSet pre = rhs.pre.has_value() ? *rhs.pre : PredicateSet{};
	PredicateSet post = rhs.post.has_value() ? *rhs.post : PredicateSet{};

	auto reC = SeqRE::createOpt(
		CharRE::create(TransLabel(std::nullopt, pre)),
		StarRE::createOpt(SeqRE::createOpt(po->clone(), std::move(fenceExp))), po->clone(),
		CharRE::create(TransLabel(std::nullopt, post)));

	auto lNFA = reC->toNFA();
	normalize(lNFA, theory);
	return lNFA;
}

/* Saturates RHS with ASSM; returns whether the assumption was of a supported shape */
static auto expandSubsetAssumption(NFA &rhs, const SubsetConstraint *assm, const KatModule &module)
	-> bool
{
	auto &theory = module.getTheory();
	auto *lRE = assm->getLHS();
	auto *rRE = assm->getRHS();

	/* If `any` is used in the assumption, realize it as `any*` */
	auto lNFA = starifyAny(lRE->clone())->toNFA();
	normalize(lNFA, theory);

	/* Handle `A <= 0` assumption */
	if (rRE->isFalse()) {
		saturateEmpty(rhs, std::move(lNFA));
		return true;
	}

	/* Handle `A <= id` assumption */
	if (*rRE == *RegExp::createId()) {
		saturateID(rhs, std::move(lNFA));
		return true;
	}

	/* Transform `A ; A <= A` to `transitive A` */
	auto *seqRE = dynamic_cast<const SeqRE *>(lRE);
	if (seqRE && *rRE == *seqRE->getKid(0) && *rRE == *seqRE->getKid(1) &&
	    dynamic_cast<const CharRE *>(rRE)) {
		auto rel = *dynamic_cast<const CharRE *>(rRE)->getLabel().getRelation();
		saturateTransitive(rhs, rel);
		return true;
	}
	/* Transform `A+ <= A` to `transitive A` */
	auto *plusRE = dynamic_cast<const PlusRE *>(&*lRE);
	if (plusRE && *rRE == *plusRE->getKid(0) && dynamic_cast<const CharRE *>(rRE)) {
		auto rel = *dynamic_cast<const CharRE *>(rRE)->getLabel().getRelation();
		saturateTransitive(rhs, rel);
		return true;
	}

	// FIXME: Also discard A <= A{*,+}
	/* Discard `A <= A?` assumption */
	auto *charRE = dynamic_cast<const CharRE *>(&*lRE);
	if (charRE && dynamic_cast<const QMarkRE *>(&*rRE) && *rRE->getKid(0) == *charRE) {
		return true;
	}
	/* Handle `A <= builtin` assumption */
	auto *charRHS = dynamic_cast<const CharRE *>(&*rRE);
	if (charRHS) {
		saturateBuiltin(rhs, *dynamic_cast<const CharRE *>(rRE)->getLabel().getRelation(),
				std::move(lNFA), theory);
		return true;
	}
	/* Handle `[A];po;[B] <= [A];po;[C];po;[B]` assumption */
	auto [supported, compRHS] = isSupportedCompScheme(assm, module.getRegisteredRE("po"));
	if (supported) {
		saturateEmpty(rhs, createCompilationNFA(compRHS, theory));
		return true;
	}

	return false;
}

/* Built-in assumptions become unsupported only once optimizeModuleForExport()
 * rewrites the builtins underneath them, so they are debug-only noise */
static void warnUnsupportedAssumption(const AssumeStatement *assm, const Theory &theory)
{
	const auto msg =
		"ignoring unsupported assumption " + toString(*assm->getConstraint(), theory);
	if (!assm->getDbgInfo().has_value()) {
		// NOLINTNEXTLINE(cppcoreguidelines-avoid-do-while): macro
		KATER_DEBUG(LOG(VerbosityLevel::Note) << "built-in: " << msg;);
		return;
	}
	LOG_ONCE_AT(msg, VerbosityLevel::Warning, assm->getDbgInfo()) << msg;
}

void expandAssumption(NFA &rhs, const AssumeStatement *assm, const KatModule &module)
{
	assert(assm);

	auto *cst = assm->getConstraint();
	if (const auto *cc = dynamic_cast<const EqualityConstraint *>(cst)) {
		auto invC = SubsetConstraint::create(cc->getRHS()->clone(), cc->getLHS()->clone(),
						     cc->sameEnds(), cc->rotated());
		auto fwd = expandSubsetAssumption(rhs, cc, module);
		auto bwd = expandSubsetAssumption(rhs, &*invC, module);
		if (!fwd || !bwd)
			warnUnsupportedAssumption(assm, module.getTheory());
		return;
	}
	if (const auto *tc = dynamic_cast<const TotalityConstraint *>(cst)) {
		saturateTotal(rhs,
			      *dynamic_cast<const CharRE *>(tc->getRE())->getLabel().getRelation());
		return;
	}
	// FIXME: What about SubsetSameEnds???
	if (const auto *ec = dynamic_cast<const SubsetConstraint *>(cst)) {
		if (!expandSubsetAssumption(rhs, ec, module))
			warnUnsupportedAssumption(assm, module.getTheory());
		return;
	}
	warnUnsupportedAssumption(assm, module.getTheory());
}

/*************************************************************
 *              Inclusion checking
 ************************************************************/

void completeCounterexample(const NFA &nfa, NFA::State *s, Counterexample &cex)
{
	if (s->isAccepting())
		return;

	std::deque<std::pair<NFA::State *, Counterexample>> worklist(1, {s, cex});
	std::vector<uint8_t> visited(nfa.getNumStates(), 0);
	visited[s->getId()] = 1;

	while (!worklist.empty()) {
		auto [s, c] = worklist.front();
		worklist.pop_front();

		if (s->isAccepting()) {
			cex = c;
			break;
		}

		for (auto it = s->out_begin(); it != s->out_end(); ++it) {
			auto nextCex(cex);
			nextCex.extend(it->label);

			if (visited[it->dest->getId()] != 0)
				continue;

			visited[it->dest->getId()] = 1;
			worklist.emplace_back(it->dest, nextCex);
		}
	}
}

auto cexNote(const Counterexample &cex, const Theory &theory) -> std::string
{
	return "\n  counterexample: " + toString(cex, theory);
}

/* The negated pre-checks on each state's outgoing transitions, indexed by state ID */
static auto collectNegatedOutgoing(const NFA &nfa) -> std::vector<VSet<Predicate>>
{
	std::vector<VSet<Predicate>> negated(nfa.getNumStates());

	for (const auto &s : nfa.states()) {
		for (auto &t : s->outs()) {
			auto negIt = std::ranges::find_if(
				t.label.getPreChecks(), [&](auto &p) { return p.isComplement(); });
			if (negIt != t.label.getPreChecks().end())
				negated[s->getId()].insert(*negIt);
		}
	}
	return negated;
}

static auto collectNegatedOutgoing(const VSet<unsigned> &states,
				   const std::vector<VSet<Predicate>> &negated) -> VSet<Predicate>
{
	VSet<Predicate> result;

	for (auto id : states)
		result.insert(negated[id]);
	return result;
}

/*
 * The right-hand automaton, arranged for the inclusion check: its distinct
 * labels, and each state's transitions as (label index, destination ID).
 *
 * next() used to ask the theory whether the left-hand label includes the label
 * of every transition it crossed. An automaton has tens of distinct labels and
 * the search crosses millions of transitions, so we ask once per pair of labels
 * instead and remember the answer.
 */
class RHSIndex {

public:
	RHSIndex(const NFA &nfa, const Theory &theory)
		: theory(&theory), outs(nfa.getNumStates()), accepting(nfa.getNumStates())
	{
		for (const auto &s : nfa.states())
			for (const auto &t : s->outs())
				labels.insert(t.label);
		for (const auto &s : nfa.states()) {
			accepting[s->getId()] = static_cast<uint8_t>(s->isAccepting());
			for (const auto &t : s->outs())
				outs[s->getId()].emplace_back(indexOf(t.label), t.dest->getId());
		}
	}

	/* The states STATES can move to by a transition whose label LABEL includes */
	auto next(const TransLabel &label, const VSet<unsigned> &states) const -> VSet<unsigned>
	{
		const auto &included = includedLabels(label);
		std::vector<unsigned> result;

		for (auto id : states)
			for (auto [index, dest] : outs[id])
				if (included[index] != 0)
					result.push_back(dest);
		std::ranges::sort(result);
		result.erase(std::ranges::unique(result).begin(), result.end());
		return {std::move(result)};
	}

	[[nodiscard]] auto anyAccepting(const VSet<unsigned> &states) const -> bool
	{
		return std::ranges::any_of(states,
					   [&](auto id) -> bool { return accepting[id] != 0; });
	}

private:
	auto indexOf(const TransLabel &label) const -> unsigned
	{
		return static_cast<unsigned>(std::ranges::lower_bound(labels, label) -
					     labels.begin());
	}

	/* Which of the automaton's labels LABEL includes, indexed as above */
	auto includedLabels(const TransLabel &label) const -> const std::vector<uint8_t> &
	{
		auto it = included.find(label);
		if (it != included.end())
			return it->second;

		std::vector<uint8_t> answers(labels.size());
		for (auto i = 0U; i < labels.size(); i++)
			answers[i] = static_cast<uint8_t>(
				theory->isIncludedIn(label, labels[static_cast<int>(i)]));
		return included.emplace(label, std::move(answers)).first->second;
	}

	const Theory *theory;
	VSet<TransLabel> labels;
	std::vector<std::vector<std::pair<unsigned, unsigned>>> outs;
	std::vector<uint8_t> accepting;
	mutable std::map<TransLabel, std::vector<uint8_t>> included;
};

std::vector<TransLabel> maybeSplitToComplements(const TransLabel &label,
						const VSet<Predicate> &negated,
						const Theory &theory)
{
	std::vector<TransLabel> result;

	for (const auto &p : negated) {
		/* First try with p */
		if (theory.composes(label, TransLabel(std::nullopt, {p}))) {
			auto l = label;
			l.merge(TransLabel(std::nullopt, {p}));
			result.push_back(l);
		}
		/* Then also with ~p */
		auto pneg = Predicate(p).complement();
		if (theory.composes(label, TransLabel(std::nullopt, {pneg}))) {
			auto l = label;
			l.merge(TransLabel(std::nullopt, {p}));
			result.push_back(l);
		}
	}

	/* If there were no negated transitions, or nothing composes w/ label, just give up */
	if (negated.empty())
		result.push_back(label);
	return result;
}

class SimState {

public:
	SimState() = delete;
	SimState(NFA::State *lhs, VSet<unsigned> rhs) : lhs(lhs), rhs(std::move(rhs)) {}

	SimState(const SimState &) = default;
	SimState(SimState &&) = default;

	auto operator=(const SimState &) -> SimState & = default;
	auto operator=(SimState &&) -> SimState & = default;

	[[nodiscard]] auto getLHS() const -> NFA::State * { return lhs; }
	[[nodiscard]] auto getRHS() const -> const VSet<unsigned> & { return rhs; }

	[[nodiscard]] auto isLHSAccepting() const -> bool { return lhs->isAccepting(); }

private:
	NFA::State *lhs;
	VSet<unsigned> rhs;
};

/*
 * The simulation on the left-hand automaton: simulates(s, p) holds when s
 * accepts everything p does. relatedTo(p) lists the states the simulation puts
 * p in either relation with, so that an antichain insertion for p can visit
 * their buckets and no others.
 */
class Simulation {

public:
	Simulation(NFA &nfa)
		: nrStates(nfa.getNumStates()), similar(findSimilarStates(nfa)), related(nrStates)
	{
		for (auto pid = 0U; pid < nrStates; pid++)
			for (auto sid = 0U; sid < nrStates; sid++)
				if (simulates(sid, pid) || simulates(pid, sid))
					related[pid].push_back(sid);
	}

	/* Whether SIMULATOR accepts everything SIMULATED does */
	[[nodiscard]] auto simulates(unsigned simulator, unsigned simulated) const -> bool
	{
		return similar[(static_cast<size_t>(simulated) * nrStates) + simulator] != 0;
	}

	[[nodiscard]] auto relatedTo(unsigned pid) const -> const std::vector<unsigned> &
	{
		return related[pid];
	}

private:
	unsigned nrStates;
	std::vector<uint8_t> similar;
	std::vector<std::vector<unsigned>> related;
};

/*
 * Antichain insertion for simulation-based language inclusion.
 *
 * Attempts to insert (p, P) into the antichain, which contains (s, Q):
 *   - if s simulates p and Q ⊆ P: insertion is skipped.
 *   - if p simulates s and P ⊆ Q: (s, Q) is pruned.
 *
 * Returns true if the pair was inserted, false if it was subsumed.
 *
 * See: Abdulla et al., "When Simulations Meet Antichains", Optimization V2.
 */
static auto antichainInsert(const SimState &state,
			    std::vector<std::vector<VSet<unsigned>>> &visited,
			    const Simulation &sim) -> bool
{
	const auto pid = state.getLHS()->getId();

	for (auto sid : sim.relatedTo(pid)) {
		const auto subsumes = sim.simulates(sid, pid);
		const auto subsumed = sim.simulates(pid, sid);
		auto &entries = visited[sid];

		for (auto it = entries.begin(); it != entries.end();) {
			if (subsumes && it->subsetOf(state.getRHS()))
				return false;
			if (subsumed && state.getRHS().subsetOf(*it))
				it = entries.erase(it);
			else
				++it;
		}
	}
	visited[pid].push_back(state.getRHS());
	return true;
}

auto Checker::isDFASubLanguageOfNFA(NFA &nfa, const NFA &other) const -> InclusionResult
{
	KATER_DEBUG(std::cout << "Checking inclusion between automata:" << std::endl;
		    std::cout << nfa << "and " << other << std::endl;);

	if (other.getNumStarting() == 0) {
		Counterexample cex;
		return {.result = nfa.acceptsNoString(cex), .cex = cex};
	}

	auto negatedOf = collectNegatedOutgoing(other);
	const RHSIndex rhs(other, getModule().getTheory());
	const Simulation sim(nfa);
	/* The antichain, bucketed by the ID of the left-hand state it belongs to */
	std::vector<std::vector<VSet<unsigned>>> visited(nfa.getNumStates());
	std::deque<std::pair<SimState, Counterexample>> workList;

	std::vector<unsigned> startIDs;
	std::for_each(other.start_begin(), other.start_end(),
		      [&](auto *s) -> void { startIDs.push_back(s->getId()); });
	std::ranges::sort(startIDs);
	VSet<unsigned> start(std::move(startIDs));

	std::for_each(nfa.start_begin(), nfa.start_end(), [&](auto *s1) {
		visited[s1->getId()].push_back(start);
		workList.push_back({{s1, start}, Counterexample()});
	});
	while (!workList.empty()) {
		auto [state, cex] = std::move(workList.front());
		workList.pop_front();

		if (state.isLHSAccepting() && !rhs.anyAccepting(state.getRHS())) {
			cex.setType(Counterexample::Type::ANA);
			return {.result = false, .cex = cex};
		}

		auto negated = collectNegatedOutgoing(state.getRHS(), negatedOf);
		for (auto &t : state.getLHS()->outs()) {

			auto nextCex(cex);
			nextCex.extend(t.label);

			auto labels =
				maybeSplitToComplements(t.label, negated, getModule().getTheory());
			for (auto &l : labels) {
				auto nextRHS = rhs.next(l, state.getRHS());

				/* If no matching step has been found, report a counterexample */
				if (nextRHS.empty()) {
					nextCex.setType(Counterexample::Type::TUT);
					completeCounterexample(nfa, t.dest, nextCex);
					return {.result = false, .cex = nextCex};
				}

				/* Proceed if the state (or a similar one) has not been examined */
				SimState next = {t.dest, std::move(nextRHS)};
				if (!antichainInsert(next, visited, sim))
					continue;
				workList.emplace_back(std::move(next), nextCex);
			}
		}
	}
	return {.result = true, .cex = {}};
}

auto Checker::checkInclusion(SubsetConstraint &subsetC) const -> InclusionResult
{
	auto &module = getModule();
	auto &theory = module.getTheory();

	expandRfs(subsetC, module);

	auto nfa1 = subsetC.getLHS()->toNFA();
	normalize(nfa1, theory);
	removeSimilarTransitions(nfa1);
	if (subsetC.sameEnds()) {
		saturateInitFinalPreds(nfa1, theory);
		saturateLoc(nfa1, theory);
	}
	removeSimilarTransitions(nfa1);
	auto lhs = nfa1.to_DFA().first;

	auto nfa2 = subsetC.getRHS()->toNFA();
	normalize(nfa2, theory);
	for (const auto &assm : theory.assumes()) {
		expandAssumption(nfa2, &*assm, module);
		normalize(nfa2, theory);
	}
	pruneNFA(nfa2, lhs, theory);
	removeDeadStates(nfa2);
	normalize(nfa2, theory);
	if (subsetC.rotated()) {
		saturateRotate(nfa2, theory);
		normalize(nfa2, theory);
	}
	/* doing another similarity pass here would
	 * further minimize the NFA, but minimizing
	 * doesn't seem to help. The remaining time
	 * is determined by the LHS anyway, and these
	 * passes are costly */
	return isDFASubLanguageOfNFA(lhs, nfa2);
}

auto Checker::checkAssertion(Constraint &cst) -> InclusionResult
{
	if (getOptions().trace) {
		std::cerr << "Checking assertion " << WithTheory(cst, getTheory()) << "\n";
	}

	InclusionResult result;
	auto visitor = make_visitor(
		type_list<SubsetConstraint, EqualityConstraint>{},
		[&](const SubsetConstraint &sc) {
			result = checkInclusion(const_cast<SubsetConstraint &>(sc));
		},
		[&](const EqualityConstraint &ec) {
			result = checkInclusion(const_cast<EqualityConstraint &>(ec));
			if (result.result) {
				auto invC = SubsetConstraint::create(ec.getRHS()->clone(),
								     ec.getLHS()->clone(),
								     ec.sameEnds(), ec.rotated());
				result = checkInclusion(*invC);
			}
		});
	visitor(cst);
	return result;
}

auto Checker::checkAssertions() -> bool
{
	/*
	 * First, simplify the module.
	 * TODO: In principle, we could optimize the REs too; if we
	 * decide to do so, the relevant routines should be placed in
	 * a new file.
	 */
	getModule().getTheory().simplify();

	/* Helper function to dispatch checkers as the different policies do not share a type */
	auto maybe_parallelize = [&]<typename F>(F f) {
#ifdef __cpp_lib_execution
		return getOptions().parallel ? f(std::execution::par_unseq)
					     : f(std::execution::seq);
#else
		return f(false); // ifdef types don't match but this is OK (false remains unused)
#endif
	};

	/* The parallel region only writes its own slot */
	auto asserts = module->asserts();
	std::vector<std::optional<Counterexample>> cexs(asserts.size());
	maybe_parallelize([&](auto policy) {
		std::transform(
#ifdef __cpp_lib_execution
			policy,
#endif
			asserts.begin(), asserts.end(), cexs.begin(),
			[&](auto &assert) -> std::optional<Counterexample> {
				auto [ok, cex] = checkAssertion(*assert->getConstraint());
				return ok ? std::nullopt : std::optional(cex);
			});
	});

	/* Print all counterexamples in declaration order */
	auto status = true;
	for (auto i = 0U; i < cexs.size(); i++) {
		if (!cexs[i].has_value())
			continue;
		LOG_AT(VerbosityLevel::Error, asserts[i]->getDbgInfo())
			<< "assertion does not hold" << cexNote(*cexs[i], getTheory());
		status = false;
	}
	return status;
}

auto Checker::isPPOIntersectionInPPO(const AcyclicConstraint *acyc) const -> InclusionResult
{
	auto &theory = getModule().getTheory();
	auto nfa = acyc->getRE()->toNFA();

	auto poNFA = getModule().getRegisteredRE("po")->toNFA();
	normalize(poNFA, theory);
	removeSimilarTransitions(poNFA);
	auto polocNFA = getModule().getRegisteredRE("po-loc")->toNFA();
	normalize(polocNFA, theory);
	removeSimilarTransitions(polocNFA);

	nfa.star();
	normalize(nfa, theory);
	removeSimilarTransitions(nfa);

	nfa.clearAllStarting();
	nfa.clearAllAccepting();
	VSet<NFA::State *> toSplit;
	for (auto &sUP : nfa.states()) {
		for (auto &t : sUP->ins()) {
			if (t.label.isRelation() && theory.isEco(t.label)) {
				toSplit.insert(&*sUP);
			}
		}
	}
	for (auto *s : toSplit) {
		auto *d = nfa.splitState(s, [&](auto &t) { return theory.isEco(t.label); });
		for (auto &t : s->ins())
			nfa.makeAccepting(t.dest);
	}
	for (auto &sUP :
	     nfa.states() | std::views::filter([&](auto &sUP) {
		     return sUP->hasAllOutPredicates() && // !sUP->isAccepting() &&
			    std::none_of(sUP->out_begin(), sUP->out_end(),
					 [&](auto &t) { return t.dest->isAccepting(); });
	     })) {
		nfa.makeStarting(&*sUP);
	}
	for (auto &sUP : nfa.states())
		nfa.removeTransitionsIf(&*sUP, [&](auto &t) {
			return t.label.isRelation() && theory.isEco(t.label);
		});

	normalize(nfa, theory);
	removeSimilarTransitions(nfa);

	auto lhs = nfa.to_DFA().first;

	auto nfa2 = AltRE::createOpt(
			    SeqRE::createOpt(
				    StarRE::createOpt(CharRE::create(TransLabel(
					    Relation::createBuiltin(Relation::BuiltinID::any)))),
				    getModule().createPPORF(),
				    StarRE::createOpt(CharRE::create(TransLabel(
					    Relation::createBuiltin(Relation::BuiltinID::any))))),
			    RegExp::createId())
			    ->toNFA();
	normalize(nfa2, theory);
	for (const auto &assm : theory.assumes()) {
		expandAssumption(nfa2, &*assm, getModule());
		normalize(nfa2, theory);
	}
	pruneNFA(nfa2, lhs, theory);
	removeDeadStates(nfa2);
	normalize(nfa2, theory);
	return isDFASubLanguageOfNFA(lhs, nfa2);
}
