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
#include <set>
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

/* The word [A];po;[C];po;[B] of a compilation scheme */
static auto compilationWord(const CompSchemeRHS &rhs) -> std::vector<TransLabel>
{
	auto po = TransLabel(Relation::createBuiltin(Relation::BuiltinID::po));
	std::vector<TransLabel> word;
	if (rhs.pre.has_value())
		word.emplace_back(std::nullopt, *rhs.pre);
	word.push_back(po);
	word.emplace_back(std::nullopt, rhs.fence);
	word.push_back(po);
	if (rhs.post.has_value())
		word.emplace_back(std::nullopt, *rhs.post);
	return word;
}

using Passes = std::vector<Checker::Pass>;

/* Saturates RHS with ASSM; returns whether the assumption was of a supported
 * shape. With PASSES, records there the saturation and its evidence */
static auto expandSubsetAssumption(NFA &rhs, const SubsetConstraint *assm, const KatModule &module,
				   Passes *passes) -> bool
{
	auto &theory = module.getTheory();
	auto *lRE = assm->getLHS();
	auto *rRE = assm->getRHS();

	/* `A & id <= B` only says something about the cycles of A, and no
	 * saturation below can use that: `r & id <= 0` is not `r <= 0` */
	if (assm->sameEnds() || assm->rotated())
		return false;

	/* The evidence of the saturation applied below, when recorded */
	std::optional<SaturationEvidence> ev;
	if (passes != nullptr)
		ev.emplace();
	auto *evidence = ev ? &*ev : nullptr;
	auto record = [&](const char *name) {
		if (passes == nullptr)
			return;
		passes->push_back({.name = name, .evidence = std::move(ev), .result = copy(rhs)});
		rhs.resetOrigins();
	};

	/* If `any` is used in the assumption, realize it as `any*` */
	auto lNFA = starifyAny(lRE->clone())->toNFA();
	normalize(lNFA, theory);

	/* Handle `A <= 0` assumption */
	if (rRE->isFalse()) {
		saturateEmpty(rhs, std::move(lNFA), evidence);
		record("saturateEmpty");
		return true;
	}

	/* Handle `A <= id` assumption */
	if (*rRE == *RegExp::createId()) {
		saturateID(rhs, std::move(lNFA), evidence);
		record("saturateID");
		return true;
	}

	/* Transform `A ; A <= A` to `transitive A` */
	auto *seqRE = dynamic_cast<const SeqRE *>(lRE);
	if (seqRE && *rRE == *seqRE->getKid(0) && *rRE == *seqRE->getKid(1) && rRE->isRelation()) {
		auto rel = *dynamic_cast<const CharRE *>(rRE)->getLabel().getRelation();
		saturateTransitive(rhs, rel, evidence);
		record("saturateTransitive");
		return true;
	}
	/* Transform `A+ <= A` to `transitive A` */
	auto *plusRE = dynamic_cast<const PlusRE *>(&*lRE);
	if (plusRE && *rRE == *plusRE->getKid(0) && rRE->isRelation()) {
		auto rel = *dynamic_cast<const CharRE *>(rRE)->getLabel().getRelation();
		saturateTransitive(rhs, rel, evidence);
		record("saturateTransitive");
		return true;
	}

	// FIXME: Also discard A <= A{*,+}
	/* Discard `A <= A?` assumption */
	auto *charRE = dynamic_cast<const CharRE *>(&*lRE);
	if (charRE && dynamic_cast<const QMarkRE *>(&*rRE) && *rRE->getKid(0) == *charRE) {
		return true;
	}
	/* Handle `A <= builtin` assumption; `A <= [P]` gives `A <= id` */
	auto *charRHS = dynamic_cast<const CharRE *>(&*rRE);
	if (charRHS && charRHS->getLabel().isPredicate()) {
		saturateID(rhs, std::move(lNFA), evidence);
		record("saturateID");
		return true;
	}
	if (charRHS) {
		saturateBuiltin(rhs, *charRHS->getLabel().getRelation(), std::move(lNFA), theory,
				evidence);
		record("saturateBuiltin");
		return true;
	}
	/* Handle `[A];po;[B] <= [A];po;[C];po;[B]` assumption: wherever the RHS
	 * reads [A];po;[C];po;[B], it may read [A];po;[B], i.e. [A];po+;[B] as
	 * po is transitive. The + lets the shortcut read the po-chains of LHSs */
	auto [supported, compRHS] = isSupportedCompScheme(assm, module.getRegisteredRE("po"));
	if (supported) {
		auto chain = SeqRE::createOpt(
			CharRE::create(
				TransLabel(std::nullopt, compRHS.pre.value_or(PredicateSet{}))),
			PlusRE::createOpt(module.getRegisteredRE("po")->clone()),
			CharRE::create(
				TransLabel(std::nullopt, compRHS.post.value_or(PredicateSet{}))));
		auto chainNFA = chain->toNFA();
		normalize(chainNFA, theory);
		saturateSubword(rhs, chainNFA, compilationWord(compRHS), theory, evidence);
		record("saturateSubword");
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

/* Saturates RHS with ASSM. With PASSES, records there each saturation and its evidence */
void expandAssumption(NFA &rhs, const AssumeStatement *assm, const KatModule &module,
		      Passes *passes = nullptr)
{
	assert(assm);

	auto *cst = assm->getConstraint();
	if (const auto *cc = dynamic_cast<const EqualityConstraint *>(cst)) {
		auto invC = SubsetConstraint::create(cc->getRHS()->clone(), cc->getLHS()->clone(),
						     cc->sameEnds(), cc->rotated());
		auto fwd = expandSubsetAssumption(rhs, cc, module, passes);
		auto bwd = expandSubsetAssumption(rhs, &*invC, module, passes);
		if (!fwd || !bwd)
			warnUnsupportedAssumption(assm, module.getTheory());
		return;
	}
	if (const auto *tc = dynamic_cast<const TotalityConstraint *>(cst)) {
		/* Only a relation of its own can be total */
		const auto *charRE = dynamic_cast<const CharRE *>(tc->getRE());
		if (charRE == nullptr || !charRE->getLabel().isRelation()) {
			warnUnsupportedAssumption(assm, module.getTheory());
			return;
		}
		/* total r: r is a strict total order (the Kater paper, Prop. 3.12).
		 * Of that, only transitivity is used: making an r-step optional, as
		 * this used to, would need r to be reflexive */
		std::optional<SaturationEvidence> ev;
		if (passes != nullptr)
			ev.emplace();
		saturateTransitive(rhs, *charRE->getLabel().getRelation(), ev ? &*ev : nullptr);
		if (passes != nullptr) {
			passes->push_back({.name = "saturateTransitive",
					   .evidence = std::move(ev),
					   .result = copy(rhs)});
			rhs.resetOrigins();
		}
		return;
	}
	if (const auto *ec = dynamic_cast<const SubsetConstraint *>(cst)) {
		if (!expandSubsetAssumption(rhs, ec, module, passes))
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

	/* The letter inclusions the theory answered yes to so far */
	[[nodiscard]] auto inclusions() const -> std::vector<std::pair<TransLabel, TransLabel>>
	{
		std::vector<std::pair<TransLabel, TransLabel>> result;
		for (const auto &[label, answers] : included)
			for (auto i = 0U; i < answers.size(); i++)
				if (answers[i] != 0)
					result.emplace_back(label, labels[static_cast<int>(i)]);
		return result;
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
		/* Then also with ~p: the two cases cover LABEL */
		auto pneg = Predicate(p).complement();
		if (theory.composes(label, TransLabel(std::nullopt, {pneg}))) {
			auto l = label;
			l.merge(TransLabel(std::nullopt, {pneg}));
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

	[[nodiscard]] auto matrix() const -> const std::vector<uint8_t> & { return similar; }

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

auto Checker::isDFASubLanguageOfNFA(NFA &nfa, const NFA &other, Certificate *cert) const
	-> InclusionResult
{
	KATER_DEBUG(std::cout << "Checking inclusion between automata:" << std::endl;
		    std::cout << nfa << "and " << other << std::endl;);

	if (other.getNumStarting() == 0) {
		Counterexample cex;
		auto empty = nfa.acceptsNoString(cex);
		/* The certificate of an empty language: no reachable state accepts */
		if (empty && cert != nullptr) {
			std::vector<NFA::State *> starts(nfa.start_begin(), nfa.start_end());
			auto reachable = calculateReachableFrom(nfa, starts);
			for (auto id = 0U; id < reachable.size(); id++)
				if (reachable[id])
					cert->pairs.emplace_back(id, VSet<unsigned>{});
			cert->lhs = copy(nfa);
			cert->rhs = copy(other);
			cert->simulation = Simulation(nfa).matrix();
		}
		return {.result = empty, .cex = cex};
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
		if (cert != nullptr)
			cert->pairs.emplace_back(s1->getId(), start);
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
				if (cert != nullptr)
					cert->pairs.emplace_back(next.getLHS()->getId(),
								 next.getRHS());
				workList.emplace_back(std::move(next), nextCex);
			}
		}
	}
	if (cert != nullptr) {
		cert->lhs = copy(nfa);
		cert->rhs = copy(other);
		cert->simulation = sim.matrix();
		cert->inclusions = rhs.inclusions();
	}
	return {.result = true, .cex = {}};
}

auto Checker::decideInclusion(NFA &lhs, const NFA &rhs, const Constraint &cst,
			      std::optional<Chain> chain, Certificate *out) const -> InclusionResult
{
	if (!certificateSink && out == nullptr)
		return isDFASubLanguageOfNFA(lhs, rhs);
	Certificate cert;
	auto result = isDFASubLanguageOfNFA(lhs, rhs, &cert);
	cert.chain = std::move(chain);
	if (result.result && certificateSink)
		certificateSink(cst, cert);
	if (out != nullptr)
		*out = std::move(cert);
	return result;
}

/* Records in CHAIN, if any, that pass NAME, without evidence, left NFA, and
 * makes NFA's states the origins from here on */
static void recordPass(std::optional<Checker::Chain> &chain, const char *name, NFA &nfa)
{
	if (!chain)
		return;
	chain->passes.push_back({.name = name, .evidence = std::nullopt, .result = copy(nfa)});
	nfa.resetOrigins();
}

void Checker::saturateRHS(NFA &rhs, const NFA &lhs, std::optional<Chain> &chain) const
{
	const auto &theory = getTheory();

	for (const auto &assm : getModule().getAssumptions()) {
		expandAssumption(rhs, &*assm, getModule(), chain ? &chain->passes : nullptr);
		normalize(rhs, theory);
		recordPass(chain, "normalize", rhs);
	}
	pruneNFA(rhs, lhs, theory);
	removeDeadStates(rhs);
	normalize(rhs, theory);
	recordPass(chain, "prune", rhs);
}

/* formal: begin checkInclusion, mirrored by formal/KaterCert/Whole.lean */
auto Checker::checkInclusion(SubsetConstraint &subsetC) const -> InclusionResult
{
	auto &module = getModule();
	auto &theory = module.getTheory();

	/* The evidence of every step, if someone wants it */
	std::optional<Evidence> ev;
	if (evidenceSink)
		ev.emplace(Evidence{.lhs = subsetC.getLHS()->clone(),
				    .rhs = subsetC.getRHS()->clone(),
				    .sameEnds = subsetC.sameEnds(),
				    .rotated = subsetC.rotated()});
	/* Records NFA, whose states' origins are of the automaton recorded last,
	 * and makes NFA's states the origins from here on */
	auto record = [&](Evidence::Stage stage, NFA &nfa) {
		if (!ev)
			return;
		ev->steps.push_back({.stage = stage, .nfa = copy(nfa)});
		nfa.resetOrigins();
	};

	expandRfs(subsetC, module);

	auto nfa1 = subsetC.getLHS()->toNFA();
	nfa1.resetOrigins();
	normalize(nfa1, theory);
	removeSimilarTransitions(nfa1);
	if (subsetC.sameEnds()) {
		record(Evidence::Stage::Left, nfa1);
		saturateInitFinalPreds(nfa1, theory);
		record(Evidence::Stage::LeftInitFinal, nfa1);
		saturateLoc(nfa1, theory);
		record(Evidence::Stage::LeftLoc, nfa1);
	}
	removeSimilarTransitions(nfa1);
	auto lhs = nfa1.to_DFA().first;
	record(Evidence::Stage::LeftFinal, lhs);

	auto nfa2 = subsetC.getRHS()->toNFA();
	nfa2.resetOrigins();
	normalize(nfa2, theory);
	/* How the right automaton comes from NFA2, for the certificate and the
	 * evidence */
	std::optional<Chain> chain;
	if (certificateSink || ev) {
		chain.emplace(Chain{.start = copy(nfa2), .passes = {}});
		nfa2.resetOrigins();
	}
	saturateRHS(nfa2, lhs, chain);
	if (subsetC.rotated()) {
		saturateRotate(nfa2, theory);
		normalize(nfa2, theory);
		recordPass(chain, "rotate", nfa2);
	}
	/* doing another similarity pass here would
	 * further minimize the NFA, but minimizing
	 * doesn't seem to help. The remaining time
	 * is determined by the LHS anyway, and these
	 * passes are costly */
	auto result = decideInclusion(lhs, nfa2, subsetC, std::move(chain),
				      ev ? &ev->certificate : nullptr);
	if (ev && result.result)
		evidenceSink(subsetC, *ev);
	return result;
}
/* formal: end checkInclusion */

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
	if (observer)
		observer(cst, result);
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
	getModule().getAssumptions().incorporateInto(getModule().getTheory());

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

/*************************************************************
 *              Extensibility
 ************************************************************/

/*
 * The extensibility check (see Checker.hpp). An event e GenMC may add has
 * nothing after it in pporf; added maximally (a read reading the last write
 * in mo, a write last in mo), it has no eco step out of it either. A cycle
 * through e, in the graph with e, then leaves e by a step that is not eco,
 * and does not begin a pporf path: unless the cycle can do without e (it
 * enters and leaves e within po, which is transitive), it is new, and makes
 * the graph inconsistent. The check finds the visits of e by the cycles of
 * a constraint that leave it so, and decides that each, read from e, is in
 * pporf ; any*: then e would have a pporf successor, and there is no such
 * cycle.
 */

/* Whether the predicates of FIRST and SECOND fit in one PredicateSet */
static auto fitTogether(const PredicateSet &first, const PredicateSet &second) -> bool
{
	auto size = first.size();
	for (const auto &p : second)
		size += first.contains(p) ? 0 : 1;
	return size <= PredicateSet::inlineCapacity;
}

namespace {

/* A step a cycle can leave the event it visits by: what it checks of the
 * event first, the step, and whether the step begins the next word */
struct Exit {
	PredicateSet preds;
	TransLabel label;
	const NFA::State *dest;
	bool wraps;
};

} // namespace

/*
 * Adds to EXITS the first relations of the words read from STATE, after
 * PREDS and what they check on the way, as exits that WRAP or not; returns
 * what the ways from STATE to an accepting state check
 */
static auto exitsFrom(const NFA::State *state, const PredicateSet &preds, bool wrap,
		      const Theory &theory, std::vector<Exit> &exits) -> std::vector<PredicateSet>
{
	std::vector<PredicateSet> ends;
	std::set<std::pair<const NFA::State *, PredicateSet>> seen;
	std::vector<std::pair<const NFA::State *, PredicateSet>> work{{state, preds}};
	while (!work.empty()) {
		auto [at, checked] = work.back();
		work.pop_back();
		if (!seen.emplace(at, checked).second)
			continue;
		if (at->isAccepting())
			ends.push_back(checked);
		for (const auto &t : at->outs()) {
			if (t.label.isRelation()) {
				exits.push_back({.preds = checked,
						 .label = t.label,
						 .dest = t.dest,
						 .wraps = wrap});
				continue;
			}
			if (!theory.composes(checked, t.label.getPreChecks()))
				continue;
			/* Predicates beyond what a label holds only narrow the cycles
			 * down: keep the path without them */
			auto more = checked;
			if (fitTogether(more, t.label.getPreChecks()))
				more.insert(t.label.getPreChecks());
			work.emplace_back(t.dest, more);
		}
	}
	return ends;
}

/* The steps a cycle can leave the event at STATE by: the first relations it
 * can read from there, and, if a word can end there, the first of the next */
static auto exitsOf(const NFA &nfa, const NFA::State *state, const Theory &theory)
	-> std::vector<Exit>
{
	std::vector<Exit> exits;
	for (const auto &end : exitsFrom(state, {}, false, theory, exits))
		for (const auto *start : nfa.starting())
			exitsFrom(start, end, true, theory, exits);
	return exits;
}

/*
 * Whether a cycle that enters an event by ENTRY, from state SRC, and leaves
 * it by EXIT, in the same word, can do without the event: both steps are
 * within po (within po-loc), whose composition then is too, and the
 * automaton reads a step that includes it from SRC to where EXIT leads
 */
static auto canSkip(const NFA::State *src, const TransLabel &entry, const Exit &exit,
		    const Theory &theory) -> bool
{
	using RB = Relation::BuiltinID;
	auto within = [&](const TransLabel &label, RB rel) -> bool {
		return label.isRelation() && !label.hasPreChecks() && !label.hasPostChecks() &&
		       theory.isIncludedIn(*label.getRelation(), Relation::createBuiltin(rel));
	};
	if (exit.wraps || !within(entry, RB::po) || !within(exit.label, RB::po))
		return false;
	auto both = TransLabel(Relation::createBuiltin(
		within(entry, RB::po_loc) && within(exit.label, RB::po_loc) ? RB::po_loc : RB::po));
	return std::ranges::any_of(src->outs(), [&](const auto &t) -> bool {
		return t.dest == exit.dest && theory.isIncludedIn(both, t.label);
	});
}

/*
 * The steps out of an event GenMC may add that a cycle of NFA's words can
 * leave it by and that the check asks about: not eco, which the event added
 * maximally has none of, and not skippable after every step into the event
 */
static auto exitsToCheck(const NFA &nfa, const Theory &theory) -> std::vector<Exit>
{
	using PB = Predicate::BuiltinID;
	/* Not part of an RMW, not a thread start, and not a thread create,
	 * which GenMC adds together with the start of its thread */
	auto addable = PredicateSet{Predicate::createBuiltin(PB::NEXCL),
				    Predicate::createBuiltin(PB::TB).complement(),
				    Predicate::createBuiltin(PB::TC).complement()};

	/* The relation steps into each state, by ID, with the states they come
	 * from */
	std::vector<std::vector<std::pair<const NFA::State *, TransLabel>>> entries(
		nfa.getNumStates());
	for (const auto &s : nfa.states())
		for (const auto &t : s->outs())
			if (t.label.isRelation())
				entries.at(t.dest->getId()).emplace_back(&*s, t.label);

	std::vector<Exit> result;
	for (const auto &s : nfa.states()) {
		const auto &ins = entries.at(s->getId());
		if (ins.empty())
			continue;
		for (auto exit : exitsOf(nfa, &*s, theory)) {
			if (theory.isEco(exit.label) || !theory.composes(exit.preds, addable) ||
			    std::ranges::all_of(ins, [&](const auto &entry) -> bool {
				    return canSkip(entry.first, entry.second, exit, theory);
			    }))
				continue;
			if (fitTogether(exit.preds, addable))
				exit.preds.insert(addable);
			result.push_back(exit);
		}
	}
	return result;
}

/*
 * The words from the event of each of EXITS to the end of the word it leaves
 * the event in: a prefix of the cycle, with its pporf step out of the event,
 * if it has one
 */
static auto toEndOfWord(const NFA &nfa, const std::vector<Exit> &exits) -> NFA
{
	auto rest = copy(nfa);
	std::vector<NFA::State *> copies;
	for (const auto &s : rest.states())
		copies.push_back(&*s);
	rest.clearAllStarting();
	auto *start = rest.createStarting();
	for (const auto &exit : exits) {
		auto *checked =
			rest.addTransitionToFresh(start, TransLabel(std::nullopt, exit.preds));
		NFA::addTransition(checked, {exit.label, copies.at(exit.dest->getId())});
	}
	removeDeadStates(rest);
	return rest;
}

/* Whether NFA accepts a word of predicates alone: its relation relates an
 * event to itself */
static auto acceptsPredicatesOnly(const NFA &nfa) -> bool
{
	std::vector<const NFA::State *> work(nfa.start_begin(), nfa.start_end());
	std::set<const NFA::State *> seen;
	while (!work.empty()) {
		const auto *s = work.back();
		work.pop_back();
		if (s->isAccepting())
			return true;
		if (!seen.insert(s).second)
			continue;
		for (const auto &t : s->outs())
			if (t.label.isPredicate())
				work.push_back(t.dest);
	}
	return false;
}

/* The expression of the builtin relation REL */
static auto letterRE(Relation::BuiltinID rel) -> std::unique_ptr<RegExp>
{
	return CharRE::create(TransLabel(Relation::createBuiltin(rel)));
}

auto Checker::decideExitWords(NFA &words, bool backToEvent, const Constraint &cst) const
	-> InclusionResult
{
	using RB = Relation::BuiltinID;
	const auto &theory = getTheory();

	normalize(words, theory);
	removeSimilarTransitions(words);
	auto lhs = words.to_DFA().first;

	/* The event has a pporf step out of it; or, for a word that ends at the
	 * event again, the cycle is a po path to another event of the event's
	 * location, and eco back to it */
	auto rhsRE =
		SeqRE::createOpt(getModule().createPPORF(), StarRE::createOpt(letterRE(RB::any)));
	if (backToEvent)
		rhsRE = AltRE::createOpt(
			std::move(rhsRE),
			SeqRE::createOpt(PlusRE::createOpt(letterRE(RB::po)),
					 PlusRE::createOpt(AltRE::createOpt(letterRE(RB::rf),
									    letterRE(RB::mo),
									    letterRE(RB::fr)))));
	auto rhs = rhsRE->toNFA();
	normalize(rhs, theory);
	std::optional<Chain> chain;
	if (certificateSink)
		chain.emplace(Chain{.start = copy(rhs), .passes = {}});
	saturateRHS(rhs, lhs, chain);
	return decideInclusion(lhs, rhs, cst, std::move(chain));
}

auto Checker::decideExtensibility(const RegExp &re, bool single, const Constraint &cst) const
	-> InclusionResult
{
	const auto &theory = getTheory();

	/* GenMC adds lin to complete graphs only, for Relinche */
	auto nfa = re.toNFA();
	normalize(nfa, theory);
	for (auto &s : nfa.states())
		nfa.removeTransitionsIf(&*s, [&](const auto &t) -> bool {
			return t.label.isRelation() &&
			       theory.isIncludedIn(
				       *t.label.getRelation(),
				       Relation::createBuiltin(Relation::BuiltinID::lin));
		});
	removeDeadStates(nfa);
	normalize(nfa, theory);
	removeSimilarTransitions(nfa);
	if (acceptsPredicatesOnly(nfa))
		return {.result = false, .cex = {}};

	auto exits = exitsToCheck(nfa, theory);
	if (!single) {
		auto words = toEndOfWord(nfa, exits);
		return decideExitWords(words, false, cst);
	}

	/* A cycle of one word that leaves the event where the word begins goes
	 * back to the event at the end of the word */
	std::vector<Exit> inWord;
	std::vector<Exit> atStart;
	for (const auto &exit : exits)
		(exit.wraps ? atStart : inWord).push_back(exit);
	auto words = toEndOfWord(nfa, inWord);
	auto result = decideExitWords(words, false, cst);
	if (!result.result)
		return result;
	auto cycles = toEndOfWord(nfa, atStart);
	return decideExitWords(cycles, true, cst);
}

auto Checker::isPPOIntersectionInPPO(const AcyclicConstraint *acyc) const -> InclusionResult
{
	return decideExtensibility(*acyc->getRE(), false, *acyc);
}

auto Checker::isCoherenceExtensible(const CoherenceConstraint *coh) const -> InclusionResult
{
	using RB = Relation::BuiltinID;
	auto eco = PlusRE::createOpt(
		AltRE::createOpt(letterRE(RB::rf), letterRE(RB::mo), letterRE(RB::fr)));
	auto re =
		SeqRE::createOpt(getModule().getCOHDeclaration()->getRE()->clone(), std::move(eco));
	return decideExtensibility(*re, true, *coh);
}
