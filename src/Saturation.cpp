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

#include "Saturation.hpp"

#include "NFAUtils.hpp"
#include "Theory.hpp"

#include <algorithm>
#include <map>
#include <ranges>
#include <set>
#include <vector>

namespace RV = std::views;

using Role = SaturationEvidence::Role;

/* Starts EV, if any, for a saturation of NFA under HYPOTHESIS: each state of
 * NFA stands for itself, until the saturation says otherwise */
static void startEvidence(SaturationEvidence *ev, const NFA &nfa,
			  SaturationEvidence::Hypothesis hypothesis)
{
	if (ev == nullptr)
		return;
	*ev = SaturationEvidence{};
	ev->hypothesis = hypothesis;
	for (auto i = 0U; i < nfa.getNumStates(); i++)
		ev->roles.push_back({.kind = Role::Kind::State, .state = i});
}

/* Records in EV, if any, a COPY of the evidence's automaton, whose states the
 * NFA is about to add from OFFSET on */
static void recordCopy(SaturationEvidence *ev, size_t offset, SaturationEvidence::Copy copy)
{
	if (ev == nullptr)
		return;
	VERIFY(ev->roles.size() == offset, "a copy's states follow the states with roles");
	const auto g = static_cast<unsigned>(ev->copies.size());
	for (auto j = 0U; j < ev->automaton.getNumStates(); j++)
		ev->roles.push_back({.kind = Role::Kind::Copy, .state = j, .copy = g});
	ev->copies.push_back(std::move(copy));
}

/* Records in EV, if any, that the theory includes letter A in letter B */
static void recordInclusion(SaturationEvidence *ev, const TransLabel &a, const TransLabel &b)
{
	if (ev != nullptr && a != b)
		ev->inclusions.emplace_back(a, b);
}

static void finishEvidence(SaturationEvidence *ev)
{
	if (ev == nullptr)
		return;
	std::ranges::sort(ev->inclusions);
	ev->inclusions.erase(std::ranges::unique(ev->inclusions).begin(), ev->inclusions.end());
}

/*
 * Duplicate the automaton for each of the initial state(s)' different
 * outgoing predicate transitions. By doing so, we can later restrict
 * incoming transitions to final states.
 */
void duplicateStatesForInitPreds(NFA &nfa)
{
	/* Ensure accepting states have no outgoing transitions */
	nfa.flip();
	for (auto *s : nfa.starting() | RV::filter([](auto *s) { return s->hasIncoming(); })) {
		nfa.splitState(s, [](auto & /*t*/) { return false; });
	}
	nfa.flip();

	/* ... and starting states no incoming ones: the predicates a starting
	 * state is left by are then the first letters of words, not the
	 * letters after a loop back to it */
	for (auto *s : nfa.starting() | RV::filter([](auto *s) { return s->hasIncoming(); })) {
		nfa.splitState(s, [](auto & /*t*/) { return false; });
	}

	std::set<PredicateSet> preds;
	for (auto *s : nfa.starting()) {
		for (auto &t :
		     s->outs() | RV::filter([](auto &t) { return t.label.isPredicate(); })) {
			preds.insert(t.label.getPreChecks());
		}
	}

	if (preds.size() <= 1)
		return;

	NFA result;
	for (const auto &p : preds) {
		auto nfac = copy(nfa);

		for (auto *s : nfa.starting()) {
			nfac.removeTransitionsIf(nfac[s->getId()], [&](auto &t) -> bool {
				return t.label.getPreChecks() != p;
			});
			nfa.removeTransitionsIf(
				s, [&](auto &t) { return t.label.getPreChecks() == p; });
		}
		if (result.getNumStates() == 0) {
			result = std::move(nfac);
		} else {
			result.alt(std::move(nfac));
		}
	}

	nfa.alt(std::move(result));
	removeDeadStates(nfa);
}

void saturateInitFinalPreds(NFA &nfa, const Theory &theory)
{
	duplicateStatesForInitPreds(nfa);

	/* Collect predicates */
	std::vector<NFA::Transition> ipreds;
	std::for_each(nfa.start_begin(), nfa.start_end(), [&](auto *s) {
		std::copy_if(s->out_begin(), s->out_end(), std::back_inserter(ipreds),
			     [&](auto &t) { return t.label.isPredicate(); });
	});

	if (ipreds.empty()) {
		return;
	}

	/* The states on words without an initial predicate: the starting states
	 * (a final predicate leaving one is a word on its own) and the states
	 * after a first relation. A final predicate leaving one of them has to
	 * stay as it is, as there is no initial predicate to merge it with */
	std::vector<NFA::State *> afterRelation;
	for (auto *s : nfa.starting())
		for (auto &t : s->outs() | RV::filter([](auto &t) { return t.label.isRelation(); }))
			afterRelation.push_back(t.dest);
	auto unmerged = calculateReachableFrom(nfa, afterRelation);
	for (auto *s : nfa.starting())
		unmerged[s->getId()] = true;

	std::for_each(nfa.accept_begin(), nfa.accept_end(), [&](auto *s) {
		std::vector<NFA::Transition> toAdd;
		std::vector<NFA::Transition> toRemove;
		for (auto tIt = s->in_begin(), tE = s->in_end(); tIt != tE; ++tIt) {
			if (!tIt->label.isPredicate()) {
				continue;
			}

			if (!unmerged[tIt->dest->getId()])
				toRemove.push_back(*tIt);
			auto reaching = calculateReachingTo(nfa, {tIt->dest});
			std::for_each(ipreds.begin(), ipreds.end(), [&](auto &ip) {
				auto t = *tIt;
				if (reaching[ip.dest->getId()] &&
				    theory.composes(t.label, ip.label)) {
					t.label.merge(ip.label);
					toAdd.push_back(t);
				}
			});
		}
		nfa.removeInvertedTransitions(s, toRemove.begin(), toRemove.end());
		nfa.addInvertedTransitions(s, toAdd.begin(), toAdd.end());
	});
	removeDeadStates(nfa);
}

/* formal: begin saturateLoc, mirrored by formal/KaterCert/Loc.lean */
void saturateLoc(NFA &nfa, const Theory &theory)
{
	std::for_each(nfa.states_begin(), nfa.states_end(), [&](auto &s) {
		std::vector<NFA::Transition> toAdd;
		std::vector<NFA::Transition> toRemove;
		for (auto it = s->out_begin(); it != s->out_end(); ++it) {
			auto &t = *it;
			if (!theory.hasPerLoc(t.label)) {
				continue;
			}

			auto perloc = true;
			nfa.foreachPathReachableFrom(
				{t.dest}, [&](std::pair<NFA::State *, NFA::Transition> p) {
					perloc &= (p.second.label.isPredicate() ||
						   theory.isEco(p.second.label));
				});
			nfa.foreachPathReachingTo({&*s},
						  [&](std::pair<NFA::State *, NFA::Transition> p) {
							  perloc &= (p.second.label.isPredicate() ||
								     theory.isEco(p.second.label));
						  });
			if (!perloc) {
				continue;
			}
			/* The variant goes the way the relation does, with its checks */
			auto rloc = theory.getPerLoc(t.label);
			if (t.label.getRelation()->isInverse())
				rloc.invert();
			toRemove.push_back(t);
			toAdd.push_back(NFA::Transition(
				TransLabel(rloc, t.label.getPreChecks(), t.label.getPostChecks()),
				t.dest));
		}
		nfa.removeTransitions(&*s, toRemove.begin(), toRemove.end());
		nfa.addTransitions(&*s, toAdd.begin(), toAdd.end());
	});
}
/* formal: end saturateLoc */

void saturateID(NFA &nfa, NFA &&id, SaturationEvidence *ev)
{
	startEvidence(ev, nfa, SaturationEvidence::Hypothesis::Within);
	if (ev != nullptr)
		ev->automaton = copy(id);

	std::vector<NFA::State *> inits(id.start_begin(), id.start_end());
	std::vector<NFA::State *> fnals(id.accept_begin(), id.accept_end());

	id.clearAllStarting();
	id.clearAllAccepting();

	std::vector<NFA::State *> states;
	std::for_each(nfa.states_begin(), nfa.states_end(),
		      [&](auto &s) { states.push_back(&*s); });

	std::for_each(states.begin(), states.end(), [&](auto *s) {
		/* alt() appends the copy's states, so state i of ID ends up at OFFSET+i */
		const auto offset = nfa.getNumStates();
		/* A copy from S back to S along no path: the word is empty */
		recordCopy(ev, offset, {.from = s->getId(), .to = s->getId(), .path = {}});
		nfa.alt(copy(id));

		for (auto *init : inits)
			nfa.addEpsilonTransitionSucc(
				s, nfa[static_cast<unsigned>(offset) + init->getId()]);
		for (auto *fnal : fnals)
			nfa.addEpsilonTransitionSucc(
				nfa[static_cast<unsigned>(offset) + fnal->getId()], s);
	});
}

void saturateTransitive(NFA &nfa, const Relation &rel, SaturationEvidence *ev)
{
	TransLabel lab(rel);
	std::vector<NFA::State *> toDuplicate;

	startEvidence(ev, nfa, SaturationEvidence::Hypothesis::Transitive);
	if (ev != nullptr)
		ev->letter = lab;

	lab.flip();
	std::for_each(nfa.states_begin(), nfa.states_end(), [&](auto &s) {
		if (std::any_of(s->in_begin(), s->in_end(),
				[&](auto &t) { return t.label == lab; })) {
			toDuplicate.push_back(&*s);
		}
	});

	std::for_each(toDuplicate.begin(), toDuplicate.end(), [&](auto *s) {
		if (std::any_of(s->in_begin(), s->in_end(),
				[&](auto &t) { return t.label != lab; })) {
			auto *d = nfa.splitState(s, [&](auto &t) { return t.label == lab; });
			/* The state split off takes the other steps into S */
			if (ev != nullptr) {
				VERIFY(ev->roles.size() == d->getId(), "a split state comes last");
				ev->roles.push_back(
					{.kind = Role::Kind::State, .state = s->getId()});
			}
		}
		NFA::addSelfTransition(s, TransLabel(rel));
		/* S is entered by REL alone, which may repeat there */
		if (ev != nullptr)
			ev->roles[s->getId()] = {.kind = Role::Kind::After, .state = s->getId()};
	});
}

/*
 * Adds a path corresponding to PATH from SRC to DST in NFA,
 * by copying the PATH nfa.  Initial/final states in the copy
 * are discarded.
 */
void addNFAPath(NFA &nfa, const NFA &path, NFA::State *src, NFA::State *dst)
{
	VSet<NFA::State *> inits(path.start_begin(), path.start_end());
	VSet<NFA::State *> finals(path.accept_begin(), path.accept_end());

	auto lcopy = copy(path);
	lcopy.clearAllAccepting();
	lcopy.clearAllStarting();

	/* alt() appends the copy's states, so state i of PATH ends up at OFFSET+i */
	const auto offset = nfa.getNumStates();
	nfa.alt(std::move(lcopy));

	for (auto *init : inits)
		nfa.addEpsilonTransition(src, nfa[static_cast<unsigned>(offset) + init->getId()]);
	for (auto *fnal : finals)
		nfa.addEpsilonTransition(nfa[static_cast<unsigned>(offset) + fnal->getId()], dst);
}

void saturateBuiltin(NFA &nfa, const Relation &rel, NFA sat, const Theory &theory,
		     SaturationEvidence *ev)
{
	TransLabel lab(rel);

	startEvidence(ev, nfa, SaturationEvidence::Hypothesis::Within);
	if (ev != nullptr) {
		ev->automaton = copy(sat);
		ev->word = {lab};
	}

	/* Collect all paths but don't modify in place */
	std::vector<std::pair<NFA::State *, NFA::Transition>> paths;
	auto relInTrans = [&](auto &t) { return theory.isIncludedIn(lab, t.label); };
	for (auto &s : nfa.states()) {
		for (auto &t : s->outs() | RV::filter(relInTrans))
			paths.emplace_back(&*s, t);
	}

	for (auto &[s, t] : paths) {
		/* The copy's path is the step it may stand for, which reads REL */
		recordCopy(ev, nfa.getNumStates(),
			   {.from = s->getId(),
			    .to = t.dest->getId(),
			    .path = {{.letter = t.label, .dest = t.dest->getId(), .known = {}}}});
		recordInclusion(ev, lab, t.label);
		addNFAPath(nfa, sat, s, t.dest);
	}
	finishEvidence(ev);
}

auto collectLabels(const NFA &nfa) -> std::vector<TransLabel>
{
	std::vector<TransLabel> labels;
	std::for_each(nfa.states_begin(), nfa.states_end(), [&](auto &s) {
		std::for_each(s->out_begin(), s->out_end(),
			      [&](auto &t) { labels.push_back(t.label); });
	});
	return labels;
}

void saturateEmpty(NFA &start, NFA &&empty, SaturationEvidence *ev)
{
	startEvidence(ev, start, SaturationEvidence::Hypothesis::Empty);
	if (ev != nullptr) {
		ev->automaton = copy(empty);
		/* EMPTY's states follow START's, in a copy anchored nowhere */
		for (auto j = 0U; j < empty.getNumStates(); j++)
			ev->roles.push_back({.kind = Role::Kind::Copy, .state = j});
	}

	std::for_each(empty.start_begin(), empty.start_end(), [&](auto &s) {
		NFA::addSelfTransition(
			s, TransLabel(Relation::createBuiltin(Relation::BuiltinID::any)));
	});
	std::for_each(empty.accept_begin(), empty.accept_end(), [&](auto &a) {
		NFA::addSelfTransition(
			a, TransLabel(Relation::createBuiltin(Relation::BuiltinID::any)));
	});

	start.alt(std::move(empty));
}

void saturateDomains(NFA &nfa, const Theory &theory)
{
	std::for_each(nfa.states_begin(), nfa.states_end(), [&](auto &s) {
		/* toAdd: temp workaround due to std::set exposing const_iters only */
		std::vector<NFA::Transition> toAdd;
		std::vector<NFA::Transition> toRemove;
		for (auto it = s->out_begin(), ie = s->out_end(); it != ie; ++it) {
			auto lab = it->label;
			if (lab.isPredicate())
				continue;

			if (theory.composes(lab.getPreChecks(),
					    {theory.getDomain(*lab.getRelation())}) &&
			    theory.composes(lab.getPostChecks(),
					    {theory.getCodomain(*lab.getRelation())})) {
				lab.getPreChecks().insert(theory.getDomain(*lab.getRelation()));
				lab.getPostChecks().insert(theory.getCodomain(*lab.getRelation()));
				toAdd.push_back(NFA::Transition(lab, it->dest));
			}
			toRemove.push_back(*it);
		}
		nfa.removeTransitions(&*s, toRemove.begin(), toRemove.end());
		nfa.addTransitions(&*s, toAdd.begin(), toAdd.end());
	});
}

void saturateSubword(NFA &nfa, const NFA &e, const std::vector<TransLabel> &word,
		     const Theory &theory, SaturationEvidence *ev)
{
	/* Where the search is: the NFA's state, how much of WORD it has read, and
	 * what WORD's predicates say about the current event */
	struct Position {
		NFA::State *state;
		size_t read;
		PredicateSet known;

		auto operator<=>(const Position &) const = default;
	};
	/* With evidence, how the search reached a position: from where, and by
	 * which step of the NFA (none when WORD checked a predicate) */
	struct Parent {
		Position from;
		const NFA::Transition *step;
	};

	startEvidence(ev, nfa, SaturationEvidence::Hypothesis::Within);
	if (ev != nullptr) {
		ev->automaton = copy(e);
		ev->word = word;
	}

	using Path = std::vector<SaturationEvidence::Step>;
	using Inclusions = std::vector<std::pair<TransLabel, TransLabel>>;
	std::vector<std::pair<NFA::State *, NFA::State *>> shortcuts;
	std::map<std::pair<NFA::State *, NFA::State *>, std::pair<Path, Inclusions>> paths;
	for (auto &startUP : nfa.states()) {
		std::set<Position> visited;
		std::map<Position, Parent> parents;
		std::vector<Position> work;
		auto visit = [&](Position pos, const Position &from, const NFA::Transition *step) {
			if (!visited.insert(pos).second)
				return;
			if (ev != nullptr)
				parents.emplace(pos, Parent{.from = from, .step = step});
			work.push_back(std::move(pos));
		};
		/* The path to POS, each step with what WORD's predicates said of the
		 * event it leaves, and the inclusions the theory granted it */
		auto pathTo = [&](Position pos) {
			Path path;
			Inclusions inclusions;
			for (auto it = parents.find(pos); it != parents.end();
			     it = parents.find(pos)) {
				const auto &[from, step] = it->second;
				if (step != nullptr) {
					path.push_back({.letter = step->label,
							.dest = step->dest->getId(),
							.known = from.known});
					auto read =
						step->label.isPredicate()
							? TransLabel(std::nullopt, from.known)
							: TransLabel(word[from.read].getRelation(),
								     from.known);
					inclusions.emplace_back(read, step->label);
				}
				pos = from;
			}
			std::ranges::reverse(path);
			return std::pair(path, inclusions);
		};

		const Position start{&*startUP, 0, {}};
		visited.insert(start);
		work.push_back(start);
		while (!work.empty()) {
			auto pos = work.back();
			work.pop_back();

			if (pos.read == word.size()) {
				shortcuts.emplace_back(&*startUP, pos.state);
				if (ev != nullptr && !paths.contains({&*startUP, pos.state}))
					paths.emplace(std::pair(&*startUP, pos.state), pathTo(pos));
			}

			/* WORD checks a predicate: it knows more about the event */
			if (pos.read < word.size() && word[pos.read].isPredicate()) {
				const auto &checks = word[pos.read].getPreChecks();
				if (pos.known.size() + checks.size() <=
				    PredicateSet::inlineCapacity) {
					auto known = pos.known;
					known.insert(checks);
					visit({pos.state, pos.read + 1, known}, pos, nullptr);
				}
				continue;
			}

			for (const auto &t : pos.state->outs()) {
				/* The NFA checks a predicate WORD implies */
				if (t.label.isPredicate()) {
					if (theory.isIncludedIn(pos.known, t.label.getPreChecks()))
						visit({t.dest, pos.read, pos.known}, pos, &t);
					continue;
				}
				/* Both read a relation, WORD's in the NFA's */
				if (pos.read < word.size() &&
				    theory.isIncludedIn(
					    TransLabel(word[pos.read].getRelation(), pos.known),
					    t.label))
					visit({t.dest, pos.read + 1, {}}, pos, &t);
			}
		}
	}

	std::ranges::sort(shortcuts);
	shortcuts.erase(std::ranges::unique(shortcuts).begin(), shortcuts.end());
	for (auto [p, q] : shortcuts) {
		if (ev != nullptr) {
			auto &[path, inclusions] = paths.at({p, q});
			for (const auto &[a, b] : inclusions)
				recordInclusion(ev, a, b);
			recordCopy(ev, nfa.getNumStates(),
				   {.from = p->getId(), .to = q->getId(), .path = path});
		}
		addNFAPath(nfa, e, p, q);
	}
	finishEvidence(ev);
}

/*
 * Makes the origins of the states of ROT, a copy of an automaton of N states
 * that the rotations through its state of origins AT begin (OFFSET 0) or end
 * (OFFSET N) in, those of the states of the automaton of rotations formal/
 * builds (KaterCert/Rotate.lean), where those through state s begin at
 * N + 2 * N * s: hints for its check
 */
static void rotationOrigins(NFA &rot, const std::vector<unsigned> &at, unsigned n, unsigned offset)
{
	for (auto &st : rot.states()) {
		std::vector<unsigned> origins;
		for (auto s : at)
			for (auto q : st->getOrigins())
				origins.push_back(n + (2 * n * s) + offset + q);
		NFA::setOrigins(&*st, std::move(origins));
	}
}

void saturateRotate(NFA &nfa, const Theory &theory)
{
	void simplify(NFA & nfa, const Theory &theory);
	NFA result;

	auto n = static_cast<unsigned>(nfa.getNumStates());
	simplify(nfa, theory);
	auto isNonStarting = [](auto &s) { return !s->isStarting(); };
	for (auto &s : nfa.states() | std::views::filter(isNonStarting)) {

		auto rot1 = copy(nfa);
		auto rot2 = copy(nfa);
		rotationOrigins(rot1, s->getOrigins(), n, 0);
		rotationOrigins(rot2, s->getOrigins(), n, n);

		rot1.clearAllStarting();
		rot1.makeStarting(rot1[s->getId()]);

		rot2.clearAllAccepting();
		rot2.makeAccepting(rot2[s->getId()]);

		rot1.seq(std::move(rot2));
		result.alt(std::move(rot1));
	}
	nfa.alt(std::move(result));
	removeDeadStates(nfa);
}
