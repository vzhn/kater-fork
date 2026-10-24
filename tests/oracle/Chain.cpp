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

#include "Chain.hpp"

#include "NFAUtils.hpp"
#include "Theory.hpp"
#include "Utils.hpp"

#include <algorithm>
#include <format>
#include <functional>
#include <memory>
#include <ranges>
#include <set>

namespace oracle {

using Hypothesis = SaturationEvidence::Hypothesis;
using Role = SaturationEvidence::Role;
using RoleKind = SaturationEvidence::Role::Kind;

/* formal: begin checkSaturation, mirrored by formal/KaterCert/Saturation.lean */
namespace {

auto hasStep(const NFA &nfa, unsigned q, const TransLabel &a, unsigned q2) -> bool
{
	return q < nfa.getNumStates() &&
	       std::ranges::any_of(
		       nfa[q]->outs(),
		       [&](auto &t) { return t.label == a && t.dest->getId() == q2; });
}

auto isStarting(const NFA &nfa, unsigned q) -> bool
{
	return q < nfa.getNumStates() && nfa[q]->isStarting();
}

auto isAccepting(const NFA &nfa, unsigned q) -> bool
{
	return q < nfa.getNumStates() && nfa[q]->isAccepting();
}

auto sameRole(const Role &r, const Role &s) -> bool
{
	return r.kind == s.kind && r.state == s.state &&
	       (r.kind != RoleKind::Copy || r.copy == s.copy);
}

/*
 * Whether PATH reads WORD: walking both, a predicate of WORD adds its checks
 * to what is known of the current event, a predicate [Q] of PATH needs
 * [K] <= [Q] for the subset K of what is known its step records, and a
 * relation b of PATH needs the next letter of WORD to be a bare relation r
 * with [K];r <= b, after which nothing is known
 */
auto readsWord(const std::vector<TransLabel> &word,
	       const std::vector<SaturationEvidence::Step> &path,
	       const std::function<bool(const TransLabel &, const TransLabel &)> &includes) -> bool
{
	std::vector<Predicate> known;
	auto knows = [&](const PredicateSet &ps) {
		return std::ranges::all_of(
			ps, [&](auto &p) { return std::ranges::find(known, p) != known.end(); });
	};
	auto w = word.begin();
	auto p = path.begin();
	while (true) {
		if (w != word.end() && w->isPredicate()) {
			known.insert(known.end(), w->getPreChecks().begin(),
				     w->getPreChecks().end());
			++w;
		} else if (p != path.end() && p->letter.isPredicate()) {
			if (!knows(p->known) ||
			    !includes(TransLabel(std::nullopt, p->known), p->letter))
				return false;
			++p;
		} else if (w != word.end() && p != path.end()) {
			if (w->hasPreChecks() || w->hasPostChecks() || !knows(p->known) ||
			    !includes(TransLabel(w->getRelation(), p->known), p->letter))
				return false;
			known.clear();
			++w;
			++p;
		} else {
			return w == word.end() && p == path.end();
		}
	}
}

} // namespace

auto checkSaturation(const NFA &before, const NFA &after, const SaturationEvidence &ev)
	-> std::optional<std::string>
{
	const auto &a = ev.automaton;
	const auto transitive = ev.hypothesis == Hypothesis::Transitive;
	const auto within = ev.hypothesis == Hypothesis::Within;
	const auto empty = ev.hypothesis == Hypothesis::Empty;

	if (ev.roles.size() != after.getNumStates())
		return "the roles are not over the saturated automaton's states";
	for (auto g = 0U; g < ev.copies.size(); g++)
		if (ev.copies[g].from >= before.getNumStates() ||
		    ev.copies[g].to >= before.getNumStates())
			return "copy " + std::to_string(g) + " is anchored outside the automaton";
	for (auto m = 0U; m < ev.roles.size(); m++) {
		const auto &r = ev.roles[m];
		auto inRange = r.kind == RoleKind::Copy
				       ? (within || empty) && r.state < a.getNumStates() &&
						 (empty || r.copy < ev.copies.size())
				       : (r.kind == RoleKind::State || transitive) &&
						 r.state < before.getNumStates();
		if (!inRange)
			return "the role of state " + std::to_string(m) + " names nothing";
	}

	std::set<std::pair<TransLabel, TransLabel>> included(ev.inclusions.begin(),
							     ev.inclusions.end());
	auto includes = [&](const TransLabel &x, const TransLabel &y) {
		return x == y || included.contains({x, y});
	};
	/* Whether copy G can be left: its path is one of BEFORE, from its start
	 * to its end, that reads the word */
	auto exits = [&](unsigned g) {
		const auto &c = ev.copies[g];
		auto q = c.from;
		for (const auto &s : c.path) {
			if (!hasStep(before, q, s.letter, s.dest))
				return false;
			q = s.dest;
		}
		return q == c.to && readsWord(ev.word, c.path, includes);
	};

	/* The roles R lifts to: itself, and those whose bound includes its
	 * bound, as doc/verification.md lists them */
	std::function<std::vector<Role>(const Role &)> lifts = [&](const Role &r) {
		std::vector<Role> result{r};
		auto addState = [&](unsigned n) {
			auto more = lifts({.kind = RoleKind::State, .state = n});
			result.insert(result.end(), more.begin(), more.end());
		};
		switch (r.kind) {
		case RoleKind::State:
			if (within)
				for (auto g = 0U; g < ev.copies.size(); g++)
					if (ev.copies[g].from == r.state)
						for (const auto *i : a.starting())
							result.push_back({.kind = RoleKind::Copy,
									  .state = i->getId(),
									  .copy = g});
			break;
		case RoleKind::After:
			addState(r.state);
			break;
		case RoleKind::Copy:
			if (within && isAccepting(a, r.state) && exits(r.copy))
				addState(ev.copies[r.copy].to);
			break;
		}
		return result;
	};
	/* Whether role S steps by letter L to role T */
	auto steps = [&](const Role &s, const TransLabel &l, const Role &t) {
		if (l.isPredicate() && sameRole(s, t))
			return true;
		switch (s.kind) {
		case RoleKind::State:
			if (t.kind == RoleKind::State)
				return hasStep(before, s.state, l, t.state);
			return t.kind == RoleKind::After && transitive && l == ev.letter &&
			       hasStep(before, s.state, l, t.state);
		case RoleKind::After:
			return t.kind == RoleKind::After && t.state == s.state && transitive &&
			       l == ev.letter;
		case RoleKind::Copy:
			if (empty && isAccepting(a, s.state))
				return true;
			if (t.kind != RoleKind::Copy)
				return false;
			if (empty && isStarting(a, s.state) && isStarting(a, t.state))
				return true;
			return (empty || s.copy == t.copy) && hasStep(a, s.state, l, t.state);
		}
		return false;
	};
	/* The states of BEFORE the identity reaches: the starting ones and, if
	 * the automaton reads the empty word, the ends of the copies from them
	 * that can be left, and so on */
	std::vector<uint8_t> byIdentity(before.getNumStates());
	for (const auto *q : before.starting())
		byIdentity[q->getId()] = 1;
	auto readsEmpty =
		std::ranges::any_of(a.starting(), [](auto *i) { return i->isAccepting(); });
	for (auto changed = within && readsEmpty; changed;) {
		changed = false;
		for (auto g = 0U; g < ev.copies.size(); g++) {
			const auto &c = ev.copies[g];
			if (byIdentity[c.from] != 0 && byIdentity[c.to] == 0 && exits(g)) {
				byIdentity[c.to] = 1;
				changed = true;
			}
		}
	}
	auto startable = [&](const Role &r) {
		switch (r.kind) {
		case RoleKind::State:
			return byIdentity[r.state] != 0;
		case RoleKind::After:
			return false;
		case RoleKind::Copy:
			return isStarting(a, r.state) &&
			       (empty || byIdentity[ev.copies[r.copy].from] != 0);
		}
		return false;
	};
	auto acceptable = [&](const Role &r) {
		return std::ranges::any_of(lifts(r), [&](const Role &s) {
			return (s.kind == RoleKind::State && isAccepting(before, s.state)) ||
			       (s.kind == RoleKind::Copy && empty && isAccepting(a, s.state));
		});
	};

	for (const auto *m : after.starting())
		if (!startable(ev.roles[m->getId()]))
			return "starting state " + std::to_string(m->getId()) + " is not justified";
	for (const auto &m : after.states()) {
		const auto &r = ev.roles[m->getId()];
		if (m->isAccepting() && !acceptable(r))
			return "accepting state " + std::to_string(m->getId()) +
			       " is not justified";
		auto ups = lifts(r);
		for (const auto &t : m->outs()) {
			const auto &r2 = ev.roles[t.dest->getId()];
			if (std::ranges::none_of(ups,
						 [&](auto &s) { return steps(s, t.label, r2); }))
				return "the step " + std::to_string(m->getId()) + " --> " +
				       std::to_string(t.dest->getId()) + " is not justified";
		}
	}
	return std::nullopt;
}
/* formal: end checkSaturation */

/* formal: begin checkChain, mirrored by formal/KaterCert/Chain.lean */
auto sameNFA(const NFA &a, const NFA &b) -> bool
{
	if (a.getNumStates() != b.getNumStates() ||
	    !std::ranges::equal(a.starting(), b.starting(),
				[](auto *p, auto *q) { return p->getId() == q->getId(); }))
		return false;
	for (auto q = 0U; q < a.getNumStates(); q++)
		if (a[q]->isAccepting() != b[q]->isAccepting() ||
		    !std::ranges::equal(a[q]->outs(), b[q]->outs(), [](auto &t, auto &u) {
			    return t.label == u.label && t.dest->getId() == u.dest->getId();
		    }))
			return false;
	return true;
}

auto checkChain(const Checker::Certificate &cert) -> std::optional<std::string>
{
	if (!cert.chain)
		return std::nullopt;
	/* The passes trusted to meet their contracts */
	static const std::set<std::string> trusted = {"normalize", "prune", "rotate"};
	const auto *last = &cert.chain->start;
	for (auto i = 0U; i < cert.chain->passes.size(); i++) {
		const auto &pass = cert.chain->passes[i];
		auto which = "pass " + std::to_string(i) + " (" + pass.name + ")";
		if (pass.evidence) {
			if (auto why = checkSaturation(*last, pass.result, *pass.evidence))
				return which + ": " + *why;
		} else if (!trusted.contains(pass.name)) {
			return which + " has no evidence";
		}
		last = &pass.result;
	}
	if (!sameNFA(*last, cert.rhs))
		return "the chain does not end at the right automaton";
	return std::nullopt;
}
/* formal: end checkChain */

auto largestAutomaton(const Checker::Chain &chain) -> size_t
{
	auto n = chain.start.getNumStates();
	for (const auto &p : chain.passes)
		n = std::max(n, p.result.getNumStates());
	return n;
}

auto clone(const SaturationEvidence &ev) -> SaturationEvidence
{
	return {.hypothesis = ev.hypothesis,
		.letter = ev.letter,
		.automaton = copy(ev.automaton),
		.word = ev.word,
		.roles = ev.roles,
		.copies = ev.copies,
		.inclusions = ev.inclusions};
}

auto clone(const Checker::Chain &chain) -> Checker::Chain
{
	Checker::Chain result{.start = copy(chain.start), .passes = {}};
	for (const auto &p : chain.passes)
		result.passes.push_back(
			{.name = p.name,
			 .evidence = p.evidence ? std::optional(clone(*p.evidence)) : std::nullopt,
			 .result = copy(p.result)});
	return result;
}

auto chainMutants(const Checker::Certificate &cert)
	-> std::vector<std::pair<std::string, Checker::Certificate>>
{
	std::vector<std::pair<std::string, Checker::Certificate>> result;
	if (!cert.chain)
		return result;
	const auto &passes = cert.chain->passes;
	/* A copy of CERT with the chain's pass I mutated */
	auto add = [&](const std::string &name, size_t i,
		       const std::function<void(Checker::Pass &)> &mutate) {
		Checker::Certificate m{.lhs = copy(cert.lhs),
				       .rhs = copy(cert.rhs),
				       .simulation = cert.simulation,
				       .pairs = cert.pairs,
				       .inclusions = cert.inclusions,
				       .chain = clone(*cert.chain)};
		mutate(m.chain->passes.at(i));
		result.emplace_back(name, std::move(m));
	};
	/* The first pass with evidence that PRED holds of */
	auto first = [&](const std::function<bool(const Checker::Pass &)> &pred)
		-> std::optional<size_t> {
		for (auto i = 0U; i < passes.size(); i++)
			if (passes[i].evidence && pred(passes[i]))
				return i;
		return std::nullopt;
	};
	auto of = [](Hypothesis h) {
		return [h](const Checker::Pass &p) { return p.evidence->hypothesis == h; };
	};

	/* Only the subword saturations of the compilation schemes take
	 * inclusions from the theory, in chains of thousands of states */
	if (auto i = first([](auto &p) { return !p.evidence->inclusions.empty(); }))
		add("chain-drop-inclusion", *i, [](auto &p) { p.evidence->inclusions.pop_back(); });
	/* Each copy is the whole chain: those of the other large chains would
	 * take up hundreds of megabytes and test nothing the small ones do not */
	if (largestAutomaton(*cert.chain) > 250)
		return result;

	if (auto i = first([](auto &p) { return !p.evidence->roles.empty(); })) {
		add("chain-drop-role", *i, [](auto &p) { p.evidence->roles.pop_back(); });
		add("chain-no-evidence", *i, [](auto &p) { p.evidence.reset(); });
		/* A step nothing justifies: a relation that loops at state 0 */
		add("chain-extra-step", *i, [](auto &p) {
			auto *q = p.result[0];
			NFA::addTransition(q, NFA::Transition(TransLabel(Relation::createBuiltin(
								      Relation::BuiltinID::rf)),
							      q));
		});
	}
	/* A loop of the transitive letter where the identity has to be bound */
	auto after = [](const Checker::Pass &p) {
		return std::ranges::any_of(p.evidence->roles,
					   [](auto &r) { return r.kind == RoleKind::After; });
	};
	if (auto i = first([&](auto &p) { return of(Hypothesis::Transitive)(p) && after(p); })) {
		add("chain-after-starts", *i, [](auto &p) {
			auto it = std::ranges::find_if(p.evidence->roles, [](auto &r) {
				return r.kind == RoleKind::After;
			});
			p.result.makeStarting(p.result[it - p.evidence->roles.begin()]);
		});
		add("chain-other-letter", *i, [](auto &p) { p.evidence->letter.flip(); });
	}
	auto withCopies = [&](const Checker::Pass &p) {
		return of(Hypothesis::Within)(p) && !p.evidence->copies.empty();
	};
	if (auto i = first(withCopies)) {
		/* The first copy, ending elsewhere */
		add("chain-copy-moved", *i, [](auto &p) {
			auto &c = p.evidence->copies.front();
			c.to = c.to == c.from ? c.from + 1 : c.from;
		});
		add("chain-hypothesis-start-dropped", *i,
		    [](auto &p) { p.evidence->automaton.clearAllStarting(); });
	}
	if (!passes.empty())
		add("chain-last-differs", passes.size() - 1,
		    [](auto &p) { p.result.createState(); });
	return result;
}

/* An automaton as text: its starting and accepting states, and its steps */
static auto describe(const NFA &nfa, const Theory &theory) -> std::string
{
	std::string s = "{start";
	for (const auto *q : nfa.starting())
		s += " " + std::to_string(q->getId());
	s += "; accept";
	for (const auto *q : nfa.accepting())
		s += " " + std::to_string(q->getId());
	for (const auto &q : nfa.states())
		for (const auto &t : q->outs())
			s += "; " + std::to_string(q->getId()) + " -" + toString(t.label, theory) +
			     "-> " + std::to_string(t.dest->getId());
	return s + "}";
}

/* The hypothesis of EV */
static auto hypothesisClaim(const SaturationEvidence &ev, const Theory &theory) -> ChainClaim
{
	auto shared = std::make_shared<SaturationEvidence>(clone(ev));
	switch (ev.hypothesis) {
	case Hypothesis::Transitive: {
		auto t = toString(ev.letter, theory);
		return {.text = t + ";" + t + " <= " + t,
			.violation = [shared](Graph & /*g*/, Semantics &sem) {
				auto r = sem.eval(shared->letter);
				return !r.compose(r).includedIn(r);
			}};
	}
	case Hypothesis::Within: {
		std::string word;
		for (const auto &l : ev.word)
			word += (word.empty() ? "" : ";") + toString(l, theory);
		return {.text = describe(ev.automaton, theory) +
				" <= " + (word.empty() ? "id" : word),
			.violation = [shared](Graph &g, Semantics &sem) {
				auto w = Matrix::identity(g.ctx(), g.size());
				for (const auto &l : shared->word)
					w = w.compose(sem.eval(l));
				return !sem.eval(shared->automaton).includedIn(w);
			}};
	}
	case Hypothesis::Empty:
		return {.text = describe(ev.automaton, theory) + " = 0",
			.violation = [shared](Graph & /*g*/, Semantics &sem) {
				return !sem.eval(shared->automaton).isEmpty();
			}};
	}
	return {};
}

/* The contract of pass NAME, without evidence, from BEFORE to AFTER */
static auto passClaim(const std::string &name, const NFA &before, const NFA &after) -> Query
{
	auto b = std::make_shared<NFA>(copy(before));
	auto a = std::make_shared<NFA>(copy(after));
	if (name == "rotate")
		return [a, b](Graph & /*g*/, Semantics &sem) {
			return sem.eval(*a).anyReflexive() && !sem.eval(*b).anyReflexive();
		};
	return [a, b](Graph & /*g*/, Semantics &sem) {
		return !sem.eval(*a).includedIn(sem.eval(*b));
	};
}

auto chainClaims(const Checker::Chain &chain, const std::string &of, unsigned events,
		 const Theory &theory) -> ChainClaims
{
	ChainClaims result;
	const auto *last = &chain.start;
	for (auto i = 0U; i < chain.passes.size(); i++) {
		const auto &p = chain.passes[i];
		if (p.evidence)
			result.hypotheses.push_back(hypothesisClaim(*p.evidence, theory));
		else if (std::max(last->getNumStates(), p.result.getNumStates()) * events >
			 maxPassClaimRounds)
			result.largePasses++;
		else
			result.passes.push_back(
				{.text = std::format("pass {} ({}) of {}", i, p.name, of),
				 .violation = passClaim(p.name, *last, p.result)});
		last = &p.result;
	}
	return result;
}

} // namespace oracle
