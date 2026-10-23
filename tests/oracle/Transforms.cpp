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

#include "Transforms.hpp"

#include "NFAUtils.hpp"
#include "ParsingDriver.hpp"
#include "Saturation.hpp"
#include "Theory.hpp"
#include "Utils.hpp"

#include <functional>
#include <iostream>
#include <map>
#include <random>
#include <sstream>
#include <vector>

/* Passes of the decision procedure with external linkage in Checker.cpp */
void removeConsecutivePredicates(NFA &nfa, const Theory &theory);
void normalize(NFA &nfa, const Theory &theory);

namespace oracle {

namespace {

using RB = Relation::BuiltinID;
using PB = Predicate::BuiltinID;

/* Random expressions over the builtin relations and predicates */
class RandomRE {

public:
	RandomRE(unsigned seed) : rng_(seed) {}

	auto expr(unsigned depth) -> std::unique_ptr<RegExp>
	{
		if (depth == 0 || chance(25))
			return CharRE::create(label());
		/* x = A | x;B, through the NFA construction of recursive definitions */
		if (chance(8)) {
			auto x = Relation::createUser();
			std::vector<std::unique_ptr<RegExp>> defs;
			defs.push_back(AltRE::createOpt(
				expr(depth - 1),
				SeqRE::createOpt(CharRE::create(TransLabel(x)), expr(depth - 1))));
			return MutRecRE::create(x, std::vector<Relation>{x}, std::move(defs));
		}
		auto op = pick(100);
		if (op < 40)
			return SeqRE::createOpt(expr(depth - 1), expr(depth - 1));
		if (op < 60)
			return AltRE::createOpt(expr(depth - 1), expr(depth - 1));
		if (op < 72)
			return PlusRE::createOpt(expr(depth - 1));
		if (op < 84)
			return StarRE::createOpt(expr(depth - 1));
		return QMarkRE::createOpt(expr(depth - 1));
	}

	/* A builtin relation, possibly inverted */
	auto relation() -> Relation
	{
		static const std::vector<RB> pool = {
			RB::po,	 RB::po_loc, RB::rf,  RB::rfe, RB::rfi, RB::mo,	   RB::moe,
			RB::moi, RB::fr,     RB::fre, RB::fri, RB::rmw, RB::detour};
		auto r = Relation::createBuiltin(pool[pick(pool.size())]);
		if (chance(10))
			r.invert();
		return r;
	}

	/* A word of alternating predicate checks and bare relations */
	auto word() -> std::vector<TransLabel>
	{
		std::vector<TransLabel> w;
		w.emplace_back(std::nullopt, predicates());
		for (auto k = 1 + pick(2); k > 0; k--) {
			w.emplace_back(relation());
			w.emplace_back(std::nullopt, predicates());
		}
		return w;
	}

private:
	auto pick(unsigned n) -> unsigned
	{
		return std::uniform_int_distribution<unsigned>(0, n - 1)(rng_);
	}
	auto chance(unsigned percent) -> bool { return pick(100) < percent; }

	auto predicates() -> PredicateSet
	{
		static const std::vector<PB> pool = {PB::R,    PB::W,	 PB::F,	    PB::ACQ,
						     PB::REL,  PB::SC,	 PB::NA,    PB::RLX,
						     PB::ATOM, PB::EXCL, PB::NEXCL, PB::DEP};
		PredicateSet ps;
		for (auto k = pick(3); k > 0; k--) {
			auto p = Predicate::createBuiltin(pool[pick(pool.size())]);
			if (chance(15))
				p.complement();
			ps.insert(p);
		}
		return ps;
	}

	auto label() -> TransLabel
	{
		static const std::vector<RB> pool = {
			RB::po,	 RB::po_loc, RB::rf,  RB::rfe, RB::rfi, RB::mo,	   RB::moe,
			RB::moi, RB::fr,     RB::fre, RB::fri, RB::rmw, RB::detour};
		if (chance(30)) {
			auto ps = predicates();
			return {std::nullopt, ps};
		}
		auto r = Relation::createBuiltin(pool[pick(pool.size())]);
		if (chance(10))
			r.invert();
		auto pre = chance(25) ? predicates() : PredicateSet{};
		auto post = chance(25) ? predicates() : PredicateSet{};
		return {r, pre, post};
	}

	std::mt19937 rng_;
};

/* What a transformation from automaton A to automaton B promises */
enum class Contract {
	Equivalent,   /* [[B]] = [[A]] */
	KeepsCycles,  /* [[B]] & id >= [[A]] & id */
	AddsNoCycles, /* B has a cycle only if A has one */
	Weaker,	      /* [[B]] <= [[A]], under the transformation's hypothesis */
};

/* What a saturation of a right-hand side is given: a hypothesis about an
 * expression, a relation, or a word */
struct Given {
	std::unique_ptr<RegExp> expr;
	Relation rel;
	std::vector<TransLabel> word;
};

/* A hypothesis about GIVEN, as a formula */
using GivenQuery = std::function<Term(Graph &, Semantics &, const Given &)>;

/* Splits each state reached by both predicates and relations in two, as
 * removeConsecutivePredicates does */
void splitMixedIncoming(NFA &nfa)
{
	std::vector<NFA::State *> mixed;
	for (auto &s : nfa.states()) {
		auto preds = std::ranges::any_of(s->ins(),
						 [](auto &t) { return t.label.isPredicate(); });
		auto rels = std::ranges::any_of(s->ins(),
						[](auto &t) { return !t.label.isPredicate(); });
		if (preds && rels)
			mixed.push_back(&*s);
	}
	for (auto *s : mixed)
		nfa.splitState(s, [](auto &t) { return t.label.isPredicate(); });
}

struct Transform {
	std::string name;
	bool normalizeFirst; /* the pass assumes a normalized automaton */
	Contract contract;
	std::function<void(NFA &, const Theory &, const Given &)> apply;
	GivenQuery hypothesis = nullptr;
};

/* The automaton of an expression, normalized as the decision procedure does */
auto normalized(const RegExp &re, const Theory &theory) -> NFA
{
	auto nfa = re.toNFA();
	normalize(nfa, theory);
	return nfa;
}

/* The relation a word denotes */
auto evalWord(Semantics &sem, Graph &g, const std::vector<TransLabel> &word) -> Matrix
{
	auto m = Matrix::identity(g.ctx(), g.size());
	for (const auto &l : word)
		m = m.compose(sem.eval(l));
	return m;
}

auto transforms() -> std::vector<Transform>
{
	using C = Contract;
	return {
		{"removeDeadStates", false, C::Equivalent,
		 [](NFA &n, const Theory &, const Given &) { removeDeadStates(n); }},
		{"removeSimilarTransitions", false, C::Equivalent,
		 [](NFA &n, const Theory &, const Given &) { removeSimilarTransitions(n); }},
		{"removeRedundantSelfLoops", false, C::Equivalent,
		 [](NFA &n, const Theory &, const Given &) { removeRedundantSelfLoops(n); }},
		{"compactEdges", false, C::Equivalent,
		 [](NFA &n, const Theory &t, const Given &) { compactEdges(n, t); }},
		{"breakToParts", false, C::Equivalent,
		 [](NFA &n, const Theory &, const Given &) { breakToParts(n); }},
		/* Pre: no state is reached by both a predicate and a relation, which
		 * removeConsecutivePredicates establishes before it calls the pass */
		{"addTransitivePredicateEdges", false, C::Equivalent,
		 [](NFA &n, const Theory &t, const Given &) {
			 splitMixedIncoming(n);
			 addTransitivePredicateEdges(n, t);
		 }},
		{"simplify", false, C::Equivalent,
		 [](NFA &n, const Theory &t, const Given &) { simplify(n, t); }},
		{"saturateDomains", false, C::Equivalent,
		 [](NFA &n, const Theory &t, const Given &) { saturateDomains(n, t); }},
		{"removeConsecutivePredicates", false, C::Equivalent,
		 [](NFA &n, const Theory &t, const Given &) { removeConsecutivePredicates(n, t); }},
		{"normalize", false, C::Equivalent,
		 [](NFA &n, const Theory &t, const Given &) { normalize(n, t); }},
		{"to_DFA", true, C::Equivalent,
		 [](NFA &n, const Theory &, const Given &) { n = n.to_DFA().first; }},
		{"saturateInitFinalPreds", true, C::KeepsCycles,
		 [](NFA &n, const Theory &t, const Given &) { saturateInitFinalPreds(n, t); }},
		{"saturateLoc", true, C::KeepsCycles,
		 [](NFA &n, const Theory &t, const Given &) { saturateLoc(n, t); }},
		{"saturateRotate", true, C::AddsNoCycles,
		 [](NFA &n, const Theory &t, const Given &) { saturateRotate(n, t); }},

		/* The saturations of a right-hand side, each under its hypothesis */
		{"saturateEmpty", true, C::Weaker,
		 [](NFA &n, const Theory &t, const Given &g) {
			 saturateEmpty(n, normalized(*g.expr, t));
		 },
		 [](Graph & /*g*/, Semantics &sem, const Given &g) {
			 return sem.eval(*g.expr).isEmpty();
		 }},
		{"saturateID", true, C::Weaker,
		 [](NFA &n, const Theory &t, const Given &g) {
			 saturateID(n, normalized(*g.expr, t));
		 },
		 [](Graph &g, Semantics &sem, const Given &giv) {
			 return sem.eval(*giv.expr).includedIn(Matrix::identity(g.ctx(), g.size()));
		 }},
		{"saturateTransitive", true, C::Weaker,
		 [](NFA &n, const Theory &, const Given &g) { saturateTransitive(n, g.rel); },
		 [](Graph & /*g*/, Semantics &sem, const Given &g) {
			 auto r = sem.eval(g.rel);
			 return r.compose(r).includedIn(r);
		 }},
		{"saturateBuiltin", true, C::Weaker,
		 [](NFA &n, const Theory &t, const Given &g) {
			 saturateBuiltin(n, g.rel, normalized(*g.expr, t), t);
		 },
		 [](Graph & /*g*/, Semantics &sem, const Given &g) {
			 return sem.eval(*g.expr).includedIn(sem.eval(g.rel));
		 }},
		{"saturateSubword", true, C::Weaker,
		 [](NFA &n, const Theory &t, const Given &g) {
			 saturateSubword(n, normalized(*g.expr, t), g.word, t);
		 },
		 [](Graph &g, Semantics &sem, const Given &giv) {
			 return sem.eval(*giv.expr).includedIn(evalWord(sem, g, giv.word));
		 }},
	};
}

auto violation(Contract c, const Matrix &before, const Matrix &after) -> Term
{
	switch (c) {
	case Contract::Equivalent:
		return before.differsFrom(after);
	case Contract::KeepsCycles: {
		std::vector<Term> lost;
		for (auto e = 0U; e < before.size(); e++)
			lost.push_back(before(e, e) && !after(e, e));
		return anyOf(before.ctx(), lost);
	}
	case Contract::AddsNoCycles:
		return after.anyReflexive() && !before.anyReflexive();
	case Contract::Weaker:
		return !after.includedIn(before);
	}
	return Term::constant(before.ctx(), false);
}

auto render(const NFA &nfa) -> std::string
{
	std::ostringstream os;
	os << nfa;
	return os.str();
}

} // namespace

auto testTransforms(const TransformOptions &opts) -> bool
{
	ParsingDriver driver; /* registers the builtins */
	auto module = driver.takeModule();
	const auto &theory = module->getTheory();
	auto noHypotheses = [](Graph &g, Semantics & /*sem*/) {
		return Term::constant(g.ctx(), true);
	};

	RandomRE gen(opts.seed);
	auto all = transforms();
	std::map<std::string, unsigned> failures;
	auto ok = true;

	for (auto c = 0U; c < opts.cases; c++) {
		auto re = gen.expr(opts.depth);
		auto text = toString(*re, theory);
		Given given{.expr = gen.expr(2), .rel = gen.relation(), .word = gen.word()};

		/* toNFA itself: the automaton of RE denotes what RE does */
		if (opts.only.empty() || opts.only == "toNFA") {
			auto nfa = re->toNFA();
			auto s = search(
				*module, noHypotheses,
				[&](Graph & /*g*/, Semantics &sem) {
					return sem.eval(*re).differsFrom(sem.eval(nfa));
				},
				opts.search);
			if (s.outcome == Search::Outcome::Counterexample) {
				ok = false;
				failures["toNFA"]++;
				std::cout << "VIOLATION toNFA on " << text << "\n"
					  << render(nfa) << s.detail;
			}
		}

		for (const auto &t : all) {
			if (!opts.only.empty() && opts.only != t.name)
				continue;
			auto before = re->toNFA();
			if (t.normalizeFirst)
				normalize(before, theory);
			auto after = copy(before);
			t.apply(after, theory, given);

			auto s = search(
				*module,
				[&](Graph &g, Semantics &sem) {
					return t.hypothesis ? t.hypothesis(g, sem, given)
							    : Term::constant(g.ctx(), true);
				},
				[&](Graph & /*g*/, Semantics &sem) {
					return violation(t.contract, sem.eval(before),
							 sem.eval(after));
				},
				opts.search);
			if (s.outcome == Search::Outcome::Counterexample) {
				ok = false;
				if (failures[t.name]++ < 3 || opts.verbose)
					std::cout
						<< "VIOLATION " << t.name << " on " << text
						<< (t.hypothesis
							    ? "\n  given: " +
								      toString(*given.expr, theory)
							    : std::string())
						<< "\n  before:\n"
						<< render(before) << "  after:\n"
						<< render(after) << "  graph:\n"
						<< s.detail << "\n";
			} else if (s.outcome == Search::Outcome::Unknown) {
				std::cout << "unknown: " << t.name << " on " << text << "\n";
			}
		}
	}

	std::cout << "\n" << opts.cases << " expressions; violations per transformation:";
	if (failures.empty())
		std::cout << " none";
	for (const auto &[name, count] : failures)
		std::cout << " " << name << "=" << count;
	std::cout << "\n";
	return ok;
}

} // namespace oracle
