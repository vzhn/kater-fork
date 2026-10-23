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

#include "Semantics.hpp"

#include "Theory.hpp"

#include <algorithm>
#include <sstream>
#include <string>

namespace oracle {

Semantics::Semantics(Graph &g, const KatModule &module) : g_(&g), theory_(&module.getTheory())
{
	/* Every declared symbol has a let of its own name */
	for (const auto &let : module.lets()) {
		const auto *charRE = dynamic_cast<const CharRE *>(let->getRE());
		if (charRE == nullptr)
			continue;
		const auto &lab = charRE->getLabel();
		if (lab.isPredicate() && lab.getPreChecks().size() == 1) {
			auto p = *lab.getPreChecks().begin();
			if (!p.isComplement())
				predicates_.emplace(p.getID(), p);
		} else if (lab.isRelation() && !lab.hasPreChecks() && !lab.hasPostChecks()) {
			auto r = *lab.getRelation();
			if (!r.isInverse())
				relations_.emplace(r.getID(), r);
		}
	}
	for (const auto &[id, r] : relations_)
		if (r.isUser() && theory_->hasPerLoc(r))
			perLocBase_.emplace(theory_->getPerLoc(r).getID(), r);
}

auto Semantics::eval(const Predicate &p, unsigned e) -> Term
{
	auto base = [&]() -> Term {
		if (!p.isBuiltin())
			return g_->userPredicate(p, e);
		auto t = g_->predicate(static_cast<Predicate::BuiltinID>(p.getID()), e);
		if (!t.has_value())
			throw Unsupported("predicate " + nameOf(p, theory_));
		return *t;
	}();
	return p.isComplement() ? !base : base;
}

auto Semantics::eval(const PredicateSet &ps, unsigned e) -> Term
{
	auto t = Term::constant(g_->ctx(), true);
	for (const auto &p : ps)
		t = t && eval(p, e);
	return t;
}

auto Semantics::eval(const Relation &r) -> Matrix
{
	auto base = r;
	if (base.isInverse())
		base.invert();

	auto m = [&]() -> Matrix {
		if (auto it = rec_.find(base.getID()); it != rec_.end())
			return it->second;
		if (base.isBuiltin()) {
			const auto *b = g_->relation(base.toBuiltin());
			if (b == nullptr)
				throw Unsupported("relation " + nameOf(base, theory_));
			return *b;
		}
		if (auto it = perLocBase_.find(base.getID()); it != perLocBase_.end())
			return eval(it->second).intersect(g_->sameLocRelation());
		return g_->userRelation(base);
	}();
	return r.isInverse() ? m.transpose() : m;
}

auto Semantics::eval(const TransLabel &lab) -> Matrix
{
	auto n = g_->size();
	auto &c = g_->ctx();
	Matrix result(c, n);

	if (lab.isPredicate()) {
		for (auto e = 0U; e < n; e++)
			result.set(e, e, eval(lab.getPreChecks(), e));
		return result;
	}

	auto rel = eval(*lab.getRelation());
	for (auto i = 0U; i < n; i++)
		for (auto j = 0U; j < n; j++)
			result.set(i, j,
				   eval(lab.getPreChecks(), i) && rel(i, j) &&
					   eval(lab.getPostChecks(), j));
	return result;
}

auto Semantics::evalMutRec(const MutRecRE &re) -> Matrix
{
	auto n = g_->size();
	auto &c = g_->ctx();
	auto recs = re.recs();
	auto k = static_cast<unsigned>(re.getNumKids());

	/* Kleene iteration from the empty relations. The definitions are
	 * left-linear, so a pair is derived through a chain of distinct
	 * (relation, endpoint) pairs: k * n rounds reach the fixpoint */
	std::vector<Matrix> approx(k, Matrix(c, n));
	std::unordered_map<Relation::ID, Matrix> saved;
	for (const auto &r : recs)
		if (auto it = rec_.find(r.getID()); it != rec_.end())
			saved.emplace(r.getID(), it->second);

	for (auto round = 0U; round <= k * n; round++) {
		for (auto i = 0U; i < k; i++)
			rec_.insert_or_assign(recs[i].getID(), approx[i]);
		std::vector<Matrix> next;
		next.reserve(k);
		for (auto i = 0U; i < k; i++)
			next.push_back(eval(*re.getKid(i)));
		approx = std::move(next);
	}

	for (const auto &r : recs) {
		rec_.erase(r.getID());
		if (auto it = saved.find(r.getID()); it != saved.end())
			rec_.emplace(r.getID(), it->second);
	}

	auto pos = std::ranges::find(recs, re.getRelation()) - std::ranges::begin(recs);
	return approx[static_cast<size_t>(pos)];
}

auto Semantics::eval(const RegExp &re) -> Matrix
{
	auto n = g_->size();
	auto &c = g_->ctx();

	if (const auto *charRE = dynamic_cast<const CharRE *>(&re))
		return eval(charRE->getLabel());

	if (dynamic_cast<const AltRE *>(&re) != nullptr) {
		Matrix result(c, n);
		for (const auto &k : re.kids())
			result = result.unite(eval(*k));
		return result;
	}
	if (dynamic_cast<const SeqRE *>(&re) != nullptr) {
		auto result = Matrix::identity(c, n);
		for (const auto &k : re.kids())
			result = result.compose(eval(*k));
		return result;
	}
	if (dynamic_cast<const AndRE *>(&re) != nullptr)
		return eval(*re.getKid(0)).intersect(eval(*re.getKid(1)));
	if (dynamic_cast<const MinusRE *>(&re) != nullptr)
		return eval(*re.getKid(0)).minus(eval(*re.getKid(1)));
	if (dynamic_cast<const PlusRE *>(&re) != nullptr)
		return eval(*re.getKid(0)).plus();
	if (dynamic_cast<const StarRE *>(&re) != nullptr)
		return eval(*re.getKid(0)).star();
	if (dynamic_cast<const QMarkRE *>(&re) != nullptr)
		return eval(*re.getKid(0)).optional();
	if (const auto *mutRec = dynamic_cast<const MutRecRE *>(&re))
		return evalMutRec(*mutRec);
	if (dynamic_cast<const RotRE *>(&re) != nullptr)
		throw Unsupported("rot outside the right-hand side of a constraint");
	throw Unsupported("unknown kind of expression");
}

auto Semantics::eval(const NFA &nfa) -> Matrix
{
	auto n = g_->size();
	auto &c = g_->ctx();
	auto states = static_cast<unsigned>(nfa.getNumStates());
	Matrix result(c, n);

	/* The meaning of each transition label, computed once */
	std::vector<std::vector<std::pair<unsigned, Matrix>>> outs(states);
	for (const auto &s : nfa.states())
		for (const auto &t : s->outs())
			outs[s->getId()].emplace_back(t.dest->getId(), eval(t.label));

	for (auto a = 0U; a < n; a++) {
		/* reach[q][e]: some path from (start, a) arrives at q on event e */
		std::vector<std::vector<Term>> reach(
			states, std::vector<Term>(n, Term::constant(c, false)));
		for (const auto *s : nfa.starting())
			reach[s->getId()][a] = Term::constant(c, true);

		/* A shortest path visits each (state, event) pair at most once */
		for (auto round = 0U; round < states * n; round++) {
			auto next = reach;
			for (auto p = 0U; p < states; p++) {
				for (const auto &[q, lab] : outs[p]) {
					for (auto e = 0U; e < n; e++) {
						if (reach[p][e].isFalse())
							continue;
						for (auto f = 0U; f < n; f++)
							next[q][f] = next[q][f] ||
								     (reach[p][e] && lab(e, f));
					}
				}
			}
			reach = std::move(next);
		}

		for (const auto *s : nfa.accepting())
			for (auto b = 0U; b < n; b++)
				result.set(a, b, result(a, b) || reach[s->getId()][b]);
	}
	return result;
}

auto Semantics::holdsSubset(const SubsetConstraint &c) -> Term
{
	auto lhs = eval(*c.getLHS());
	auto rhs = eval(*c.getRHS());
	auto n = g_->size();
	auto &ctx = g_->ctx();

	/* "A & id <= rot B": a cycle of A is a rotation of a cycle of B, so
	 * B has a cycle whenever A has one. Without & id, Kater only accepts an
	 * A within id, whose pairs are all cycles */
	if (c.rotated())
		return implies(lhs.anyReflexive(), rhs.anyReflexive());
	if (c.sameEnds()) {
		std::vector<Term> each;
		for (auto e = 0U; e < n; e++)
			each.push_back(implies(lhs(e, e), rhs(e, e)));
		return allOf(ctx, each);
	}
	return lhs.includedIn(rhs);
}

auto Semantics::holds(const Constraint &c) -> Term
{
	if (const auto *eq = dynamic_cast<const EqualityConstraint *>(&c)) {
		auto inverse = SubsetConstraint::create(eq->getRHS()->clone(),
							eq->getLHS()->clone(), eq->sameEnds(),
							eq->rotated());
		return holdsSubset(*eq) && holdsSubset(*inverse);
	}
	if (const auto *sub = dynamic_cast<const SubsetConstraint *>(&c))
		return holdsSubset(*sub);
	if (const auto *acyc = dynamic_cast<const AcyclicConstraint *>(&c))
		return !eval(*acyc->getRE()).plus().anyReflexive();
	throw Unsupported("constraint " + [&] {
		std::ostringstream s;
		c.dump(s, theory_);
		return s.str();
	}());
}

auto Semantics::declarationAxioms(const VSet<VSet<Predicate::ID>> &disjointSets) -> Term
{
	auto &c = g_->ctx();
	std::vector<Term> axioms;
	for (const auto &set : disjointSets) {
		if (std::ranges::none_of(set, [](auto id) { return id < 0; }))
			continue;
		for (auto it1 = set.begin(); it1 != set.end(); ++it1) {
			for (auto it2 = it1 + 1; it2 != set.end(); ++it2) {
				auto p1 = predicates_.find(*it1);
				auto p2 = predicates_.find(*it2);
				if (p1 == predicates_.end() || p2 == predicates_.end())
					throw Unsupported("disjointness of undeclared predicates");
				for (auto e = 0U; e < g_->size(); e++)
					axioms.push_back(
						!(eval(p1->second, e) && eval(p2->second, e)));
			}
		}
	}
	return allOf(c, axioms);
}

} // namespace oracle
