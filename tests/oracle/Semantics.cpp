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

#include "SavedExp.hpp"
#include "Theory.hpp"

#include <algorithm>
#include <sstream>
#include <string>

namespace oracle {

Semantics::Semantics(Graph &g, const KatModule &module) : g_(&g), theory_(&module.getTheory())
{
	for (const auto &let : module.lets()) {
		const auto &name = let->getName();
		if (dynamic_cast<const ViewExp *>(let->getSaved()) != nullptr &&
		    name.substr(name.rfind(':') == std::string::npos ? 0 : name.rfind(':') + 1) ==
			    "hb")
			hbView_ = let->getRE();
	}

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

/* formal: begin LetterSemantics, mirrored by formal/KaterCert/Label.lean */
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
			if (auto p = positional(base.toBuiltin()))
				return *p;
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
/* formal: end LetterSemantics */

auto Semantics::evalShared(const RegExp &re) -> const Matrix &
{
	for (const auto &[e, m] : shared_)
		if (*e == re)
			return m;
	auto m = eval(re);
	return shared_.emplace_back(&re, std::move(m)).second;
}

auto Semantics::genmcHb() -> const Matrix &
{
	if (!hb_) {
		if (hbView_ != nullptr)
			hb_ = evalShared(*hbView_);
		else if (auto hb = g_->genmcHb())
			hb_ = std::move(hb);
		else
			throw Unsupported("GenMC's hb, of a module without a view hb");
	}
	return *hb_;
}

auto isHbPositional(Relation::BuiltinID r) -> bool
{
	using RB = Relation::BuiltinID;
	return r == RB::last_na_reads || r == RB::last_na_writes || r == RB::last_at_reads ||
	       r == RB::last_at_writes || r == RB::unprotected;
}

/*
 * GenMC's ExecutionState keeps, for each location, the NA reads, the atomic
 * reads, the atomic writes and the accesses made while no hazard pointer
 * protected the block: each access it records drops the ones in its hb view
 * (AdaptiveView::operator+=), so the ones left are the hb-maximal of those
 * recorded. Of the NA writes it keeps the last (lastNAWriteEvent_). Event Y
 * asks about its location (pomax_*_pos(); unprotected_pos() for allocations,
 * frees and retires) with the events before it recorded.
 */
auto hbPositional(Graph &g, Relation::BuiltinID r, const Matrix &hb) -> Matrix
{
	using RB = Relation::BuiltinID;
	auto n = g.size();
	auto na = [&](unsigned e) { return g.hasOrder(e, Order::NA); };
	auto access = [&](unsigned e) { return g.is(e, Kind::R) || g.is(e, Kind::W); };
	auto recorded = [&](unsigned e) -> Term {
		switch (r) {
		case RB::last_na_reads:
			return g.is(e, Kind::R) && na(e);
		case RB::last_na_writes:
			return g.is(e, Kind::W) && na(e);
		case RB::last_at_reads:
			return g.is(e, Kind::R) && !na(e);
		case RB::last_at_writes:
			return g.is(e, Kind::W) && !na(e);
		default:
			return access(e) && !g.protectedWhenAdded(e);
		}
	};
	auto lifecycle = [&](unsigned e) {
		return g.is(e, Kind::Alloc) || g.is(e, Kind::Free) || g.is(e, Kind::HpRetire);
	};
	auto asks = [&](unsigned e) {
		return r == RB::unprotected ? lifecycle(e) : access(e) || lifecycle(e);
	};
	auto byHb = r != RB::last_na_writes;

	Matrix m(g.ctx(), n);
	for (auto x = 0U; x < n; x++) {
		for (auto y = 0U; y < n; y++) {
			if (x == y)
				continue;
			auto t = asks(y) && recorded(x) && g.sameBlock(x, y) && g.addedBefore(x, y);
			for (auto z = 0U; z < n && !t.isFalse(); z++) {
				if (z == x || z == y)
					continue;
				auto later = recorded(z) && g.sameBlock(z, y) &&
					     g.addedBefore(x, z) && g.addedBefore(z, y);
				t = t && !(byHb ? later && hb(x, z) : later);
			}
			m.set(x, y, t);
		}
	}
	return m;
}

auto Semantics::positional(Relation::BuiltinID r) -> std::optional<Matrix>
{
	if (!isHbPositional(r))
		return std::nullopt;
	if (auto it = positional_.find(r); it != positional_.end())
		return it->second;
	/* last_na_writes keeps the last, whatever hb is: a module needs no hb for it */
	auto m = r == Relation::BuiltinID::last_na_writes
			 ? hbPositional(*g_, r, Matrix(g_->ctx(), g_->size()))
			 : hbPositional(*g_, r, genmcHb());
	return positional_.emplace(static_cast<int>(r), std::move(m)).first->second;
}

/* formal: begin ExpSemantics, mirrored by formal/KaterCert/Exp.lean */
/* Whether RE refers to a relation of RECS through its inverse */
static auto refersInverted(const RegExp &re,
			   const std::ranges::ref_view<const std::vector<Relation>> &recs) -> bool
{
	if (const auto *charRE = dynamic_cast<const CharRE *>(&re)) {
		const auto &rel = charRE->getLabel().getRelation();
		return rel.has_value() && rel->isInverse() &&
		       std::ranges::any_of(recs,
					   [&](auto &r) { return r.getID() == rel->getID(); });
	}
	return std::ranges::any_of(re.kids(), [&](auto &k) { return refersInverted(*k, recs); });
}

auto Semantics::evalMutRec(const MutRecRE &re) -> Matrix
{
	auto n = g_->size();
	auto &c = g_->ctx();
	auto recs = re.recs();
	auto k = static_cast<unsigned>(re.getNumKids());

	/* `x^-1` flips the definitions of x in place, so that they refer to
	 * x^-1: such a definition is the inverse of the one it was flipped from */
	if (std::ranges::any_of(re.kids(), [&](auto &kid) { return refersInverted(*kid, recs); })) {
		auto unflipped = re.clone();
		unflipped->flip();
		if (const auto *orig = dynamic_cast<const MutRecRE *>(&*unflipped);
		    orig != nullptr && std::ranges::none_of(orig->kids(), [&](auto &kid) {
			    return refersInverted(*kid, recs);
		    }))
			return evalMutRec(*orig).transpose();
		throw Unsupported("a recursive definition through both a relation and its inverse");
	}

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
/* formal: end ExpSemantics */

/* The most rounds of NFASemantics whose terms it does not name */
constexpr unsigned unnamedRounds = 24;

/* formal: begin NFASemantics, mirrored by formal/KaterCert/NFA.lean */
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

		/* A shortest path visits each (state, event) pair at most once.
		 * The terms nest once per round, which Z3 does not survive past a
		 * few hundred: with more than unnamedRounds rounds, each round's
		 * terms are named (Graph::define), which costs time on smaller
		 * automata */
		const auto nameTerms = states * n > unnamedRounds;
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
			if (nameTerms)
				for (auto &row : next)
					for (auto &t : row)
						t = g_->define(t);
			reach = std::move(next);
		}

		for (const auto *s : nfa.accepting())
			for (auto b = 0U; b < n; b++)
				result.set(a, b, result(a, b) || reach[s->getId()][b]);
	}
	return result;
}
/* formal: end NFASemantics */

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
	/* "total r": r is a strict total order, on all events (the Kater paper,
	 * Prop. 3.12). Kater ignores totality of anything but a relation */
	if (const auto *tot = dynamic_cast<const TotalityConstraint *>(&c)) {
		const auto *charRE = dynamic_cast<const CharRE *>(tot->getRE());
		if (charRE != nullptr && charRE->getLabel().isRelation()) {
			auto r = eval(*charRE);
			auto n = g_->size();
			std::vector<Term> order{r.compose(r).includedIn(r)};
			for (auto e = 0U; e < n; e++) {
				order.push_back(!r(e, e));
				for (auto f = e + 1; f < n; f++)
					order.push_back(r(e, f) || r(f, e));
			}
			return allOf(g_->ctx(), order);
		}
	}
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
	auto predicate = [&](Predicate::ID id) -> Predicate {
		if (auto it = predicates_.find(id); it != predicates_.end())
			return it->second;
		if (id >= 0)
			return Predicate::createBuiltin(static_cast<Predicate::BuiltinID>(id));
		throw Unsupported("disjointness of undeclared predicates");
	};
	for (const auto &set : disjointSets) {
		for (auto it1 = set.begin(); it1 != set.end(); ++it1) {
			for (auto it2 = it1 + 1; it2 != set.end(); ++it2) {
				auto p1 = predicate(*it1);
				auto p2 = predicate(*it2);
				for (auto e = 0U; e < g_->size(); e++)
					axioms.push_back(!(eval(p1, e) && eval(p2, e)));
			}
		}
	}
	return allOf(c, axioms);
}

} // namespace oracle
