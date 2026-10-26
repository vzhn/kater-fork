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

#include "Graph.hpp"

#include "Theory.hpp"

#include <algorithm>
#include <string>

namespace oracle {

using PB = Predicate::BuiltinID;
using RB = Relation::BuiltinID;

/*
 * The orderings each kind of label can carry. Reads and writes are left
 * unconstrained (GenMC gives RMW parts the ordering of the whole RMW);
 * the rest follows the label constructors of GenMC.
 */
static auto allowedOrders(Kind k) -> std::vector<Order>
{
	using enum Order;
	switch (k) {
	case Kind::R:
	case Kind::W:
	case Kind::Other:
		return {NA, RLX, ACQ, REL, ACQ_REL, SC};
	case Kind::F:
		return {ACQ, REL, ACQ_REL, SC};
	case Kind::TC:
	case Kind::TE:
	case Kind::HpProtect:
		return {REL};
	case Kind::TB:
	case Kind::TJ:
		return {ACQ};
	case Kind::TK:
	case Kind::Alloc:
	case Kind::Free:
	case Kind::HpRetire:
	case Kind::MethodBegin:
	case Kind::MethodEnd:
		return {NA};
	}
	return {};
}

Graph::Graph(z3::context &ctx, unsigned n)
	: ctx_(&ctx), n_(n), rf_(ctx, n), mo_(ctx, n), ctrl_(ctx, n), addr_(ctx, n), data_(ctx, n),
	  pctrl_(ctx, n), tc_(ctx, n), tj_(ctx, n), lin_(ctx, n), sameThread_(ctx, n),
	  sameLoc_(ctx, n), sameBlock_(ctx, n), sameHp_(ctx, n), axioms_(ctx), definitions_(ctx)
{
	buildStructure();
	buildDerived();
	buildAxioms();
}

Graph::Graph(z3::context &ctx, const Execution &x, UserPredicates userPredicates,
	     std::optional<std::vector<unsigned>> order)
	: ctx_(&ctx), n_(x.size()), concrete_(true),
	  concreteUserPredicates_(std::move(userPredicates)),
	  concreteOrder_(order ? std::move(*order) : x.additionOrder(std::nullopt).events),
	  rf_(ctx, n_), mo_(ctx, n_), ctrl_(ctx, n_), addr_(ctx, n_), data_(ctx, n_),
	  pctrl_(ctx, n_), tc_(ctx, n_), tj_(ctx, n_), lin_(ctx, n_), sameThread_(ctx, n_),
	  sameLoc_(ctx, n_), sameBlock_(ctx, n_), sameHp_(ctx, n_), axioms_(ctx), definitions_(ctx)
{
	buildStructure(x);
	buildDerived();
	buildAxioms();
	/* Nothing is left to the solver: the axioms of the heap and of the
	 * order are known now */
	buildHeap();
	buildOrder();
}

auto Graph::freshBool(const std::string &name) -> z3::expr
{
	return ctx().bool_const(name.c_str());
}

auto Graph::freshMatrix(const std::string &name,
			const std::function<bool(unsigned, unsigned)> &allowed) -> Matrix
{
	Matrix m(ctx(), n_);
	for (auto i = 0U; i < n_; i++)
		for (auto j = 0U; j < n_; j++)
			if (allowed(i, j))
				m.set(i, j,
				      freshBool(name + "_" + std::to_string(i) + "_" +
						std::to_string(j)));
	return m;
}

auto Graph::define(const Term &t) -> Term
{
	if (t.isTrue() || t.isFalse() || t.expr().is_const())
		return t;
	auto name = freshBool("def_" + std::to_string(definitions_.size()));
	definitions_.push_back(name == t.expr());
	return {name};
}

void Graph::addAxiom(const Term &t)
{
	/* Over a concrete graph every axiom folds to a constant (the
	 * comparisons of locations too, see buildAxioms()): simplify the rest */
	if (concrete_ && !t.isTrue() && !t.isFalse()) {
		addAxiom(Term(t.expr().simplify()));
		return;
	}
	if (!t.isTrue())
		axioms_.push_back(t.expr());
}

void Graph::buildStructure()
{
	auto &c = ctx();
	auto ev = [](const char *what, unsigned e) {
		return std::string(what) + std::to_string(e);
	};

	for (auto e = 0U; e < n_; e++) {
		newThread_.push_back(e == 0 ? Term::constant(c, true)
					    : freshBool(ev("newthread", e)));

		std::vector<Term> kinds;
		for (auto k = 0U; k < numKinds; k++)
			kinds.emplace_back(
				freshBool(ev("kind", e) + "_" + kindName(static_cast<Kind>(k))));
		kind_.push_back(std::move(kinds));

		std::vector<Term> orders;
		for (auto o = 0U; o < numOrders; o++)
			orders.emplace_back(
				freshBool(ev("order", e) + "_" + orderName(static_cast<Order>(o))));
		order_.push_back(std::move(orders));

		excl_.emplace_back(freshBool(ev("excl", e)));
		loc_.push_back(c.int_const(ev("loc", e).c_str()));
		hp_.push_back(c.int_const(ev("hp", e).c_str()));
		durable_.emplace_back(freshBool(ev("durable", e)));
		recovery_.emplace_back(freshBool(ev("recovery", e)));
		abstractLock_.emplace_back(freshBool(ev("abslock", e)));
		dependableOther_.emplace_back(freshBool(ev("depother", e)));
	}

	/* Threads are contiguous: i and j (i < j) share one iff no thread starts in (i, j] */
	for (auto i = 0U; i < n_; i++) {
		sameThread_.set(i, i, Term::constant(c, true));
		auto same = Term::constant(c, true);
		for (auto j = i + 1; j < n_; j++) {
			same = same && !newThread_[j];
			sameThread_.set(i, j, same);
			sameThread_.set(j, i, same);
		}
	}

	/* Two accesses are on the same location if they access the same
	 * address. Every event is on the same location as itself: that only
	 * matters for the per-location variants of user relations (the builtin
	 * ones are irreflexive), and is what Kater's saturateLoc assumes */
	for (auto i = 0U; i < n_; i++)
		for (auto j = 0U; j < n_; j++)
			sameLoc_.set(i, j,
				     i == j ? Term::constant(c, true)
					    : isLocated(i) && isLocated(j) &&
						      Term(loc_[i] == loc_[j]));

	/* The location of allocations, frees, retires and protections: GenMC's
	 * alloc_pos() and the like look up the block of the event's address */
	for (auto i = 0U; i < n_; i++) {
		for (auto j = 0U; j < n_; j++) {
			sameBlock_.set(i, j,
				       i == j ? hasLocation(i)
					      : hasLocation(i) && hasLocation(j) &&
							Term(loc_[i] == loc_[j]));
			sameHp_.set(i, j,
				    i == j ? Term::constant(c, true) : Term(hp_[i] == hp_[j]));
		}
	}

	auto distinct = [](unsigned i, unsigned j) { return i != j; };
	auto forward = [](unsigned i, unsigned j) { return i < j; };
	rf_ = freshMatrix("rf", distinct);
	mo_ = freshMatrix("mo", distinct);
	ctrl_ = freshMatrix("ctrl", forward);
	addr_ = freshMatrix("addr", forward);
	data_ = freshMatrix("data", forward);
	pctrl_ = freshMatrix("pctrl", forward);
	tc_ = freshMatrix("tc", distinct);
	tj_ = freshMatrix("tj", distinct);
	lin_ = freshMatrix("lin", distinct);
}

void Graph::buildStructure(const Execution &x)
{
	auto &c = ctx();
	auto val = [&](bool b) { return Term::constant(c, b); };

	for (auto e = 0U; e < n_; e++) {
		const auto &ev = x.events[e];
		newThread_.push_back(val(e == 0 || ev.thread != x.events[e - 1].thread));

		std::vector<Term> kinds;
		for (auto k = 0U; k < numKinds; k++)
			kinds.push_back(val(static_cast<Kind>(k) == ev.kind));
		kind_.push_back(std::move(kinds));

		std::vector<Term> orders;
		for (auto o = 0U; o < numOrders; o++)
			orders.push_back(val(static_cast<Order>(o) == ev.order));
		order_.push_back(std::move(orders));

		excl_.push_back(val(ev.excl));
		loc_.push_back(c.int_val(std::max(ev.loc, 0)));
		hp_.push_back(c.int_val(static_cast<int>(ev.hp)));
		/* GenMC's label flags: an Execution has none of them */
		for (auto *flags : {&durable_, &recovery_, &abstractLock_, &dependableOther_})
			flags->push_back(val(false));
	}

	for (auto i = 0U; i < n_; i++) {
		for (auto j = 0U; j < n_; j++) {
			const auto &a = x.events[i];
			const auto &b = x.events[j];
			sameThread_.set(i, j, val(a.thread == b.thread));
			sameLoc_.set(
				i, j,
				val(i == j || (a.isAccess() && b.isAccess() && a.loc == b.loc)));
			sameBlock_.set(i, j,
				       val(a.hasLocation() && b.hasLocation() && a.loc == b.loc));
			sameHp_.set(i, j, val(a.hp == b.hp));
			rf_.set(i, j, val(i != j && x.rf[j] == static_cast<int>(i)));
			mo_.set(i, j, val(x.moBefore(i, j)));
			ctrl_.set(i, j, val(Execution::has(x.ctrl, i, j)));
			addr_.set(i, j, val(Execution::has(x.addr, i, j)));
			data_.set(i, j, val(Execution::has(x.data, i, j)));
			pctrl_.set(i, j, val(Execution::has(x.pctrl, i, j)));
			tc_.set(i, j, val(Execution::has(x.tc, i, j)));
			tj_.set(i, j, val(Execution::has(x.tj, i, j)));
			lin_.set(i, j, val(Execution::has(x.lin, i, j)));
		}
	}
}

void Graph::buildDerived()
{
	auto &c = ctx();
	auto n = n_;

	/* po: forward within a thread; po-imm: the next event of the thread */
	Matrix po(c, n);
	Matrix poImm(c, n);
	for (auto i = 0U; i < n; i++)
		for (auto j = i + 1; j < n; j++) {
			po.set(i, j, sameThread(i, j));
			if (j == i + 1)
				poImm.set(i, j, sameThread(i, j));
		}

	/* po-loc, and the next event of the thread on the same location */
	auto poLoc = po.intersect(sameLoc_);
	Matrix poLocImm(c, n);
	for (auto i = 0U; i < n; i++)
		for (auto j = i + 1; j < n; j++) {
			auto t = poLoc(i, j);
			for (auto k = i + 1; k < j; k++)
				t = t && !sameLoc(i, k);
			poLocImm.set(i, j, t);
		}

	auto internal = sameThread_;
	Matrix external(c, n);
	for (auto i = 0U; i < n; i++)
		for (auto j = 0U; j < n; j++)
			external.set(i, j, !sameThread(i, j));

	/* fr: from a read to the writes mo-after its source (to all, if it reads init) */
	Matrix fr(c, n);
	for (auto r = 0U; r < n; r++) {
		std::vector<Term> sources;
		for (auto w = 0U; w < n; w++)
			sources.push_back(rf_(w, r));
		auto readsInit = !anyOf(c, sources);
		for (auto w = 0U; w < n; w++) {
			if (w == r)
				continue;
			std::vector<Term> later;
			for (auto s = 0U; s < n; s++)
				later.push_back(rf_(s, r) && mo_(s, w));
			fr.set(r, w,
			       is(r, Kind::R) && is(w, Kind::W) && sameLoc(r, w) &&
				       (readsInit || anyOf(c, later)));
		}
	}

	/* The immediate successors in mo, and in fr */
	Matrix moImm(c, n);
	Matrix frImm(c, n);
	for (auto i = 0U; i < n; i++)
		for (auto j = 0U; j < n; j++) {
			if (i == j)
				continue;
			auto mi = mo_(i, j);
			auto fi = fr(i, j);
			for (auto k = 0U; k < n; k++) {
				if (k == i || k == j)
					continue;
				mi = mi && !(mo_(i, k) && mo_(k, j));
				fi = fi && !(fr(i, k) && mo_(k, j));
			}
			moImm.set(i, j, mi);
			frImm.set(i, j, fi);
		}

	/* rmw: an exclusive read and the exclusive write right after it */
	Matrix rmw(c, n);
	for (auto i = 0U; i + 1 < n; i++)
		rmw.set(i, i + 1,
			poImm(i, i + 1) && is(i, Kind::R) && isExclusive(i) && is(i + 1, Kind::W) &&
				isExclusive(i + 1) && sameLoc(i, i + 1));

	/* detour (GenMC's): a write and a po-later read of its location that reads elsewhere */
	Matrix detour(c, n);
	for (auto w = 0U; w < n; w++)
		for (auto r = w + 1; r < n; r++)
			detour.set(w, r,
				   is(w, Kind::W) && is(r, Kind::R) && poLoc(w, r) && !rf_(w, r));

	builtins_.emplace(RB::po, po);
	builtins_.emplace(RB::po_imm, poImm);
	builtins_.emplace(RB::po_loc, poLoc);
	builtins_.emplace(RB::po_loc_imm, poLocImm);
	builtins_.emplace(RB::rf, rf_);
	builtins_.emplace(RB::rfe, rf_.intersect(external));
	builtins_.emplace(RB::rfi, rf_.intersect(internal));
	builtins_.emplace(RB::mo, mo_);
	builtins_.emplace(RB::moe, mo_.intersect(external));
	builtins_.emplace(RB::moi, mo_.intersect(internal));
	builtins_.emplace(RB::mo_imm, moImm);
	builtins_.emplace(RB::fr, fr);
	builtins_.emplace(RB::fre, fr.intersect(external));
	builtins_.emplace(RB::fri, fr.intersect(internal));
	builtins_.emplace(RB::fr_imm, frImm);
	builtins_.emplace(RB::rmw, rmw);
	builtins_.emplace(RB::detour, detour);
	builtins_.emplace(RB::ctrl, ctrl_);
	builtins_.emplace(RB::addr, addr_);
	builtins_.emplace(RB::data, data_);
	builtins_.emplace(RB::pctrl, pctrl_);
	builtins_.emplace(RB::tc, tc_);
	builtins_.emplace(RB::tj, tj_);
	builtins_.emplace(RB::lin, lin_);
	builtins_.emplace(RB::any, Matrix(c, n, true));

	/* Heap blocks: the locations an allocation is of */
	heap_.reserve(n);
	for (auto e = 0U; e < n; e++) {
		std::vector<Term> allocs;
		allocs.reserve(n);
		for (auto a = 0U; a < n; a++)
			allocs.push_back(is(a, Kind::Alloc) && sameBlock(a, e));
		heap_.push_back(anyOf(c, allocs));
	}

	/* GenMC's isHazptrProtected(): the closest protection of the event's
	 * block before it in po, through a hazard pointer that does not
	 * protect anything else before the event */
	for (auto e = 0U; e < n; e++) {
		std::vector<Term> through;
		for (auto p = 0U; p < e; p++) {
			auto t = sameThread(p, e) && is(p, Kind::HpProtect) && sameBlock(p, e);
			for (auto q = p + 1; q < e; q++)
				t = t &&
				    !(is(q, Kind::HpProtect) && (sameBlock(q, e) || sameHp_(q, p)));
			through.push_back(t);
		}
		hpProtected_.push_back(anyOf(c, through));
	}
}

auto Graph::memLabel(unsigned e) const -> Term
{
	return isLocated(e) || is(e, Kind::Alloc) || is(e, Kind::Free) || is(e, Kind::HpRetire);
}

void Graph::buildHeap()
{
	if (heapBuilt_)
		return;
	heapBuilt_ = true;

	/* An allocation precedes the events of its block in porf: a thread
	 * accesses the block through the address the allocation returned */
	causal_ = builtins_.at(RB::po).unite(rf_).unite(tc_).unite(tj_).plus();
	for (auto a = 0U; a < n_; a++)
		for (auto e = 0U; e < n_; e++)
			if (a != e)
				addAxiom(implies(is(a, Kind::Alloc) && sameBlock(a, e),
						 (*causal_)(a, e)));
}

void Graph::buildOrder()
{
	if (added_)
		return;
	buildHeap();
	auto &c = ctx();
	auto n = n_;
	Matrix added(c, n);

	/* A concrete graph's order is the one it was given */
	if (concrete_) {
		std::vector<unsigned> at(n, 0);
		for (auto i = 0U; i < concreteOrder_.size(); i++)
			at[concreteOrder_[i]] = i;
		for (auto i = 0U; i < n; i++)
			for (auto j = 0U; j < n; j++)
				added.set(i, j, Term::constant(c, i != j && at[i] < at[j]));
		added_ = std::move(added);
		return;
	}

	/* A strict total order: one unknown per pair, transitive */
	for (auto i = 0U; i < n; i++) {
		for (auto j = i + 1; j < n; j++) {
			auto b = Term(
				freshBool("added_" + std::to_string(i) + "_" + std::to_string(j)));
			added.set(i, j, b);
			added.set(j, i, !b);
		}
	}
	for (auto i = 0U; i < n; i++)
		for (auto j = 0U; j < n; j++)
			for (auto k = 0U; k < n; k++)
				if (i != j && j != k && i != k)
					addAxiom(implies(added(i, j) && added(j, k), added(i, k)));

	/* GenMC adds an event after its po predecessors and its allocation,
	 * and, without a porf cycle, after the events it reads from, was
	 * created by or joins: its execution state holds them in such an order
	 * (reconstructState() rebuilds it so on a restart) */
	auto porfAcyclic = !causal_->anyReflexive();
	for (auto i = 0U; i < n; i++) {
		for (auto j = 0U; j < n; j++) {
			if (i == j)
				continue;
			if (i < j)
				addAxiom(implies(sameThread(i, j), added(i, j)));
			addAxiom(implies(is(i, Kind::Alloc) && sameBlock(i, j), added(i, j)));
			addAxiom(implies(porfAcyclic && (rf_(i, j) || tc_(i, j) || tj_(i, j)),
					 added(i, j)));
		}
	}
	added_ = std::move(added);
}

void Graph::buildPositional()
{
	if (builtins_.contains(RB::alloc))
		return;
	buildOrder();
	auto &c = ctx();
	auto n = n_;
	const auto &added = *added_;

	/* alloc_pos(): the allocation of the event's block */
	Matrix alloc(c, n);
	for (auto a = 0U; a < n; a++)
		for (auto e = 0U; e < n; e++)
			if (a != e)
				alloc.set(a, e,
					  is(a, Kind::Alloc) && memLabel(e) && sameBlock(a, e));

	/* free_pos() and retire_pos(): the last free or retire of the event's
	 * block, before it in the execution state, as the one or the other */
	auto freeing = [&](unsigned f) { return is(f, Kind::Free) || is(f, Kind::HpRetire); };
	Matrix free(c, n);
	Matrix retire(c, n);
	for (auto f = 0U; f < n; f++) {
		for (auto e = 0U; e < n; e++) {
			if (f == e)
				continue;
			auto last = freeing(f) && memLabel(e) && sameBlock(f, e) && added(f, e);
			for (auto g = 0U; g < n; g++)
				if (g != f && g != e)
					last = last && !(freeing(g) && sameBlock(g, e) &&
							 added(f, g) && added(g, e));
			free.set(f, e, last && is(f, Kind::Free));
			retire.set(f, e, last && is(f, Kind::HpRetire));
		}
	}

	/* NOTHPPROT: an access of a retired block, not protected */
	std::vector<Term> notProtected;
	notProtected.reserve(n);
	for (auto e = 0U; e < n; e++) {
		std::vector<Term> retired;
		retired.reserve(n);
		for (auto r = 0U; r < n; r++)
			retired.push_back(retire(r, e));
		notProtected.push_back(isLocated(e) && heap_[e] && anyOf(c, retired) &&
				       !hpProtected_[e]);
	}

	builtins_.emplace(RB::alloc, std::move(alloc));
	builtins_.emplace(RB::free, std::move(free));
	builtins_.emplace(RB::retire, std::move(retire));
	notHpProtected_ = std::move(notProtected);
}

auto Graph::addedBefore(unsigned a, unsigned b) -> Term
{
	buildOrder();
	return (*added_)(a, b);
}

auto Graph::protectedWhenAdded(unsigned x) -> Term
{
	buildOrder();
	if (!protectedWhenAdded_) {
		/* ExecutionState::isProtected(): some hazard pointer protects the
		 * block, its last protection before the access being of it */
		const auto &added = *added_;
		std::vector<Term> result;
		for (auto e = 0U; e < n_; e++) {
			std::vector<Term> through;
			for (auto p = 0U; p < n_; p++) {
				if (p == e)
					continue;
				auto t = is(p, Kind::HpProtect) && sameBlock(p, e) && added(p, e);
				for (auto q = 0U; q < n_; q++)
					if (q != p && q != e)
						t = t &&
						    !(is(q, Kind::HpProtect) && sameHp_(q, p) &&
						      added(p, q) && added(q, e));
				through.push_back(t);
			}
			result.push_back(anyOf(ctx(), through));
		}
		protectedWhenAdded_ = std::move(result);
	}
	return (*protectedWhenAdded_)[x];
}

auto Graph::genmcHb() -> std::optional<Matrix>
{
	if (concrete_)
		return std::nullopt;
	if (!genmcHb_) {
		auto n = n_;
		auto hb = freshMatrix("genmchb", [](unsigned i, unsigned j) { return i != j; });
		auto porf =
			builtins_.at(RB::po).unite(rf_).unite(tc_).unite(tj_).unite(lin_).plus();
		for (auto i = 0U; i < n; i++) {
			for (auto j = 0U; j < n; j++) {
				if (i == j)
					continue;
				if (i < j)
					addAxiom(implies(sameThread(i, j), hb(i, j)));
				addAxiom(implies(hb(i, j), porf(i, j)));
				for (auto k = 0U; k < n; k++)
					if (k != i && k != j)
						addAxiom(implies(hb(i, j) && hb(j, k), hb(i, k)));
			}
		}
		genmcHb_ = std::move(hb);
	}
	return genmcHb_;
}

void Graph::buildAxioms()
{
	auto &c = ctx();
	auto n = n_;

	for (auto e = 0U; e < n; e++) {
		/* Exactly one kind, and one ordering that kind can carry */
		std::vector<Term> kinds(kind_[e].begin(), kind_[e].end());
		addAxiom(anyOf(c, kinds));
		for (auto k1 = 0U; k1 < numKinds; k1++)
			for (auto k2 = k1 + 1; k2 < numKinds; k2++)
				addAxiom(!(kind_[e][k1] && kind_[e][k2]));

		std::vector<Term> orders(order_[e].begin(), order_[e].end());
		addAxiom(anyOf(c, orders));
		for (auto o1 = 0U; o1 < numOrders; o1++)
			for (auto o2 = o1 + 1; o2 < numOrders; o2++)
				addAxiom(!(order_[e][o1] && order_[e][o2]));
		for (auto k = 0U; k < numKinds; k++) {
			std::vector<Term> allowed;
			for (auto o : allowedOrders(static_cast<Kind>(k)))
				allowed.push_back(hasOrder(e, o));
			addAxiom(implies(kind_[e][k], anyOf(c, allowed)));
		}

		/* Only reads and writes can be exclusive, and an exclusive write
		 * always follows the exclusive read of its RMW */
		addAxiom(implies(isExclusive(e), is(e, Kind::R) || is(e, Kind::W)));
		auto excWrite = is(e, Kind::W) && isExclusive(e);
		addAxiom(implies(excWrite, e == 0 ? Term::constant(c, false)
						  : relation(RB::rmw)->operator()(e - 1, e)));

		/* Locations: of accesses, allocations, frees, retires and
		 * protections; numbered by first use */
		auto in = [&](const z3::expr &v, int from, int to) {
			return concrete_ ? Term::constant(c, v.get_numeral_int() >= from &&
								     v.get_numeral_int() <= to)
					 : Term(v >= from && v <= to);
		};
		addAxiom(in(loc_[e], 0, static_cast<int>(e)));
		addAxiom(implies(!hasLocation(e), in(loc_[e], 0, 0)));
		addAxiom(in(hp_[e], 0, static_cast<int>(n) - 1));
		addAxiom(implies(!is(e, Kind::HpProtect), in(hp_[e], 0, 0)));

		/* Frees, retires and protections are of heap blocks (GenMC looks up
		 * the allocation of their address) */
		addAxiom(implies(is(e, Kind::Free) || is(e, Kind::HpRetire) ||
					 is(e, Kind::HpProtect),
				 heap_[e]));

		/* Label flags only exist where GenMC defines them */
		addAxiom(implies(durable_[e], isLocated(e)));
		addAxiom(implies(abstractLock_[e], is(e, Kind::R)));
		addAxiom(implies(dependableOther_[e], is(e, Kind::Other)));
	}

	/* A block has one allocation */
	for (auto a = 0U; a < n; a++)
		for (auto b = a + 1; b < n; b++)
			addAxiom(!(is(a, Kind::Alloc) && is(b, Kind::Alloc) && sameBlock(a, b)));

	for (auto i = 0U; i < n; i++) {
		for (auto j = 0U; j < n; j++) {
			if (i == j)
				continue;

			/* rf: from a write to a read of the same location; one per read */
			addAxiom(implies(rf_(i, j),
					 is(i, Kind::W) && is(j, Kind::R) && sameLoc(i, j)));
			for (auto k = i + 1; k < n; k++)
				if (k != j)
					addAxiom(!(rf_(i, j) && rf_(k, j)));

			/* mo: a strict total order on the writes of each location */
			addAxiom(implies(mo_(i, j),
					 is(i, Kind::W) && is(j, Kind::W) && sameLoc(i, j)));
			addAxiom(!(mo_(i, j) && mo_(j, i)));
			if (i < j)
				addAxiom(implies(is(i, Kind::W) && is(j, Kind::W) && sameLoc(i, j),
						 mo_(i, j) || mo_(j, i)));
			for (auto k = 0U; k < n; k++)
				if (k != i && k != j)
					addAxiom(implies(mo_(i, j) && mo_(j, k), mo_(i, k)));

			/* GenMC only builds graphs that are coherent within a thread:
			 * rf, mo, and fr never go backwards in po */
			if (j < i) {
				addAxiom(implies(rf_(i, j), !sameThread(i, j)));
				addAxiom(implies(mo_(i, j), !sameThread(i, j)));
				addAxiom(implies(relation(RB::fr)->operator()(i, j),
						 !sameThread(i, j)));
			}

			/* Dependencies go forward in po, out of dependable events */
			for (const auto *dep : {&ctrl_, &addr_, &data_, &pctrl_})
				addAxiom(
					implies((*dep)(i, j), sameThread(i, j) && isDependable(i)));

			/* Thread creation and join cross threads; lin goes from ends to begins */
			addAxiom(implies(tc_(i, j),
					 is(i, Kind::TC) && is(j, Kind::TB) && !sameThread(i, j)));
			addAxiom(implies(tj_(i, j),
					 is(i, Kind::TE) && is(j, Kind::TJ) && !sameThread(i, j)));
			addAxiom(implies(lin_(i, j),
					 is(i, Kind::MethodEnd) && is(j, Kind::MethodBegin)));
		}
	}
}

auto Graph::incidentals() const -> std::vector<z3::expr>
{
	std::vector<z3::expr> result;
	auto add = [&](const Term &t) {
		if (!t.isTrue() && !t.isFalse())
			result.push_back(t.expr());
	};
	for (auto e = 0U; e < n_; e++)
		for (const auto *flags :
		     {&excl_, &durable_, &recovery_, &abstractLock_, &dependableOther_})
			add((*flags)[e]);
	for (const auto *rel : {&ctrl_, &addr_, &data_, &pctrl_, &tc_, &tj_, &lin_})
		for (auto i = 0U; i < n_; i++)
			for (auto j = 0U; j < n_; j++)
				add((*rel)(i, j));
	return result;
}

auto Graph::is(unsigned e, Kind k) const -> Term { return kind_[e][static_cast<unsigned>(k)]; }

auto Graph::hasOrder(unsigned e, Order o) const -> Term
{
	return order_[e][static_cast<unsigned>(o)];
}

auto Graph::isExclusive(unsigned e) const -> Term { return excl_[e]; }

auto Graph::isLocated(unsigned e) const -> Term { return is(e, Kind::R) || is(e, Kind::W); }

auto Graph::hasLocation(unsigned e) const -> Term
{
	return isLocated(e) || is(e, Kind::Alloc) || is(e, Kind::Free) || is(e, Kind::HpRetire) ||
	       is(e, Kind::HpProtect);
}

auto Graph::isDependable(unsigned e) const -> Term
{
	return is(e, Kind::R) || is(e, Kind::Alloc) || dependableOther_[e];
}

auto Graph::predicate(Predicate::BuiltinID p, unsigned e) -> std::optional<Term>
{
	auto atLeastAcq = hasOrder(e, Order::ACQ) || hasOrder(e, Order::ACQ_REL) ||
			  hasOrder(e, Order::SC);
	auto atLeastRel = hasOrder(e, Order::REL) || hasOrder(e, Order::ACQ_REL) ||
			  hasOrder(e, Order::SC);
	switch (p) {
	case PB::NA:
		return hasOrder(e, Order::NA);
	case PB::ATOM:
		return !hasOrder(e, Order::NA);
	case PB::RLX:
		return hasOrder(e, Order::RLX);
	case PB::ACQ:
		return atLeastAcq;
	case PB::REL:
		return atLeastRel;
	case PB::SC:
		return hasOrder(e, Order::SC);
	case PB::W:
		return is(e, Kind::W);
	case PB::R:
		return is(e, Kind::R);
	case PB::EXCL:
		return isExclusive(e);
	case PB::NEXCL:
		return !isExclusive(e);
	case PB::F:
		return is(e, Kind::F);
	case PB::TC:
		return is(e, Kind::TC);
	case PB::TJ:
		return is(e, Kind::TJ);
	case PB::TB:
		return is(e, Kind::TB);
	case PB::TE:
		return is(e, Kind::TE);
	case PB::TK:
		return is(e, Kind::TK);
	case PB::ALLOC:
		return is(e, Kind::Alloc);
	case PB::FREE:
		return is(e, Kind::Free);
	case PB::HPRET:
		return is(e, Kind::HpRetire);
	case PB::PROT:
		return is(e, Kind::HpProtect);
	case PB::HPPROT:
		buildHeap();
		return isLocated(e) && heap_[e] && hpProtected_[e];
	case PB::NOTHPPROT:
		buildPositional();
		return (*notHpProtected_)[e];
	case PB::PLK:
		return abstractLock_[e];
	case PB::NPLK:
		return !abstractLock_[e];
	case PB::MB:
		return is(e, Kind::MethodBegin);
	case PB::ME:
		return is(e, Kind::MethodEnd);
	case PB::HEAP:
		buildHeap();
		return isLocated(e) && heap_[e];
	case PB::REC:
		return recovery_[e];
	case PB::D:
		return durable_[e];
	case PB::DEP:
		return isDependable(e);
	case PB::LOC:
		return hasLocation(e);
	case PB::LK:
	case PB::UL:
		return std::nullopt;
	}
	return std::nullopt;
}

auto Graph::relation(Relation::BuiltinID r) -> const Matrix *
{
	if (r == RB::alloc || r == RB::free || r == RB::retire)
		buildPositional();
	auto it = builtins_.find(r);
	return it == builtins_.end() ? nullptr : &it->second;
}

auto Graph::userPredicate(const Predicate &p, unsigned e) -> Term
{
	auto it = userPredicates_.find(p.getID());
	if (it == userPredicates_.end()) {
		auto base = p;
		if (base.isComplement())
			base.complement();
		std::vector<Term> values;
		for (auto i = 0U; i < n_; i++)
			values.emplace_back(
				concrete_ && concreteUserPredicates_
					? Term::constant(ctx(), concreteUserPredicates_(base, i))
					: freshBool("upred" + std::to_string(-p.getID()) + "_" +
						    std::to_string(i)));
		it = userPredicates_.emplace(p.getID(), std::make_pair(base, std::move(values)))
			     .first;
	}
	return it->second.second[e];
}

auto Graph::userRelation(const Relation &r) -> const Matrix &
{
	auto it = userRelations_.find(r.getID());
	if (it == userRelations_.end()) {
		auto base = r;
		if (base.isInverse())
			base.invert();
		auto m = freshMatrix("urel" + std::to_string(-r.getID()),
				     [](unsigned /*i*/, unsigned /*j*/) { return true; });
		it = userRelations_.emplace(r.getID(), std::make_pair(base, std::move(m))).first;
	}
	return it->second.second;
}

void Graph::fixUserRelation(const Relation &r, Matrix m)
{
	auto base = r;
	if (base.isInverse())
		base.invert();
	userRelations_.insert_or_assign(base.getID(), std::make_pair(base, std::move(m)));
}

auto Graph::threadOf(const z3::model &m, unsigned e) const -> unsigned
{
	auto t = 0U;
	for (auto i = 1U; i <= e; i++)
		if (m.eval(newThread_[i].expr(), true).is_true())
			t++;
	return t;
}

void Graph::print(std::ostream &os, const z3::model &m, const Theory &theory) const
{
	auto holds = [&](const Term &t) { return m.eval(t.expr(), true).is_true(); };
	auto locName = [&](unsigned e) {
		auto l = m.eval(loc_[e], true).get_numeral_int();
		return std::string(1, static_cast<char>('x' + (l % 3))) +
		       (l >= 3 ? std::to_string(l / 3) : "");
	};

	for (auto e = 0U; e < n_; e++) {
		os << "    e" << e << ": T" << threadOf(m, e) << " ";
		for (auto k = 0U; k < numKinds; k++)
			if (holds(kind_[e][k]))
				os << kindName(static_cast<Kind>(k));
		if (holds(hasLocation(e)))
			os << "(" << locName(e) << ")";
		for (auto o = 0U; o < numOrders; o++)
			if (holds(order_[e][o]))
				os << " " << orderName(static_cast<Order>(o));
		if (holds(is(e, Kind::HpProtect)))
			os << " hp:" << m.eval(hp_[e], true).get_numeral_int();
		if (holds(excl_[e]))
			os << " excl";
		if (holds(durable_[e]))
			os << " durable";
		if (holds(recovery_[e]))
			os << " recovery";
		if (holds(abstractLock_[e]))
			os << " abstract-lock";
		if (holds(isLocated(e) && heap_[e] && hpProtected_[e]))
			os << " hp-protected";
		if (holds(isDependable(e)) && !holds(is(e, Kind::R)) && !holds(is(e, Kind::Alloc)))
			os << " dependable";
		for (const auto &[id, pv] : userPredicates_)
			if (holds(pv.second[e]))
				os << " " << nameOf(pv.first, &theory);
		os << "\n";
	}

	auto printEdges = [&](const std::string &name, const Matrix &rel) {
		std::string edges;
		for (auto i = 0U; i < n_; i++)
			for (auto j = 0U; j < n_; j++)
				if (holds(rel(i, j)))
					edges += " e" + std::to_string(i) + "->e" +
						 std::to_string(j);
		if (!edges.empty())
			os << "    " << name << ":" << edges << "\n";
	};

	/* rf, with the reads of the initial value */
	printEdges("rf", rf_);
	std::string inits;
	for (auto r = 0U; r < n_; r++) {
		if (!holds(is(r, Kind::R)))
			continue;
		auto hasSource = false;
		for (auto w = 0U; w < n_; w++)
			hasSource |= holds(rf_(w, r));
		if (!hasSource)
			inits += " e" + std::to_string(r);
	}
	if (!inits.empty())
		os << "    reads-init:" << inits << "\n";

	/* mo, as the chain of immediate successors */
	printEdges("mo-imm", builtins_.at(RB::mo_imm));
	printEdges("ctrl", ctrl_);
	printEdges("addr", addr_);
	printEdges("data", data_);
	printEdges("pctrl", pctrl_);
	printEdges("tc", tc_);
	printEdges("tj", tj_);
	printEdges("lin", lin_);
	for (const auto &[id, rm] : userRelations_)
		printEdges(nameOf(rm.first, &theory), rm.second);

	/* The order of GenMC's execution state, if the positional builtins read it */
	if (added_) {
		std::vector<std::pair<unsigned, unsigned>> rank; /* (events before, event) */
		for (auto e = 0U; e < n_; e++) {
			auto before = 0U;
			for (auto f = 0U; f < n_; f++)
				if (f != e && holds((*added_)(f, e)))
					before++;
			rank.emplace_back(before, e);
		}
		std::ranges::sort(rank);
		os << "    added:";
		for (const auto &[before, e] : rank)
			os << " e" << e;
		os << "\n";
	}
}

} // namespace oracle
