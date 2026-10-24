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

#ifndef KATER_ORACLE_MATRIX_HPP
#define KATER_ORACLE_MATRIX_HPP

#include <z3++.h>

#include <cassert>
#include <vector>

namespace oracle {

/*
 * A Boolean formula over the unknowns of a graph, folded as it is built.
 *
 * Over a fixed number of events most of a relation is constant (po never
 * goes backwards, rf never starts at a read, ...). Folding the constants
 * away keeps the formulae handed to the solver small.
 */
class Term {

public:
	Term(z3::expr e) : e_(std::move(e)), c_(classify(e_)) {}

	static auto constant(z3::context &ctx, bool value) -> Term { return {ctx.bool_val(value)}; }

	[[nodiscard]] auto isTrue() const -> bool { return c_ == Const::True; }
	[[nodiscard]] auto isFalse() const -> bool { return c_ == Const::False; }

	[[nodiscard]] auto expr() const -> const z3::expr & { return e_; }
	[[nodiscard]] auto ctx() const -> z3::context & { return e_.ctx(); }

	friend auto operator&&(const Term &a, const Term &b) -> Term
	{
		if (a.isFalse() || b.isTrue())
			return a;
		if (b.isFalse() || a.isTrue())
			return b;
		return {a.expr() && b.expr()};
	}

	friend auto operator||(const Term &a, const Term &b) -> Term
	{
		if (a.isTrue() || b.isFalse())
			return a;
		if (b.isTrue() || a.isFalse())
			return b;
		return {a.expr() || b.expr()};
	}

	friend auto operator!(const Term &a) -> Term
	{
		if (a.isTrue() || a.isFalse())
			return constant(a.ctx(), a.isFalse());
		return {!a.expr()};
	}

	/* a => b */
	friend auto implies(const Term &a, const Term &b) -> Term { return !a || b; }

private:
	enum class Const { Unknown, True, False };

	static auto classify(const z3::expr &e) -> Const
	{
		if (e.is_true())
			return Const::True;
		if (e.is_false())
			return Const::False;
		return Const::Unknown;
	}

	z3::expr e_;
	Const c_;
};

/* The disjunction of TERMS, skipping the ones known to be false */
auto anyOf(z3::context &ctx, const std::vector<Term> &terms) -> Term;

/* The conjunction of TERMS, skipping the ones known to be true */
auto allOf(z3::context &ctx, const std::vector<Term> &terms) -> Term;

/*
 * A binary relation over the events 0..n-1 of a graph: cell (i, j) holds
 * when the relation relates event i to event j.
 */
class Matrix {

public:
	Matrix(z3::context &ctx, unsigned n, bool value = false)
		: ctx_(&ctx), n_(n), cells_(static_cast<size_t>(n) * n, Term::constant(ctx, value))
	{
	}

	static auto identity(z3::context &ctx, unsigned n) -> Matrix;

	[[nodiscard]] auto size() const -> unsigned { return n_; }
	[[nodiscard]] auto ctx() const -> z3::context & { return *ctx_; }

	[[nodiscard]] auto operator()(unsigned i, unsigned j) const -> const Term &
	{
		assert(i < n_ && j < n_);
		return cells_[(static_cast<size_t>(i) * n_) + j];
	}

	void set(unsigned i, unsigned j, Term t)
	{
		assert(i < n_ && j < n_);
		cells_[(static_cast<size_t>(i) * n_) + j] = std::move(t);
	}

	/* this | other */
	[[nodiscard]] auto unite(const Matrix &other) const -> Matrix;
	/* this & other */
	[[nodiscard]] auto intersect(const Matrix &other) const -> Matrix;
	/* this \ other */
	[[nodiscard]] auto minus(const Matrix &other) const -> Matrix;
	/* this ; other */
	[[nodiscard]] auto compose(const Matrix &other) const -> Matrix;
	/* this^-1 */
	[[nodiscard]] auto transpose() const -> Matrix;
	/* this+ */
	[[nodiscard]] auto plus() const -> Matrix;
	/* this* */
	[[nodiscard]] auto star() const -> Matrix;
	/* this? */
	[[nodiscard]] auto optional() const -> Matrix;

	/* Whether some event is related to itself */
	[[nodiscard]] auto anyReflexive() const -> Term;

	/* Whether the relation relates no events at all */
	[[nodiscard]] auto isEmpty() const -> Term;

	/* Whether every pair of this is a pair of OTHER */
	[[nodiscard]] auto includedIn(const Matrix &other) const -> Term;

	/* Whether some pair is in exactly one of this and OTHER */
	[[nodiscard]] auto differsFrom(const Matrix &other) const -> Term;

private:
	z3::context *ctx_;
	unsigned n_;
	std::vector<Term> cells_;
};

} // namespace oracle

#endif /* KATER_ORACLE_MATRIX_HPP */
