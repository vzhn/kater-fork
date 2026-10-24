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

#include "Matrix.hpp"

namespace oracle {

/* The disjunction (OR) or conjunction of TERMS: ABSORBING decides it, and
 * terms that are the other constant drop out */
static auto foldAll(z3::context &ctx, const std::vector<Term> &terms, bool absorbing) -> Term
{
	const Term *single = nullptr;
	auto unknowns = 0U;
	for (const auto &t : terms) {
		if (absorbing ? t.isTrue() : t.isFalse())
			return t;
		if (!t.isTrue() && !t.isFalse()) {
			unknowns++;
			single = &t;
		}
	}
	if (unknowns == 0)
		return Term::constant(ctx, !absorbing);
	if (unknowns == 1)
		return *single;
	z3::expr_vector unknown(ctx);
	for (const auto &t : terms)
		if (!t.isTrue() && !t.isFalse())
			unknown.push_back(t.expr());
	return {absorbing ? z3::mk_or(unknown) : z3::mk_and(unknown)};
}

auto anyOf(z3::context &ctx, const std::vector<Term> &terms) -> Term
{
	return foldAll(ctx, terms, true);
}

auto allOf(z3::context &ctx, const std::vector<Term> &terms) -> Term
{
	return foldAll(ctx, terms, false);
}

auto Matrix::identity(z3::context &ctx, unsigned n) -> Matrix
{
	Matrix id(ctx, n);
	for (auto i = 0U; i < n; i++)
		id.set(i, i, Term::constant(ctx, true));
	return id;
}

auto Matrix::unite(const Matrix &other) const -> Matrix
{
	assert(size() == other.size());
	Matrix result(*this);
	for (auto i = 0U; i < n_; i++)
		for (auto j = 0U; j < n_; j++)
			result.set(i, j, (*this)(i, j) || other(i, j));
	return result;
}

auto Matrix::intersect(const Matrix &other) const -> Matrix
{
	assert(size() == other.size());
	Matrix result(*this);
	for (auto i = 0U; i < n_; i++)
		for (auto j = 0U; j < n_; j++)
			result.set(i, j, (*this)(i, j) && other(i, j));
	return result;
}

auto Matrix::minus(const Matrix &other) const -> Matrix
{
	assert(size() == other.size());
	Matrix result(*this);
	for (auto i = 0U; i < n_; i++)
		for (auto j = 0U; j < n_; j++)
			result.set(i, j, (*this)(i, j) && !other(i, j));
	return result;
}

auto Matrix::compose(const Matrix &other) const -> Matrix
{
	assert(size() == other.size());
	auto &c = ctx();
	Matrix result(c, n_);
	std::vector<Term> paths;
	for (auto i = 0U; i < n_; i++) {
		for (auto j = 0U; j < n_; j++) {
			paths.clear();
			for (auto k = 0U; k < n_; k++)
				paths.push_back((*this)(i, k) && other(k, j));
			result.set(i, j, anyOf(c, paths));
		}
	}
	return result;
}

auto Matrix::transpose() const -> Matrix
{
	Matrix result(*this);
	for (auto i = 0U; i < n_; i++)
		for (auto j = 0U; j < n_; j++)
			result.set(i, j, (*this)(j, i));
	return result;
}

auto Matrix::plus() const -> Matrix
{
	/* Warshall: after round K, (i, j) holds iff a path from i to j exists
	 * whose intermediate events are all below K */
	Matrix result(*this);
	for (auto k = 0U; k < n_; k++)
		for (auto i = 0U; i < n_; i++)
			for (auto j = 0U; j < n_; j++)
				result.set(i, j, result(i, j) || (result(i, k) && result(k, j)));
	return result;
}

auto Matrix::star() const -> Matrix { return plus().unite(identity(ctx(), n_)); }

auto Matrix::optional() const -> Matrix { return unite(identity(ctx(), n_)); }

auto Matrix::anyReflexive() const -> Term
{
	std::vector<Term> diag;
	for (auto i = 0U; i < n_; i++)
		diag.push_back((*this)(i, i));
	return anyOf(ctx(), diag);
}

auto Matrix::isEmpty() const -> Term
{
	std::vector<Term> none;
	for (auto i = 0U; i < n_; i++)
		for (auto j = 0U; j < n_; j++)
			none.push_back(!(*this)(i, j));
	return allOf(ctx(), none);
}

auto Matrix::includedIn(const Matrix &other) const -> Term
{
	assert(size() == other.size());
	std::vector<Term> each;
	for (auto i = 0U; i < n_; i++)
		for (auto j = 0U; j < n_; j++)
			each.push_back(implies((*this)(i, j), other(i, j)));
	return allOf(ctx(), each);
}

auto Matrix::differsFrom(const Matrix &other) const -> Term
{
	assert(size() == other.size());
	std::vector<Term> cells;
	for (auto i = 0U; i < n_; i++)
		for (auto j = 0U; j < n_; j++)
			cells.push_back(((*this)(i, j) && !other(i, j)) ||
					(!(*this)(i, j) && other(i, j)));
	return anyOf(ctx(), cells);
}

} // namespace oracle
