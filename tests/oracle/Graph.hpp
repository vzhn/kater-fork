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

#ifndef KATER_ORACLE_GRAPH_HPP
#define KATER_ORACLE_GRAPH_HPP

#include "Matrix.hpp"

#include "Predicate.hpp"
#include "Relation.hpp"

#include <z3++.h>

#include <cstdint>
#include <functional>
#include <map>
#include <optional>
#include <ostream>
#include <string>
#include <vector>

class Theory;

namespace oracle {

/* The kinds of GenMC event labels the model tells apart */
enum class Kind : std::uint8_t {
	R,
	W,
	F,
	TC, /* ThreadCreate */
	TB, /* ThreadStart */
	TJ, /* ThreadJoin */
	TE, /* ThreadFinish */
	TK, /* ThreadKill */
	Alloc,
	Free,
	HpRetire,
	HpProtect,
	MethodBegin,
	MethodEnd,
	Other, /* every other label: optionals, loop and spin markers, outputs, ... */
};
inline constexpr unsigned numKinds = 15;

/* GenMC's memory orderings (consume is never generated) */
enum class Order : std::uint8_t { NA, RLX, ACQ, REL, ACQ_REL, SC };
inline constexpr unsigned numOrders = 6;

/*
 * A symbolic execution graph of a fixed number of events: every attribute
 * of every event, and every edge of the base relations, is an unknown of
 * the solver. The builtin relations and predicates of Kater are given
 * their meaning in GenMC (genmc/Execution/{EventLabel,ExecutionGraph}.hpp),
 * independently of what Kater's Theory claims about them; the axioms
 * restrict the unknowns to the graphs GenMC can build.
 *
 * Events are numbered thread by thread, in program order: thread
 * boundaries are the only unknown of po. Initial writes are implicit: a
 * read without an incoming rf edge reads the initial value, and is then
 * fr-before every write to its location.
 */
class Graph {

public:
	Graph(z3::context &ctx, unsigned n);

	[[nodiscard]] auto size() const -> unsigned { return n_; }
	[[nodiscard]] auto ctx() const -> z3::context & { return *ctx_; }

	/* Event attributes */
	[[nodiscard]] auto is(unsigned e, Kind k) const -> Term;
	[[nodiscard]] auto hasOrder(unsigned e, Order o) const -> Term;
	[[nodiscard]] auto isExclusive(unsigned e) const -> Term;
	[[nodiscard]] auto isLocated(unsigned e) const -> Term;
	[[nodiscard]] auto isDependable(unsigned e) const -> Term;
	[[nodiscard]] auto sameThread(unsigned a, unsigned b) const -> Term
	{
		return sameThread_(a, b);
	}
	[[nodiscard]] auto sameLoc(unsigned a, unsigned b) const -> Term { return sameLoc_(a, b); }

	/* The meaning of builtin predicate P at event E; nullopt if the model has none */
	[[nodiscard]] auto predicate(Predicate::BuiltinID p, unsigned e) const
		-> std::optional<Term>;

	/* The meaning of builtin relation R; nullptr if the model has none */
	[[nodiscard]] auto relation(Relation::BuiltinID r) const -> const Matrix *;

	/* The relation "same location", as a matrix */
	[[nodiscard]] auto sameLocRelation() const -> const Matrix & { return sameLoc_; }

	/* Uninterpreted symbols, created on first use */
	auto userPredicate(const Predicate &p, unsigned e) -> Term;
	auto userRelation(const Relation &r) -> const Matrix &;

	/* What every graph GenMC builds satisfies */
	[[nodiscard]] auto axioms() const -> const z3::expr_vector & { return axioms_; }

	/* The unknowns a counterexample can usually do without (label flags,
	 * dependencies, ...): turning them off makes it easier to read */
	[[nodiscard]] auto incidentals() const -> std::vector<z3::expr>;

	/* Renders the graph M assigns, naming user symbols via THEORY */
	void print(std::ostream &os, const z3::model &m, const Theory &theory) const;

private:
	auto freshBool(const std::string &name) -> z3::expr;
	auto freshMatrix(const std::string &name,
			 const std::function<bool(unsigned, unsigned)> &allowed) -> Matrix;

	void addAxiom(const Term &t);
	void buildStructure();
	void buildDerived();
	void buildAxioms();

	[[nodiscard]] auto threadOf(const z3::model &m, unsigned e) const -> unsigned;

	z3::context *ctx_;
	unsigned n_;

	/* Unknowns */
	std::vector<Term> newThread_; /* event e starts a new thread */
	std::vector<std::vector<Term>> kind_;
	std::vector<std::vector<Term>> order_;
	std::vector<Term> excl_;
	std::vector<z3::expr> loc_;
	std::vector<Term> heap_, durable_, recovery_, abstractLock_, hpProtected_, notHpProtected_,
		dependableOther_;
	Matrix rf_, mo_;
	Matrix ctrl_, addr_, data_, pctrl_, tc_, tj_, lin_;

	/* Derived structure */
	Matrix sameThread_, sameLoc_;
	std::map<Relation::BuiltinID, Matrix> builtins_;

	/* Uninterpreted user symbols */
	std::map<Relation::ID, std::pair<Relation, Matrix>> userRelations_;
	std::map<Predicate::ID, std::pair<Predicate, std::vector<Term>>> userPredicates_;

	z3::expr_vector axioms_;
};

} // namespace oracle

#endif /* KATER_ORACLE_GRAPH_HPP */
