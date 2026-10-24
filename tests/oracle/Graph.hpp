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

#include "Execution.hpp"
#include "Matrix.hpp"

#include "Predicate.hpp"
#include "Relation.hpp"

#include <z3++.h>

#include <functional>
#include <map>
#include <optional>
#include <ostream>
#include <string>
#include <vector>

class Theory;

namespace oracle {

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
 *
 * A location an allocation is of is a heap block; frees, retires and
 * hazard-pointer protections are of one. GenMC's driver keeps what its
 * memory-error checks read (the last accesses of each location, frees,
 * protections) in an execution state, which holds the events in the order
 * they entered it: the positional builtins (alloc, free, last_na_reads,
 * ...) are relative to that order, which an event that GenMC checks sees
 * the events before (GenMCDriver::checkForRaces).
 *
 * A graph can also be concrete (an Execution): its unknowns are then
 * constants, and so is every formula built over it, the axioms included.
 */
class Graph {

public:
	/* The meaning of a user predicate at an event of a concrete graph */
	using UserPredicates = std::function<bool(const Predicate &, unsigned)>;

	Graph(z3::context &ctx, unsigned n);
	/* ORDER is the order the events entered GenMC's execution state; by
	 * default, the order kater-oracle-runner adds them in */
	Graph(z3::context &ctx, const Execution &x, UserPredicates userPredicates = {},
	      std::optional<std::vector<unsigned>> order = std::nullopt);

	[[nodiscard]] auto size() const -> unsigned { return n_; }
	[[nodiscard]] auto ctx() const -> z3::context & { return *ctx_; }

	/* Event attributes */
	[[nodiscard]] auto is(unsigned e, Kind k) const -> Term;
	[[nodiscard]] auto hasOrder(unsigned e, Order o) const -> Term;
	[[nodiscard]] auto isExclusive(unsigned e) const -> Term;
	[[nodiscard]] auto isLocated(unsigned e) const -> Term;
	[[nodiscard]] auto hasLocation(unsigned e) const -> Term;
	[[nodiscard]] auto isDependable(unsigned e) const -> Term;
	[[nodiscard]] auto sameThread(unsigned a, unsigned b) const -> Term
	{
		return sameThread_(a, b);
	}
	[[nodiscard]] auto sameLoc(unsigned a, unsigned b) const -> Term { return sameLoc_(a, b); }

	/* Whether A and B have the same location (accesses, allocations, frees,
	 * retires, protections) */
	[[nodiscard]] auto sameBlock(unsigned a, unsigned b) const -> Term
	{
		return sameBlock_(a, b);
	}

	/* Whether event A entered GenMC's execution state before event B */
	auto addedBefore(unsigned a, unsigned b) -> Term;

	/* Whether access X was hazard-pointer protected when it entered the state */
	auto protectedWhenAdded(unsigned x) -> Term;

	/* The meaning of builtin predicate P at event E; nullopt if the model has none */
	auto predicate(Predicate::BuiltinID p, unsigned e) -> std::optional<Term>;

	/* The meaning of builtin relation R; nullptr if the model has none (or
	 * GenMC's hb defines it: Semantics gives the last_* and unprotected) */
	auto relation(Relation::BuiltinID r) -> const Matrix *;

	/* GenMC's hb for a module that names none: a strict order between po
	 * and porf; nullopt for a concrete graph */
	auto genmcHb() -> std::optional<Matrix>;

	/* The relation "same location", as a matrix */
	[[nodiscard]] auto sameLocRelation() const -> const Matrix & { return sameLoc_; }

	/* Uninterpreted symbols, created on first use. In a concrete graph, user
	 * predicates mean what its UserPredicates say, and a user relation is
	 * what fixUserRelation() set */
	auto userPredicate(const Predicate &p, unsigned e) -> Term;
	auto userRelation(const Relation &r) -> const Matrix &;

	/* Gives user relation R the meaning M */
	void fixUserRelation(const Relation &r, Matrix m);

	/* What every graph GenMC builds satisfies; for a concrete graph, the
	 * axioms it violates (all of them false) */
	[[nodiscard]] auto axioms() const -> const z3::expr_vector & { return axioms_; }
	[[nodiscard]] auto isConcrete() const -> bool { return concrete_; }

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
	void buildStructure(const Execution &x);
	void buildDerived();
	void buildAxioms();

	/* Built on first use, with their axioms: that allocations precede
	 * the events of their block in porf, the order of the execution state,
	 * and what the positional builtins read from it */
	void buildHeap();
	void buildOrder();
	void buildPositional();
	[[nodiscard]] auto memLabel(unsigned e) const -> Term;

	[[nodiscard]] auto threadOf(const z3::model &m, unsigned e) const -> unsigned;

	z3::context *ctx_;
	unsigned n_;
	bool concrete_ = false;
	UserPredicates concreteUserPredicates_;
	std::vector<unsigned> concreteOrder_;

	/* Unknowns */
	std::vector<Term> newThread_; /* event e starts a new thread */
	std::vector<std::vector<Term>> kind_;
	std::vector<std::vector<Term>> order_;
	std::vector<Term> excl_;
	std::vector<z3::expr> loc_;
	std::vector<z3::expr> hp_; /* the hazard pointer of a protection */
	std::vector<Term> durable_, recovery_, abstractLock_, dependableOther_;
	Matrix rf_, mo_;
	Matrix ctrl_, addr_, data_, pctrl_, tc_, tj_, lin_;

	/* Derived structure */
	Matrix sameThread_, sameLoc_, sameBlock_, sameHp_;
	std::vector<Term> heap_;	/* on a location an allocation is of */
	std::vector<Term> hpProtected_; /* GenMC's isHazptrProtected() */
	std::map<Relation::BuiltinID, Matrix> builtins_;

	/* Built on first use */
	bool heapBuilt_ = false;
	std::optional<Matrix> causal_; /* (po | rf | tc | tj)+ */
	std::optional<Matrix> added_;  /* the order of the execution state */
	std::optional<std::vector<Term>> protectedWhenAdded_, notHpProtected_;
	std::optional<Matrix> genmcHb_;

	/* Uninterpreted user symbols */
	std::map<Relation::ID, std::pair<Relation, Matrix>> userRelations_;
	std::map<Predicate::ID, std::pair<Predicate, std::vector<Term>>> userPredicates_;

	z3::expr_vector axioms_;
};

} // namespace oracle

#endif /* KATER_ORACLE_GRAPH_HPP */
