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

#ifndef KATER_ORACLE_SEMANTICS_HPP
#define KATER_ORACLE_SEMANTICS_HPP

#include "Graph.hpp"
#include "Matrix.hpp"

#include "Constraint.hpp"
#include "KatModule.hpp"
#include "NFA.hpp"
#include "RegExp.hpp"

#include <deque>
#include <stdexcept>
#include <unordered_map>

namespace oracle {

/* Raised for constructs the reference semantics does not cover */
class Unsupported : public std::runtime_error {
public:
	using std::runtime_error::runtime_error;
};

/* Whether R is a positional builtin that GenMC's hb defines (last_*, unprotected) */
auto isHbPositional(Relation::BuiltinID r) -> bool;

/* That builtin's meaning in G, with HB as GenMC's hb */
auto hbPositional(Graph &g, Relation::BuiltinID r, const Matrix &hb) -> Matrix;

/*
 * The reference semantics of .kat: what an expression, a constraint or an
 * automaton means on a graph, defined by structural recursion over Kater's
 * syntax and nothing else. In particular, none of Kater's own inference
 * (Theory, saturation, automata) is consulted: the module's theory is only
 * used to find names, the per-location variants of user relations, and
 * the user's disjointness declarations.
 */
class Semantics {

public:
	Semantics(Graph &g, const KatModule &module);

	/* The relation RE denotes */
	auto eval(const RegExp &re) -> Matrix;

	/* The same, evaluated once for all the expressions equal to RE (a
	 * model's clauses repeat its views): not inside a recursive definition */
	auto evalShared(const RegExp &re) -> const Matrix &;
	auto eval(const TransLabel &lab) -> Matrix;
	auto eval(const Relation &r) -> Matrix;

	/* Whether predicate P (or every predicate of PS) holds at event E */
	auto eval(const Predicate &p, unsigned e) -> Term;
	auto eval(const PredicateSet &ps, unsigned e) -> Term;

	/*
	 * The relation an automaton denotes: the pairs (a, b) such that some
	 * accepting path reads a, ..., b. Built as the least fixpoint of
	 * "reach" over (state, event) pairs, with fixed start event.
	 */
	auto eval(const NFA &nfa) -> Matrix;

	/* Whether constraint C holds in the graph */
	auto holds(const Constraint &c) -> Term;

	/* The axioms of the module's user declarations (disjoint predicates) */
	auto declarationAxioms(const VSet<VSet<Predicate::ID>> &disjointSets) -> Term;

	/* GenMC's hb: the view the module names hb, which GenMC's driver records
	 * the accesses of its execution state with (getHbView()) */
	auto genmcHb() -> const Matrix &;

private:
	auto evalMutRec(const MutRecRE &re) -> Matrix;
	auto holdsSubset(const SubsetConstraint &c) -> Term;

	/* The positional builtins that GenMC's hb defines (last_*, unprotected);
	 * nullopt for the others */
	auto positional(Relation::BuiltinID r) -> std::optional<Matrix>;

	Graph *g_;
	const Theory *theory_;

	/* The module's view hb, and GenMC's hb and positional builtins once evaluated */
	const RegExp *hbView_ = nullptr;
	std::optional<Matrix> hb_;
	std::unordered_map<int, Matrix> positional_;

	/* The expressions evalShared() evaluated (where they stay) */
	std::deque<std::pair<const RegExp *, Matrix>> shared_;

	/* Objects for the module's symbols, by ID */
	std::unordered_map<Predicate::ID, Predicate> predicates_;
	std::unordered_map<Relation::ID, Relation> relations_;

	/* The relation each per-location variant restricts */
	std::unordered_map<Relation::ID, Relation> perLocBase_;

	/* The current approximations of the recursive relations being defined */
	std::unordered_map<Relation::ID, Matrix> rec_;
};

} // namespace oracle

#endif /* KATER_ORACLE_SEMANTICS_HPP */
