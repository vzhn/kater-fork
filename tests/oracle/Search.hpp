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

#ifndef KATER_ORACLE_SEARCH_HPP
#define KATER_ORACLE_SEARCH_HPP

#include "Graph.hpp"
#include "Semantics.hpp"

#include <functional>
#include <memory>
#include <string>
#include <vector>

namespace oracle {

/* The outcome of a bounded search for a counterexample */
struct Search {
	enum class Outcome {
		NoCounterexample, /* none with up to `events` events */
		Counterexample,	  /* `detail` is one with `events` events */
		Unsupported,	  /* `detail` names the construct */
		Unknown,	  /* the solver gave up at `events` events */
	};

	Outcome outcome;
	unsigned events;
	std::string detail;
};

/* A formula over a graph and the semantics of the module on it */
using Query = std::function<Term(Graph &, Semantics &)>;

/*
 * The hypotheses of a module: its user assumptions and disjointness
 * declarations. Kater folds some assumptions into its theory, and drops
 * them, before it checks anything, so they have to be taken before that.
 * The built-in assumptions are not hypotheses but claims about GenMC,
 * which `audit` checks.
 */
struct Hypotheses {
	std::vector<std::unique_ptr<Constraint>> assumptions;
	VSet<VSet<Predicate::ID>> disjoint;

	/* That they all hold in the graph */
	auto operator()(Graph &g, Semantics &sem) const -> Term;
};

auto takeHypotheses(const KatModule &module) -> Hypotheses;

struct SearchOptions {
	unsigned minEvents = 1;
	unsigned maxEvents = 5;
	unsigned timeoutMs = 60000;
	/* --allow-unchecked: the claims, by a part of their text, that may go
	 * unchecked (the solver gives up, or the oracle cannot express them)
	 * without failing the command (#83) */
	std::vector<std::string> allowUnchecked;
};

/* Whether the claim WHAT may go unchecked */
inline auto uncheckedAllowed(const SearchOptions &opts, const std::string &what) -> bool
{
	for (const auto &part : opts.allowUnchecked)
		if (what.find(part) != std::string::npos)
			return true;
	return false;
}

/*
 * Looks for a graph, from the smallest up, that GenMC can build, satisfies
 * HYPOTHESES, and satisfies VIOLATION; the counterexample is rendered with
 * MODULE's names.
 */
auto search(const KatModule &module, const Query &hypotheses, const Query &violation,
	    const SearchOptions &opts) -> Search;

} // namespace oracle

#endif /* KATER_ORACLE_SEARCH_HPP */
