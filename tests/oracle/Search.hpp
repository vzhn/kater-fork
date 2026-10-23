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
#include <string>

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

struct SearchOptions {
	unsigned minEvents = 1;
	unsigned maxEvents = 5;
	unsigned timeoutMs = 60000;
};

/*
 * Looks for a graph, from the smallest up, that GenMC can build, satisfies
 * HYPOTHESES, and satisfies VIOLATION; the counterexample is rendered with
 * MODULE's names.
 */
auto search(const KatModule &module, const Query &hypotheses, const Query &violation,
	    const SearchOptions &opts) -> Search;

} // namespace oracle

#endif /* KATER_ORACLE_SEARCH_HPP */
