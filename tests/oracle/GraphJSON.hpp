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

#ifndef KATER_ORACLE_GRAPH_JSON_HPP
#define KATER_ORACLE_GRAPH_JSON_HPP

#include "Enumerate.hpp"

#include <filesystem>
#include <string>
#include <vector>

namespace oracle {

struct GraphJSONOptions {
	/* Every graph within these bounds, of every kind of event; every one
	 * with a heap within the second */
	Bounds bounds{.events = 3, .threads = 3, .locations = 2};
	Bounds heapBounds{.events = 3, .threads = 3, .locations = 2};

	/* This many random graphs within these bounds, with thread events and
	 * method calls */
	unsigned random = 0;
	Bounds randomBounds{.events = 6, .threads = 3, .locations = 2};

	/* This many models of the symbolic graph's axioms, up to this many events */
	unsigned symbolic = 0;
	unsigned symbolicEvents = 4;

	unsigned seed = 1;

	/* Graph files (in the form Execution::print renders) */
	std::vector<std::string> graphs;

	bool verbose = false;
};

/*
 * Writes to OUT, as JSON lines, the graphs OPTS asks for, each with the
 * oracle's meaning of every builtin relation and predicate on it, and the
 * axioms of the oracle it violates: the input of kater-model-check in
 * formal/, which compares them with the model's. Returns whether every
 * graph was written.
 */
auto writeGraphs(const std::filesystem::path &out, const GraphJSONOptions &opts) -> bool;

} // namespace oracle

#endif /* KATER_ORACLE_GRAPH_JSON_HPP */
