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

#ifndef KATER_ORACLE_GENMC_HPP
#define KATER_ORACLE_GENMC_HPP

#include "Enumerate.hpp"

#include <string>
#include <vector>

namespace oracle {

struct GenMCOptions {
	/* kater-oracle-runner, which runs the checkers Kater exported */
	std::string runner;

	/* Every graph within these bounds, and every one with a heap (for the
	 * memory-error checks) within the second ... */
	Bounds bounds{.events = 4, .threads = 3, .locations = 2};
	Bounds heapBounds{.events = 4, .threads = 3, .locations = 2};

	/* ... and this many random ones within those */
	unsigned random = 0;
	Bounds randomBounds{.events = 8, .threads = 4, .locations = 3};
	unsigned seed = 1;

	/* Graph files to check instead (in the form Execution::print renders) */
	std::vector<std::string> graphs;

	/* At most this many graphs (0: no limit) */
	unsigned limit = 0;

	/* Disagreements shown in full, for each kind of check */
	unsigned shown = 3;

	/* Only count the graphs */
	bool count = false;

	/* Of the graphs enumerated, check only the SHARD-th of every SHARDS */
	unsigned shard = 0;
	unsigned shards = 1;

	bool verbose = false;
};

/*
 * Runs the GenMC consistency checker Kater exports for the model in FILE
 * (a kat/NAME-genmc.kat) on small graphs, and compares its verdicts with
 * the model's meaning in the reference semantics: isConsistent() on whole
 * graphs and incrementally, the views and prefixes every event saves, the
 * rf and co choices coherence leaves for a new read or write, and the
 * memory-error checks (checkErrors(), checkWarnings(), clause by clause)
 * of every event GenMC checks. Prints every disagreement with its graph;
 * returns whether there were none.
 */
auto checkGenMC(const std::string &file, const GenMCOptions &opts) -> bool;

} // namespace oracle

#endif /* KATER_ORACLE_GENMC_HPP */
