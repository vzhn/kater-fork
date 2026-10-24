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

#ifndef KATER_ORACLE_EXTENSIBLE_HPP
#define KATER_ORACLE_EXTENSIBLE_HPP

#include "Enumerate.hpp"

#include <string>
#include <vector>

namespace oracle {

struct ExtensibleOptions {
	/* Every graph within these bounds ... */
	Bounds bounds{.events = 3, .threads = 3, .locations = 2};

	/* ... or the graphs of these files (in the form Execution::print renders) */
	std::vector<std::string> graphs;

	/* The model is expected not to be extensible: a counterexample is the
	 * answer, and none an error */
	bool refutable = false;

	/* Decide by what Kater's extensibility check proves too: an event that
	 * nothing po-after it accesses the location of can be added maximally */
	bool maximal = false;

	/* Counterexamples shown in full */
	unsigned shown = 3;

	bool verbose = false;
};

/*
 * Checks that the model of FILE (a kat/NAME-genmc.kat) is extensible, as
 * GenMC's exploration needs: an event GenMC may add to a consistent graph
 * can be added so that the graph stays consistent. GenMC adds an event
 * once everything before it in its prefix relation, pporf = (ppo | rfe |
 * tc | tj | lin)+, is in the graph; under the models that track
 * dependencies, it may have po-successors there already (it fills a hole
 * a revisit left). So: for every graph G GenMC can build, and every event
 * e of G that nothing follows in pporf and nothing reads from, that is not
 * part of an RMW and not a thread start, if G without e is consistent,
 * then G is, for some choice of where e reads from (a read) or of its
 * place in mo (a write). Consistent means every acyclicity and inclusion
 * export holds, and the view of `export coherence` is irreflexive with eco.
 *
 * Also counts, among these events, those that nothing po-after them
 * accesses the location of and that are not consistent added maximally (a
 * read reading the last write in mo, a write last in mo), which Kater's
 * extensibility check claims there are none of. With MAXIMAL, these
 * decide the verdict too.
 *
 * Prints each counterexample (shown in full up to a number), and returns
 * whether there was none (with REFUTABLE, whether there was one).
 */
auto checkExtensible(const std::string &file, const ExtensibleOptions &opts) -> bool;

} // namespace oracle

#endif /* KATER_ORACLE_EXTENSIBLE_HPP */
