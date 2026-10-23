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

#ifndef KATER_ORACLE_TRANSFORMS_HPP
#define KATER_ORACLE_TRANSFORMS_HPP

#include "Search.hpp"

#include <string>

namespace oracle {

struct TransformOptions {
	SearchOptions search;
	unsigned cases = 100;
	unsigned seed = 1;
	unsigned depth = 3;
	std::string only; /* test only the transformation of this name */
	bool verbose = false;
};

/*
 * Tests each automaton transformation of the decision procedure against
 * its semantic contract, on the automata of random expressions: toNFA and
 * the normalization passes must preserve the relation an automaton
 * denotes; the left-hand-side saturations of "& id" must keep every
 * cycle; the rotation of a right-hand side must not create a cycle.
 * Prints each violation with both automata and a graph that tells them
 * apart; returns whether there was none.
 */
auto testTransforms(const TransformOptions &opts) -> bool;

} // namespace oracle

#endif /* KATER_ORACLE_TRANSFORMS_HPP */
