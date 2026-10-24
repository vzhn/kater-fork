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

#ifndef KATER_ORACLE_AUDIT_HPP
#define KATER_ORACLE_AUDIT_HPP

#include "Search.hpp"

namespace oracle {

/*
 * Checks every fact Kater's Theory states about the builtin relations and
 * predicates (inclusions, domains, disjointness, composability, the
 * built-in assumptions, per-location variants) against their meaning in
 * GenMC. Prints the false ones with a counterexample; returns whether all
 * of them hold.
 */
auto audit(const SearchOptions &opts, bool verbose) -> bool;

} // namespace oracle

#endif /* KATER_ORACLE_AUDIT_HPP */
