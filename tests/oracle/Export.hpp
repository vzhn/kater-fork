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

#ifndef KATER_ORACLE_EXPORT_HPP
#define KATER_ORACLE_EXPORT_HPP

#include "Search.hpp"

#include <filesystem>
#include <optional>
#include <string>

namespace oracle {

/*
 * Validates the export of FILE as GenMC code, short of the printing:
 *  - every claim the Checker proves on the way (the export requirements,
 *    the closure checks of incremental views) has no counterexample;
 *  - the inclusion the extensibility check of each acyclicity export
 *    (Checker::isPPOIntersectionInPPO) decides between automata of its
 *    own, taken from its certificate, has no counterexample either; each
 *    whose left automaton accepts nothing is reported as vacuous;
 *  - every certificate of these claims checks, and the letter inclusions
 *    they rest on hold;
 *  - every definition, view and export constraint the exporter rewrites
 *    (po into po-imm+, transitive views into recursive ones, ...) means
 *    the same as before.
 * Returns whether all of it holds up to the search bound. With JSONDIR,
 * also writes the certificates, as certifyFile does.
 */
auto validateExport(const std::string &file, const SearchOptions &opts, bool verbose,
		    const std::optional<std::filesystem::path> &jsonDir = std::nullopt) -> bool;

} // namespace oracle

#endif /* KATER_ORACLE_EXPORT_HPP */
