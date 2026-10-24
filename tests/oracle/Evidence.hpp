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

#ifndef KATER_ORACLE_EVIDENCE_HPP
#define KATER_ORACLE_EVIDENCE_HPP

#include <filesystem>
#include <string>

namespace oracle {

/*
 * Has Kater prove the assertions of FILE, and writes to DIR, for each it
 * proves, everything the proof went through (Checker::setEvidenceSink): the
 * assertion's constraint, the module's declarations and assumptions, and for
 * each inclusion checkInclusion proved, its expressions, the automata between
 * its passes and the final check's certificate. The k-th assertion of FILE
 * goes to DIR/<stem>.a<k>.json, the input of the checker of whole proofs in
 * formal/ (kater-chain-check). Returns whether FILE parsed.
 */
auto writeEvidence(const std::string &file, const std::filesystem::path &dir, bool verbose) -> bool;

/*
 * Has Kater export FILE, and writes to DIR the evidence of every claim the
 * export rests on: of each subset or equality constraint the Checker proves
 * on the way (the export requirements, the closure checks of incremental
 * views), with the temporary assumptions it is proved under, to
 * DIR/<stem>.c<k>.json, in the format of the assertions'; and of each
 * extensibility check that passes (Checker::setExtensibilityEvidenceSink),
 * to DIR/<stem>.x<k>.json. Returns whether the export succeeded.
 */
auto writeExportEvidence(const std::string &file, const std::filesystem::path &dir, bool verbose)
	-> bool;

} // namespace oracle

#endif /* KATER_ORACLE_EVIDENCE_HPP */
