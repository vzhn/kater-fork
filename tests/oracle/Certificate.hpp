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

#ifndef KATER_ORACLE_CERTIFICATE_HPP
#define KATER_ORACLE_CERTIFICATE_HPP

#include "Search.hpp"

#include "Checker.hpp"

#include <optional>
#include <string>

namespace oracle {

/*
 * Checks that CERT proves that every word of its left automaton is matched,
 * letter by letter, by a word of its right one, where a letter a is matched
 * by a letter b if (a, b) is among CERT's inclusions (or a = b). The check
 * searches for nothing: it verifies that
 *  - the simulation is one, and is transitive;
 *  - some pair covers each starting state;
 *  - each pair whose left state accepts has an accepting right state;
 *  - each step out of a pair lands on a pair the simulation subsumes.
 * Returns why CERT is not a proof, if it is not.
 */
auto checkCertificate(const Checker::Certificate &cert) -> std::optional<std::string>;

/*
 * Has Kater prove the assertions of FILE with certificates, checks each
 * certificate, and checks each letter inclusion they rest on against the
 * semantics, up to the search bound. Returns whether all of it holds.
 */
auto certifyFile(const std::string &file, const SearchOptions &opts, bool verbose) -> bool;

} // namespace oracle

#endif /* KATER_ORACLE_CERTIFICATE_HPP */
