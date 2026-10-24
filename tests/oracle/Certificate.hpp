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

#include <filesystem>
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
 * Returns why CERT is not a proof, if it is not. formal/ has the same check
 * in Lean, with a proof that it is sound.
 */
auto checkCertificate(const Checker::Certificate &cert) -> std::optional<std::string>;

/* checkCertificate, then checkChain (Chain.hpp): why CERT, with the chain of
 * passes its right automaton came by, is not a proof, if it is not */
auto checkCertificateAndChain(const Checker::Certificate &cert) -> std::optional<std::string>;

/*
 * Has Kater prove the assertions of FILE with certificates, checks each
 * certificate and its chain, and checks against the semantics, up to the
 * search bound, what they rest on: each letter inclusion, each hypothesis a
 * saturation used, under the module's assumptions, and each pass of a chain
 * without evidence. Returns whether all of it holds.
 *
 * With JSONDIR, also writes the k-th certificate of FILE to
 * JSONDIR/<stem>.<k>.json, and copies of it that differ in one place to
 * JSONDIR/<stem>.<k>.<how>.json, each with checkCertificateAndChain's
 * verdict: the input of the checker in formal/.
 */
auto certifyFile(const std::string &file, const SearchOptions &opts, bool verbose,
		 const std::optional<std::filesystem::path> &jsonDir = std::nullopt) -> bool;

/* The pieces of the certificates' JSON, for other writers of it: a string, a
 * letter, an automaton, a chain, as formal/KaterCert/Read.lean reads them */
auto jsonString(const std::string &s) -> std::string;
auto jsonBool(bool b) -> const char *;
void writeLabel(std::ostream &out, const TransLabel &label, const Theory &theory);
void writeNFA(std::ostream &out, const NFA &nfa, const Theory &theory);
void writeChain(std::ostream &out, const Checker::Chain &chain, const Theory &theory);

/*
 * Writes CERT, the NTH certificate of FILE, a proof of CLAIM, with its chain,
 * to DIR/<stem>.<nth>.json, and copies of it that differ in one place to
 * DIR/<stem>.<nth>.<how>.json, each with checkCertificateAndChain's verdict:
 * those that differ in the certificate have no chain, those that differ in
 * the chain have the certificate
 */
void writeCertificateJSONs(const std::filesystem::path &dir, const std::string &file, unsigned nth,
			   const std::string &claim, const Checker::Certificate &cert,
			   const Theory &theory);

} // namespace oracle

#endif /* KATER_ORACLE_CERTIFICATE_HPP */
