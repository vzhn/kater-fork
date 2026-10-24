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

#ifndef KATER_ORACLE_CHAIN_HPP
#define KATER_ORACLE_CHAIN_HPP

#include "Search.hpp"

#include "Checker.hpp"

#include <optional>
#include <string>
#include <utility>
#include <vector>

namespace oracle {

/*
 * Checks, without searching, that EV shows that under its hypothesis AFTER
 * denotes no more than BEFORE: that the roles are over AFTER's states, each
 * starting state's role bounds the identity, each step takes its source's
 * role to its destination's, and each accepting state's role is within
 * BEFORE's accepting states' (doc/verification.md, Evidence of the
 * saturations). Returns why it does not, if it does not. formal/ has the
 * same check in Lean, with a proof that it is sound.
 */
auto checkSaturation(const NFA &before, const NFA &after, const SaturationEvidence &ev)
	-> std::optional<std::string>;

/* Checks CERT's chain, if it has one: each saturation has evidence, which
 * checks, and the chain ends at CERT's right automaton */
auto checkChain(const Checker::Certificate &cert) -> std::optional<std::string>;

/* Whether A and B are the same automaton: the same states, steps, starting
 * states in the same order, and accepting states */
auto sameNFA(const NFA &a, const NFA &b) -> bool;

/* The number of states of the largest automaton of CHAIN */
auto largestAutomaton(const Checker::Chain &chain) -> size_t;

auto clone(const SaturationEvidence &ev) -> SaturationEvidence;
auto clone(const Checker::Chain &chain) -> Checker::Chain;

/* Copies of CERT, which has a chain, that each differ from it in one place
 * of the chain, named */
auto chainMutants(const Checker::Certificate &cert)
	-> std::vector<std::pair<std::string, Checker::Certificate>>;

/* What a chain rests on that the semantics decides, as a claim and the
 * graphs that refute it */
struct ChainClaim {
	std::string text;
	Query violation;
};

/* What a chain rests on that the semantics decides: the hypotheses of its
 * saturations, and the contracts of its passes without evidence, that the
 * result denotes no more than what the pass was given (for "rotate", has a
 * cycle only if it has one). The contracts of passes between automata too
 * large to check, see maxPassClaimRounds, are left out and counted */
struct ChainClaims {
	std::vector<ChainClaim> hypotheses;
	std::vector<ChainClaim> passes;
	unsigned largePasses = 0;
};

/* The claims CHAIN, of the proof of OF, rests on, for graphs up to EVENTS events */
auto chainClaims(const Checker::Chain &chain, const std::string &of, unsigned events,
		 const Theory &theory) -> ChainClaims;

/* The most rounds of NFASemantics, an automaton's states times the events
 * of a graph, of the automata a pass's claim is about: the semantics nests
 * its formulas once per round, and on automata with cycles of a few dozen
 * states Z3 takes gigabytes, then gives up */
constexpr size_t maxPassClaimRounds = 24;

} // namespace oracle

#endif /* KATER_ORACLE_CHAIN_HPP */
