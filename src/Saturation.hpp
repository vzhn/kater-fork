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

#ifndef KATER_SATURATION_HPP
#define KATER_SATURATION_HPP

#include "NFA.hpp"

#include <cstdint>
#include <utility>
#include <vector>

class Theory;

/* formal: begin SaturationEvidence, mirrored by formal/KaterCert/Saturation.lean */
/*
 * Evidence that a saturation of a right-hand side, from automaton N to M,
 * adds nothing its hypothesis does not justify: under the hypothesis, M
 * denotes no more than N (doc/verification.md, Evidence of the saturations).
 * Each state of M has a role, which bounds what the words reaching it
 * relate. The copies of the hypothesis' automaton that M has are anchored on
 * paths of N that read the hypothesis' word.
 */
struct SaturationEvidence {
	/* TRANSITIVE: letter;letter <= letter. WITHIN: [[automaton]] <= [[word]].
	 * EMPTY: [[automaton]] = 0 */
	enum class Hypothesis : std::uint8_t { Transitive, Within, Empty };

	/* What a state of M stands for: STATE, state STATE of N; AFTER, state
	 * STATE of N, entered by the transitive letter; COPY, state STATE of the
	 * automaton, in copy COPY (any copy, for an empty hypothesis) */
	struct Role {
		enum class Kind : std::uint8_t { State, After, Copy };
		Kind kind;
		unsigned state;
		unsigned copy = 0;
	};

	/* A step of a copy's path: its letter and destination, and the
	 * predicates of the word known of the event it leaves that it needs */
	struct Step {
		TransLabel letter;
		unsigned dest;
		PredicateSet known;
	};

	/* A copy of the automaton, from state FROM of N to state TO, along a
	 * PATH of N that reads the word */
	struct Copy {
		unsigned from;
		unsigned to;
		std::vector<Step> path;
	};

	Hypothesis hypothesis = Hypothesis::Within;
	TransLabel letter = TransLabel(std::nullopt);
	NFA automaton;
	std::vector<TransLabel> word;
	std::vector<Role> roles;
	std::vector<Copy> copies;
	/* (a, b): letter a is included in letter b, as the theory said */
	std::vector<std::pair<TransLabel, TransLabel>> inclusions;
};
/* formal: end SaturationEvidence */

/*
 * Saturates the NFA by (1) conjuncting all outgoing
 * predicates from the initial states with Q (where Q is
 * the disjunction of all incoming predicates to final states),
 * and (2) conjuncting all incoming predicates to final
 * states with P (where P is the disjunction of all outgoing
 * predicates from initial states).
 *
 * Pre: NFA is in normal form
 */
void saturateInitFinalPreds(NFA &nfa, const Theory &theory);

/*
 * If all the preds/successors of a given relation R relation are
 * restricted to a single memory location, it replaces R with its
 * per-loc counterpart
 *
 * Pre: NFA is in normal form
 */
void saturateLoc(NFA &nfa, const Theory &theory);

/*
 * The saturations of a right-hand side below record, with EV, the evidence
 * that the hypothesis justifies what they add: see SaturationEvidence. They
 * record nothing without.
 */

/* Saturates the NFA given an NFA ID with [[ID]] <= id: at each state, ID may be read */
void saturateID(NFA &nfa, NFA &&id, SaturationEvidence *ev = nullptr);

/* Saturates the NFA given that REL is transitive: where it reads REL, it may read REL+ */
void saturateTransitive(NFA &nfa, const Relation &rel, SaturationEvidence *ev = nullptr);

/* Saturates the NFA given an NFA SAT with [[SAT]] <= REL: SAT may be read
 * wherever the NFA reads a letter that includes REL */
void saturateBuiltin(NFA &nfa, const Relation &rel, NFA sat, const Theory &theory,
		     SaturationEvidence *ev = nullptr);

/*
 * Saturates the NFA given an NFA EMPTY that corresponds
 * to a relation R = 0
 */
void saturateEmpty(NFA &nfa, NFA &&empty, SaturationEvidence *ev = nullptr);

/*
 * Saturates by adding domains/codomains for all builtins.
 * (If a dom/codom does not compose with the existing
 * pre/post-checks of a label, the label is removed.)
 *
 */
void saturateDomains(NFA &nfa, const Theory &theory);

/*
 * Saturates the NFA by rotating it.
 */
void saturateRotate(NFA &nfa, const Theory &theory);

/*
 * Saturates the NFA given a hypothesis E <= WORD: wherever the NFA reads
 * WORD from a state P to a state Q, adds a path from P to Q that reads E.
 * This is sound because E <= WORD gives u;E;v <= u;WORD;v.
 *
 * The NFA reads WORD when each relation of WORD is included in the relation
 * the NFA reads there, and each predicate the NFA checks on the way is
 * implied by the predicates of WORD at that event. Each letter of WORD is a
 * predicate check or a bare relation.
 *
 * Pre: NFA is in normal form
 */
void saturateSubword(NFA &nfa, const NFA &e, const std::vector<TransLabel> &word,
		     const Theory &theory, SaturationEvidence *ev = nullptr);

#endif /* KATER_SATURATION_HPP */
