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

#ifndef KATER_CHECKER_HPP
#define KATER_CHECKER_HPP

#include "Counterexample.hpp"
#include "KatModule.hpp"
#include "Saturation.hpp"

#include <functional>
#include <optional>
#include <string>

/*
 * The decision procedure: decides constraints over a module's relations
 * under the hypotheses of its theory.
 *
 * A constraint is decided by translating both sides to automata,
 * saturating the right-hand side with the theory's assumptions, and
 * checking language inclusion. A positive answer is a claim that the
 * constraint holds in every execution of the model; a negative answer
 * comes with a counterexample path.
 *
 * This is the only component whose correctness decides whether a "holds"
 * verdict is sound. It depends on the theory and the automata layers, and
 * on nothing else: not on the command line, nor on code export.
 */
struct CheckerOptions {
	/* Decide the module's assertions in parallel */
	bool parallel = true;
	/* Report each assertion as it is being checked */
	bool trace = false;
};

class Checker {

public:
	using Options = CheckerOptions;

	struct InclusionResult {
		bool result{};
		Counterexample cex;
	};

	/* Called with each constraint checkAssertion decides, and its verdict:
	 * a record of what Kater claims, for checking it independently */
	using Observer = std::function<void(const Constraint &, const InclusionResult &)>;

	/* formal: begin Chain, mirrored by formal/KaterCert/Chain.lean */
	/*
	 * How the right automaton of an inclusion check came from the right-hand
	 * side: the automaton the right-hand side normalized to, and each pass
	 * after it with the automaton it produced, the last of which is the
	 * right automaton. A saturation comes with the evidence that its
	 * hypothesis justifies what it added. The other passes are trusted:
	 * "normalize" and "prune" denote no more than they are given, and
	 * "rotate" adds no cycle
	 */
	struct Pass {
		std::string name;
		std::optional<SaturationEvidence> evidence;
		NFA result;
	};
	struct Chain {
		NFA start;
		std::vector<Pass> passes;
	};
	/* formal: end Chain */

	/* formal: begin Certificate, mirrored by formal/KaterCert/Checker.lean */
	/*
	 * What the proof of an inclusion rests on, for checking it without
	 * searching: the automata the check compared, the simulation it used on
	 * the left one, the pairs (left state, set of right states) it explored,
	 * and the letter inclusions it took from the theory. The proof holds if
	 * the pairs cover the starting ones, every accepting left state of a
	 * pair meets an accepting right state, and every step out of a pair
	 * lands on a pair the simulation subsumes.
	 */
	struct Certificate {
		NFA lhs;
		NFA rhs;
		/* simulation[simulated * |lhs| + simulator] */
		std::vector<uint8_t> simulation;
		std::vector<std::pair<unsigned, VSet<unsigned>>> pairs;
		/* (a, b): letter a is included in letter b */
		std::vector<std::pair<TransLabel, TransLabel>> inclusions;
		/* How RHS came from the right-hand side, if recorded: checked on
		 * its own (formal/KaterCert/Chain.lean) */
		std::optional<Chain> chain;
	};
	/* formal: end Certificate */
	/* Gets the certificate of an inclusion, and the constraint it proves it
	 * for: the subset constraint checkInclusion decides, or the acyclicity or
	 * coherence constraint whose extensibility isPPOIntersectionInPPO or
	 * isCoherenceExtensible checks */
	using CertificateSink = std::function<void(const Constraint &, const Certificate &)>;

	Checker() = delete;
	Checker(KatModule &mod, Options opts = {}) : module(&mod), options(opts) {}

	[[nodiscard]] auto getModule() const -> const KatModule & { return *module; }
	auto getModule() -> KatModule & { return *module; }

	/* Check the module's user assertions and report the violated ones.
	 * Returns whether all of them hold */
	auto checkAssertions() -> bool;

	/* Decide a subset or equality constraint */
	auto checkAssertion(Constraint &cst) -> InclusionResult;

	void setObserver(Observer obs) { observer = std::move(obs); }

	/* Called with the certificate of each inclusion checkAssertion and the
	 * extensibility checks prove */
	void setCertificateSink(CertificateSink sink) { certificateSink = std::move(sink); }

	/*
	 * The exporter's check of extensibility. GenMC adds an event e once its
	 * pporf-predecessors are in the graph; when ppo is not po, e may have
	 * po-successors there already. Added maximally (reading the last write
	 * in mo, or last in mo), e has no eco step out of it. Decides that no
	 * cycle of ACYC can then leave e by another step without a pporf step
	 * out of e, unless it can do without e (both its steps at e within
	 * po): every such visit of e, read from e to the end of the word of
	 * ACYC it leaves e in, is in pporf ; any*.
	 *
	 * With isCoherenceExtensible for the coherence view, this proves:
	 * for every consistent graph and every event e GenMC may add to it
	 * (nothing after it in pporf, nothing reading from it, not part of an
	 * RMW, not a thread start or create), such that nothing po-after e
	 * accesses e's location, the graph with e added maximally is
	 * consistent (doc/verification.md, "Extensibility")
	 */
	auto isPPOIntersectionInPPO(const AcyclicConstraint *acyc) const -> InclusionResult;
	/* The same for the cycles of COH's view composed with eco, which must
	 * be irreflexive: a cycle that leaves e where its word begins comes
	 * back to e, and may also be a po path to another event of e's
	 * location, and eco back, which there is none of */
	auto isCoherenceExtensible(const CoherenceConstraint *coh) const -> InclusionResult;

private:
	[[nodiscard]] auto getTheory() const -> const Theory & { return getModule().getTheory(); }
	[[nodiscard]] auto getOptions() const -> const Options & { return options; }

	auto isDFASubLanguageOfNFA(NFA &nfa, const NFA &other, Certificate *cert = nullptr) const
		-> InclusionResult;
	/* Saturates RHS with the module's assumptions, normalizing after each,
	 * and prunes what LHS cannot use; records the passes in CHAIN, if any */
	void saturateRHS(NFA &rhs, const NFA &lhs, std::optional<Chain> &chain) const;
	/* isDFASubLanguageOfNFA, with the certificate, if it holds, handed to
	 * the certificate sink with CST, the constraint it is a proof for, and
	 * CHAIN, how RHS came from the right-hand side */
	auto decideInclusion(NFA &lhs, const NFA &rhs, const Constraint &cst,
			     std::optional<Chain> chain) const -> InclusionResult;
	[[nodiscard]] auto checkInclusion(SubsetConstraint &subsetC) const -> InclusionResult;
	/* The extensibility check of CST, whose cycles are those of the words of
	 * RE (of one word, with SINGLE) */
	auto decideExtensibility(const RegExp &re, bool single, const Constraint &cst) const
		-> InclusionResult;
	/* Whether every word of WORDS, read from an event GenMC may add, has a
	 * pporf step out of the event, or else, with BACK_TO_EVENT, is a po
	 * path to an event of its location and eco back */
	auto decideExitWords(NFA &words, bool backToEvent, const Constraint &cst) const
		-> InclusionResult;

	KatModule *module;
	Options options;
	Observer observer;
	CertificateSink certificateSink;
};

/* A diagnostic note describing CEX, to be appended to an error message */
auto cexNote(const Counterexample &cex, const Theory &theory) -> std::string;

#endif /* KATER_CHECKER_HPP */
