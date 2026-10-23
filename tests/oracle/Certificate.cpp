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

#include "Certificate.hpp"

#include "ParsingDriver.hpp"
#include "Theory.hpp"
#include "Utils.hpp"

#include <iostream>
#include <set>
#include <vector>

namespace oracle {

auto checkCertificate(const Checker::Certificate &cert) -> std::optional<std::string>
{
	const auto &lhs = cert.lhs;
	const auto &rhs = cert.rhs;
	const auto n = static_cast<unsigned>(lhs.getNumStates());

	if (cert.simulation.size() != static_cast<size_t>(n) * n)
		return "the simulation is not over the left automaton's states";
	auto simulates = [&](unsigned simulator, unsigned simulated) {
		return cert.simulation[(static_cast<size_t>(simulated) * n) + simulator] != 0;
	};

	/* The simulation: a simulator accepts what it simulates does, and
	 * follows each of its steps into a simulating state; and is transitive,
	 * so that subsumption composes along a word */
	for (auto p = 0U; p < n; p++) {
		if (!simulates(p, p))
			return "the simulation is not reflexive at " + std::to_string(p);
		for (auto s = 0U; s < n; s++) {
			if (s == p || !simulates(s, p))
				continue;
			if (lhs[p]->isAccepting() && !lhs[s]->isAccepting())
				return "a non-accepting state simulates an accepting one";
			for (const auto &t : lhs[p]->outs()) {
				auto follows = std::ranges::any_of(lhs[s]->outs(), [&](auto &u) {
					return u.label == t.label &&
					       simulates(u.dest->getId(), t.dest->getId());
				});
				if (!follows)
					return "state " + std::to_string(s) +
					       " does not simulate " + std::to_string(p);
			}
			for (auto r = 0U; r < n; r++)
				if (simulates(r, s) && !simulates(r, p))
					return "the simulation is not transitive";
		}
	}

	/* Negated predicates in the right automaton would make the search split
	 * letters, which this check does not model */
	for (const auto &q : rhs.states())
		for (const auto &t : q->outs())
			if (std::ranges::any_of(t.label.getPreChecks(),
						[](auto &p) { return p.isComplement(); }))
				return "the right automaton has negated predicates";

	std::set<std::pair<TransLabel, TransLabel>> included(cert.inclusions.begin(),
							     cert.inclusions.end());
	auto matches = [&](const TransLabel &a, const TransLabel &b) {
		return a == b || included.contains({a, b});
	};
	auto next = [&](const TransLabel &a, const VSet<unsigned> &states) {
		VSet<unsigned> result;
		for (auto q : states)
			for (const auto &t : rhs[q]->outs())
				if (matches(a, t.label))
					result.insert(t.dest->getId());
		return result;
	};

	std::vector<std::vector<VSet<unsigned>>> byState(n);
	for (const auto &[p, states] : cert.pairs) {
		if (p >= n)
			return "a pair names no left state";
		byState[p].push_back(states);
	}
	auto covered = [&](unsigned p, const VSet<unsigned> &states) {
		for (auto s = 0U; s < n; s++)
			if (simulates(s, p) && std::ranges::any_of(byState[s], [&](auto &q) {
				    return q.subsetOf(states);
			    }))
				return true;
		return false;
	};

	VSet<unsigned> rhsStarts;
	for (const auto *q : rhs.starting())
		rhsStarts.insert(q->getId());
	for (const auto *p : lhs.starting())
		if (!covered(p->getId(), rhsStarts))
			return "no pair covers starting state " + std::to_string(p->getId());

	for (const auto &[p, states] : cert.pairs) {
		if (lhs[p]->isAccepting() &&
		    std::ranges::none_of(states, [&](auto q) { return rhs[q]->isAccepting(); }))
			return "left state " + std::to_string(p) +
			       " accepts where no right state does";
		for (const auto &t : lhs[p]->outs())
			if (!covered(t.dest->getId(), next(t.label, states)))
				return "a step out of a pair of left state " + std::to_string(p) +
				       " lands on no subsumed pair";
	}
	return std::nullopt;
}

auto certifyFile(const std::string &file, const SearchOptions &opts, bool verbose) -> bool
{
	ParsingDriver driver;
	if (driver.parse(file) != 0)
		return false;
	auto module = driver.takeModule();
	auto hyps = takeHypotheses(*module);
	module->getAssumptions().incorporateInto(module->getTheory());
	const auto &theory = module->getTheory();

	Checker checker(*module, {.parallel = false});
	auto ok = true;
	auto certificates = 0U;
	std::set<std::pair<TransLabel, TransLabel>> inclusions;
	checker.setCertificateSink(
		[&](const SubsetConstraint &c, const Checker::Certificate &cert) {
			certificates++;
			if (auto why = checkCertificate(cert)) {
				ok = false;
				std::cout << "INVALID certificate for " << WithTheory(c, theory)
					  << ": " << *why << "\n";
				return;
			}
			if (verbose)
				std::cout << "valid certificate for " << WithTheory(c, theory)
					  << " (" << cert.pairs.size() << " pairs)\n";
			for (const auto &[a, b] : cert.inclusions)
				if (a != b)
					inclusions.emplace(a, b);
		});
	for (const auto &assrt : module->asserts())
		checker.checkAssertion(*assrt->getConstraint());

	/* The letter inclusions the certificates rest on */
	auto refuted = 0U;
	for (const auto &[a, b] : inclusions) {
		auto s = search(
			*module, [&](Graph &g, Semantics &sem) { return hyps(g, sem); },
			[&](Graph & /*g*/, Semantics &sem) {
				return !sem.eval(a).includedIn(sem.eval(b));
			},
			opts);
		if (s.outcome == Search::Outcome::Counterexample) {
			ok = false;
			refuted++;
			std::cout << "FALSE inclusion " << toString(a, theory)
				  << " <= " << toString(b, theory) << "\n"
				  << s.detail;
		}
	}
	std::cout << file << ": " << certificates << " certificates, " << inclusions.size()
		  << " letter inclusions (" << refuted << " false, up to " << opts.maxEvents
		  << " events)\n";
	return ok;
}

} // namespace oracle
