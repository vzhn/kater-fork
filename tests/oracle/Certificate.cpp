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

#include "Constraint.hpp"
#include "NFAUtils.hpp"
#include "ParsingDriver.hpp"
#include "Theory.hpp"
#include "Utils.hpp"

#include <algorithm>
#include <cctype>
#include <format>
#include <fstream>
#include <functional>
#include <iostream>
#include <set>
#include <vector>

namespace oracle {

namespace {

/* formal: begin CertificateJSON, mirrored by formal/KaterCert/Read.lean */
/*
 * Certificates as JSON, for the checker in formal/: a certificate's automata,
 * simulation, pairs and letter inclusions, as Checker::Certificate has them.
 * A letter is {"relation": [id, inverse] or null, "pre": [[id, complement],
 * ...], "post": [...]}, with its text for the reader; row p of the
 * simulation lists, as 0s and 1s, which states simulate p.
 */

auto jsonString(const std::string &s) -> std::string
{
	std::string result = "\"";
	for (auto c : s) {
		auto u = static_cast<unsigned char>(c);
		if (c == '"' || c == '\\') {
			result += '\\';
			result += c;
		} else if (std::iscntrl(u) != 0) {
			result += std::format("\\u{:04x}", u);
		} else {
			result += c;
		}
	}
	return result + "\"";
}

auto jsonBool(bool b) -> const char * { return b ? "true" : "false"; }

void writeChecks(std::ostream &out, const PredicateSet &checks)
{
	out << "[";
	const auto *sep = "";
	for (const auto &p : checks) {
		out << sep << "[" << p.getID() << ", " << jsonBool(p.isComplement()) << "]";
		sep = ", ";
	}
	out << "]";
}

void writeLabel(std::ostream &out, const TransLabel &label, const Theory &theory)
{
	out << "{\"relation\": ";
	if (const auto &r = label.getRelation())
		out << "[" << r->getID() << ", " << jsonBool(r->isInverse()) << "]";
	else
		out << "null";
	out << ", \"pre\": ";
	writeChecks(out, label.getPreChecks());
	out << ", \"post\": ";
	writeChecks(out, label.getPostChecks());
	out << ", \"text\": " << jsonString(toString(label, theory)) << "}";
}

void writeNFA(std::ostream &out, const NFA &nfa, const Theory &theory)
{
	out << "{\"states\": " << nfa.getNumStates() << ",\n  \"starting\": [";
	const auto *sep = "";
	for (const auto *s : nfa.starting()) {
		out << sep << s->getId();
		sep = ", ";
	}
	out << "],\n  \"accepting\": [";
	sep = "";
	for (const auto *s : nfa.accepting()) {
		out << sep << s->getId();
		sep = ", ";
	}
	out << "],\n  \"transitions\": [";
	sep = "\n   ";
	for (const auto &s : nfa.states()) {
		for (const auto &t : s->outs()) {
			out << sep << "[" << s->getId() << ", ";
			writeLabel(out, t.label, theory);
			out << ", " << t.dest->getId() << "]";
			sep = ",\n   ";
		}
	}
	out << "]}";
}

/* VERDICT is what checkCertificate says of CERT; MUTATION names how CERT
 * differs from Kater's certificate, if it does */
void writeJSON(const std::filesystem::path &path, const std::string &file,
	       const std::string &constraint, const std::string &mutation,
	       const Checker::Certificate &cert, const std::optional<std::string> &verdict,
	       const Theory &theory)
{
	std::ofstream out(path);
	out << "{\"file\": " << jsonString(file)
	    << ",\n \"constraint\": " << jsonString(constraint);
	if (!mutation.empty())
		out << ",\n \"mutation\": " << jsonString(mutation);
	out << ",\n \"verdict\": " << jsonString(verdict ? "invalid: " + *verdict : "valid");
	out << ",\n \"lhs\": ";
	writeNFA(out, cert.lhs, theory);
	out << ",\n \"rhs\": ";
	writeNFA(out, cert.rhs, theory);

	out << ",\n \"simulation\": [";
	const auto width = std::max<size_t>(cert.lhs.getNumStates(), 1);
	const auto *sep = "\n  ";
	for (auto row = 0UL; row < cert.simulation.size(); row += width) {
		std::string bits;
		for (auto i = row; i < std::min(row + width, cert.simulation.size()); i++)
			bits += cert.simulation[i] != 0 ? '1' : '0';
		out << sep << jsonString(bits);
		sep = ",\n  ";
	}

	out << "],\n \"pairs\": [";
	sep = "\n  ";
	for (const auto &[p, states] : cert.pairs) {
		out << sep << "[" << p << ", [";
		const auto *comma = "";
		for (auto q : states) {
			out << comma << q;
			comma = ", ";
		}
		out << "]]";
		sep = ",\n  ";
	}

	out << "],\n \"inclusions\": [";
	sep = "\n  ";
	for (const auto &[a, b] : cert.inclusions) {
		out << sep << "[";
		writeLabel(out, a, theory);
		out << ", ";
		writeLabel(out, b, theory);
		out << "]";
		sep = ",\n  ";
	}
	out << "]}\n";
}
/* formal: end CertificateJSON */

auto clone(const Checker::Certificate &cert) -> Checker::Certificate
{
	return {.lhs = copy(cert.lhs),
		.rhs = copy(cert.rhs),
		.simulation = cert.simulation,
		.pairs = cert.pairs,
		.inclusions = cert.inclusions};
}

/* The index of whether S simulates P, in a simulation over N states */
auto entry(unsigned n, unsigned s, unsigned p) -> size_t
{
	return (static_cast<size_t>(p) * n) + s;
}

/* A state that does not simulate another one, if any: the index of the
 * entry. CERT's simulation is over its N states */
auto missingSimulation(const Checker::Certificate &cert, unsigned n) -> std::optional<size_t>
{
	for (auto p = 0U; p < n; p++)
		for (auto s = 0U; s < n; s++)
			if (s != p && cert.simulation.at(entry(n, s, p)) == 0)
				return entry(n, s, p);
	return std::nullopt;
}

/* A state r that simulates a state s that simulates p, and r simulating p,
 * if any: the index of that last entry, without which the simulation is not
 * transitive */
auto transitiveSimulation(const Checker::Certificate &cert, unsigned n) -> std::optional<size_t>
{
	auto sim = [&](unsigned s, unsigned p) { return cert.simulation.at(entry(n, s, p)) != 0; };
	for (auto p = 0U; p < n; p++)
		for (auto s = 0U; s < n; s++)
			for (auto r = 0U; r < n; r++)
				if (r != s && s != p && r != p && sim(r, s) && sim(s, p) &&
				    sim(r, p))
					return entry(n, r, p);
	return std::nullopt;
}

/*
 * Copies of CERT that each differ from it in one place, named: for checking
 * that another checker of certificates says what checkCertificate says of
 * them, and for the same reason
 */
auto mutants(const Checker::Certificate &cert)
	-> std::vector<std::pair<std::string, Checker::Certificate>>
{
	std::vector<std::pair<std::string, Checker::Certificate>> result;
	auto add = [&](const std::string &name,
		       const std::function<void(Checker::Certificate &)> &mutate) {
		auto m = clone(cert);
		mutate(m);
		result.emplace_back(name, std::move(m));
	};
	const auto n = static_cast<unsigned>(cert.lhs.getNumStates());

	if (n > 0 && cert.simulation.size() == static_cast<size_t>(n) * n) {
		add("simulation-size", [](auto &m) { m.simulation.pop_back(); });
		add("not-reflexive", [](auto &m) { m.simulation.at(0) = 0; });
		if (auto i = missingSimulation(cert, n))
			add("more-simulation", [i = *i](auto &m) { m.simulation.at(i) = 1; });
		if (auto i = transitiveSimulation(cert, n))
			add("not-transitive", [i = *i](auto &m) { m.simulation.at(i) = 0; });
		/* The identity, which is a simulation */
		add("identity-simulation", [n](auto &m) {
			m.simulation.assign(m.simulation.size(), 0);
			for (auto p = 0U; p < n; p++)
				m.simulation.at(entry(n, p, p)) = 1;
		});
	}

	if (!cert.pairs.empty()) {
		add("drop-first-pair", [](auto &m) { m.pairs.erase(m.pairs.begin()); });
		add("drop-last-pair", [](auto &m) { m.pairs.pop_back(); });
	}
	/* A pair claiming its words from fewer right states */
	auto pair = std::ranges::find_if(cert.pairs, [](auto &p) { return !p.second.empty(); });
	if (pair != cert.pairs.end()) {
		add("shrink-pair", [i = pair - cert.pairs.begin()](auto &m) {
			auto &states = m.pairs.at(i).second;
			states.erase(states.max());
		});
	}
	add("pair-out-of-range", [n](auto &m) { m.pairs.emplace_back(n, VSet<unsigned>{}); });

	auto inclusion = std::ranges::find_if(cert.inclusions,
					      [](auto &ab) { return ab.first != ab.second; });
	if (inclusion != cert.inclusions.end()) {
		add("drop-inclusion", [i = inclusion - cert.inclusions.begin()](auto &m) {
			m.inclusions.erase(m.inclusions.begin() + i);
		});
	}

	add("rhs-accepts-nothing", [](auto &m) { m.rhs.clearAllAccepting(); });
	add("lhs-accepts-everywhere", [](auto &m) {
		for (const auto &s : m.lhs.states())
			m.lhs.makeAccepting(s.get());
	});
	if (cert.rhs.getNumStates() > 0) {
		add("rhs-negated", [](auto &m) {
			auto p = Predicate::createBuiltin(Predicate::BuiltinID::R);
			p.complement();
			auto *q = m.rhs[0];
			NFA::addTransition(q, NFA::Transition(TransLabel(std::nullopt, {p}), q));
		});
	}
	return result;
}

} // namespace

void writeCertificateJSONs(const std::filesystem::path &dir, const std::string &file, unsigned nth,
			   const std::string &claim, const Checker::Certificate &cert,
			   const Theory &theory)
{
	auto base = std::format("{}.{}", std::filesystem::path(file).stem().string(), nth);
	writeJSON(dir / std::format("{}.json", base), file, claim, "", cert, checkCertificate(cert),
		  theory);
	for (const auto &[name, m] : mutants(cert))
		writeJSON(dir / std::format("{}.{}.json", base, name), file, claim, name, m,
			  checkCertificate(m), theory);
}

/* formal: begin checkCertificate, mirrored by formal/KaterCert/Checker.lean */
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
	 * follows each of its steps into a simulating state. It is also
	 * reflexive and transitive, as Kater's is, though the proof of this
	 * check in formal/ needs neither */
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
/* formal: end checkCertificate */

auto certifyFile(const std::string &file, const SearchOptions &opts, bool verbose,
		 const std::optional<std::filesystem::path> &jsonDir) -> bool
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
		[&](const Constraint &cst, const Checker::Certificate &cert) -> void {
			certificates++;
			auto why = checkCertificate(cert);
			if (jsonDir)
				writeCertificateJSONs(*jsonDir, file, certificates,
						      toString(cst, theory), cert, theory);
			if (why) {
				ok = false;
				std::cout << "INVALID certificate for " << WithTheory(cst, theory)
					  << ": " << *why << "\n";
				return;
			}
			if (verbose)
				std::cout << "valid certificate for " << WithTheory(cst, theory)
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
