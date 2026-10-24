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

#include "Evidence.hpp"

#include "Certificate.hpp"

#include "Checker.hpp"
#include "Constraint.hpp"
#include "ParsingDriver.hpp"
#include "Theory.hpp"
#include "Utils.hpp"

#include <format>
#include <fstream>
#include <iostream>
#include <map>
#include <memory>
#include <sstream>
#include <vector>

namespace oracle {

namespace {

/* formal: begin EvidenceJSON, mirrored by formal/KaterCert/ReadChain.lean */
/*
 * The evidence of an assertion as JSON, for the checker of whole proofs in
 * formal/. An expression is {"label": LETTER}, {"alt": [E, ...]},
 * {"seq": [E, ...]}, {"star": E}, {"plus": E}, {"opt": E}, {"and": [E, E]},
 * {"minus": [E, E]}, {"rot": E}, or {"rec": {"relation": ID, "relations":
 * [ID, ...], "defs": [E, ...]}}; a constraint is {"subset": SIDES},
 * {"equal": SIDES} or {"total": E}, SIDES being {"lhs": E, "rhs": E,
 * "sameEnds": B, "rotated": B}. An inclusion is SIDES with the "steps" of
 * the left side, each {"stage": NAME, "nfa": A, "origins": O}, the "chain"
 * of passes of the right side, the "chainOrigins" of its start and of each
 * pass's result, and the "certificate"; O lists, for each state, the states
 * of the automaton before it that it stands for. Letters, automata,
 * chains and certificates are as in the certificates' JSON
 * (Certificate.cpp).
 */

void writeExp(std::ostream &out, const RegExp &re, const Theory &theory)
{
	auto list = [&](const char *kind, auto &&kids) {
		out << "{\"" << kind << "\": [";
		const auto *sep = "";
		for (const auto &k : kids) {
			out << sep;
			writeExp(out, *k, theory);
			sep = ", ";
		}
		out << "]}";
	};
	auto one = [&](const char *kind) {
		out << "{\"" << kind << "\": ";
		writeExp(out, *re.getKid(0), theory);
		out << "}";
	};
	if (const auto *c = dynamic_cast<const CharRE *>(&re)) {
		out << "{\"label\": ";
		writeLabel(out, c->getLabel(), theory);
		out << "}";
	} else if (dynamic_cast<const AltRE *>(&re) != nullptr) {
		list("alt", re.kids());
	} else if (dynamic_cast<const SeqRE *>(&re) != nullptr) {
		list("seq", re.kids());
	} else if (dynamic_cast<const AndRE *>(&re) != nullptr) {
		list("and", re.kids());
	} else if (dynamic_cast<const MinusRE *>(&re) != nullptr) {
		list("minus", re.kids());
	} else if (dynamic_cast<const StarRE *>(&re) != nullptr) {
		one("star");
	} else if (dynamic_cast<const PlusRE *>(&re) != nullptr) {
		one("plus");
	} else if (dynamic_cast<const QMarkRE *>(&re) != nullptr) {
		one("opt");
	} else if (dynamic_cast<const RotRE *>(&re) != nullptr) {
		one("rot");
	} else if (const auto *m = dynamic_cast<const MutRecRE *>(&re)) {
		out << "{\"rec\": {\"relation\": " << m->getRelation().getID()
		    << ", \"relations\": [";
		const auto *sep = "";
		for (const auto &r : m->recs()) {
			out << sep << r.getID();
			sep = ", ";
		}
		out << "], \"defs\": [";
		sep = "";
		for (const auto &k : m->kids()) {
			out << sep;
			writeExp(out, *k, theory);
			sep = ", ";
		}
		out << "]}}";
	} else {
		out << "{\"unknown\": " << jsonString(toString(re, theory)) << "}";
	}
}

void writeSides(std::ostream &out, const char *kind, const SubsetConstraint &c,
		const Theory &theory)
{
	out << "{\"" << kind << "\": {\"lhs\": ";
	writeExp(out, *c.getLHS(), theory);
	out << ", \"rhs\": ";
	writeExp(out, *c.getRHS(), theory);
	out << ", \"sameEnds\": " << jsonBool(c.sameEnds())
	    << ", \"rotated\": " << jsonBool(c.rotated()) << "}}";
}

void writeConstraint(std::ostream &out, const Constraint &c, const Theory &theory)
{
	if (const auto *eq = dynamic_cast<const EqualityConstraint *>(&c)) {
		writeSides(out, "equal", *eq, theory);
	} else if (const auto *sub = dynamic_cast<const SubsetConstraint *>(&c)) {
		writeSides(out, "subset", *sub, theory);
	} else if (const auto *tot = dynamic_cast<const TotalityConstraint *>(&c)) {
		out << "{\"total\": ";
		writeExp(out, *tot->getRE(), theory);
		out << "}";
	} else {
		out << "{\"unknown\": " << jsonString(toString(c, theory)) << "}";
	}
}

auto stageName(Checker::Evidence::Stage stage) -> const char *
{
	using enum Checker::Evidence::Stage;
	switch (stage) {
	case Left:
		return "left";
	case LeftInitFinal:
		return "leftInitFinal";
	case LeftLoc:
		return "leftLoc";
	case LeftFinal:
		return "leftFinal";
	}
	return "unknown";
}

void writeCertificate(std::ostream &out, const Checker::Certificate &cert, const Theory &theory)
{
	out << "{\"lhs\": ";
	writeNFA(out, cert.lhs, theory);
	out << ",\n \"rhs\": ";
	writeNFA(out, cert.rhs, theory);
	out << ",\n \"simulation\": [";
	const auto width = std::max<size_t>(cert.lhs.getNumStates(), 1);
	const auto *sep = "";
	for (auto row = 0UL; row < cert.simulation.size(); row += width) {
		std::string bits;
		for (auto i = row; i < std::min(row + width, cert.simulation.size()); i++)
			bits += cert.simulation[i] != 0 ? '1' : '0';
		out << sep << jsonString(bits);
		sep = ", ";
	}
	out << "],\n \"pairs\": [";
	sep = "";
	for (const auto &[p, states] : cert.pairs) {
		out << sep << "[" << p << ", [";
		const auto *comma = "";
		for (auto q : states) {
			out << comma << q;
			comma = ", ";
		}
		out << "]]";
		sep = ", ";
	}
	out << "],\n \"inclusions\": [";
	sep = "";
	for (const auto &[a, b] : cert.inclusions) {
		out << sep << "[";
		writeLabel(out, a, theory);
		out << ", ";
		writeLabel(out, b, theory);
		out << "]";
		sep = ",\n  ";
	}
	out << "]}";
}

/* For each state of NFA, the states of the automaton before it that it
 * stands for */
void writeOrigins(std::ostream &out, const NFA &nfa)
{
	out << "[";
	const auto *sep = "";
	for (const auto &st : nfa.states()) {
		out << sep << "[";
		const auto *comma = "";
		for (auto o : st->getOrigins()) {
			out << comma << o;
			comma = ", ";
		}
		out << "]";
		sep = ", ";
	}
	out << "]";
}

/* An inclusion's evidence */
void writeInclusion(std::ostream &out, const Checker::Evidence &ev, const Theory &theory)
{
	out << "{\"lhs\": ";
	writeExp(out, *ev.lhs, theory);
	out << ",\n \"rhs\": ";
	writeExp(out, *ev.rhs, theory);
	out << ",\n \"sameEnds\": " << jsonBool(ev.sameEnds)
	    << ", \"rotated\": " << jsonBool(ev.rotated) << ",\n \"steps\": [";
	const auto *sep = "\n  ";
	for (const auto &step : ev.steps) {
		out << sep << "{\"stage\": \"" << stageName(step.stage) << "\",\n   \"nfa\": ";
		writeNFA(out, step.nfa, theory);
		out << ",\n   \"origins\": ";
		writeOrigins(out, step.nfa);
		out << "}";
		sep = ",\n  ";
	}
	/* Checker::checkInclusion records the chain whenever it records evidence */
	const auto &chain = *ev.certificate.chain;
	out << "],\n \"chain\": ";
	writeChain(out, chain, theory);
	out << ",\n \"chainOrigins\": [";
	writeOrigins(out, chain.start);
	for (const auto &p : chain.passes) {
		out << ",\n  ";
		writeOrigins(out, p.result);
	}
	out << "],\n \"certificate\": ";
	writeCertificate(out, ev.certificate, theory);
	out << "}";
}
/* formal: end EvidenceJSON */

} // namespace

auto writeEvidence(const std::string &file, const std::filesystem::path &dir, bool verbose)
	-> bool
{
	ParsingDriver driver;
	if (driver.parse(file) != 0)
		return false;
	auto module = driver.takeModule();
	const auto &theory = module->getTheory();

	/* The assumptions as declared: the theory takes some of them in, which
	 * drops them from the module's list */
	struct Assumed {
		std::unique_ptr<Constraint> constraint;
		std::string text;
		bool builtin;
	};
	std::vector<Assumed> assumptions;
	std::map<const AssumeStatement *, unsigned> numbers;
	for (const auto &a : module->getAssumptions()) {
		numbers.emplace(&*a, assumptions.size());
		assumptions.push_back({.constraint = a->getConstraint()->clone(),
				       .text = toString(*a->getConstraint(), theory),
				       .builtin = !a->getDbgInfo().has_value()});
	}
	module->getAssumptions().incorporateInto(module->getTheory());
	std::vector<bool> saturated(assumptions.size(), false);
	for (const auto &a : module->getAssumptions())
		saturated[numbers.at(&*a)] = true;

	std::ostringstream preamble;
	preamble << ",\n \"disjoint\": [";
	const auto *sep = "";
	for (const auto &preds : module->disjointDeclarations()) {
		preamble << sep << "[";
		const auto *comma = "";
		for (auto p : preds) {
			preamble << comma << p;
			comma = ", ";
		}
		preamble << "]";
		sep = ", ";
	}
	/* The per-location variants of user relations: every declared relation
	 * has a let of its own name */
	preamble << "],\n \"perLoc\": [";
	sep = "";
	for (const auto &let : module->lets()) {
		const auto *charRE = dynamic_cast<const CharRE *>(let->getRE());
		if (charRE == nullptr || !charRE->getLabel().isRelation())
			continue;
		const auto &lab = charRE->getLabel();
		auto r = *lab.getRelation();
		if (!r.isUser() || r.isInverse() || lab.hasPreChecks() || lab.hasPostChecks() ||
		    !theory.hasPerLoc(r))
			continue;
		preamble << sep << "[" << r.getID() << ", " << theory.getPerLoc(r).getID() << "]";
		sep = ", ";
	}
	preamble << "],\n \"assumptions\": [";
	sep = "\n  ";
	for (auto i = 0U; i < assumptions.size(); i++) {
		preamble << sep << "{\"text\": " << jsonString(assumptions[i].text)
			 << ", \"builtin\": " << jsonBool(assumptions[i].builtin)
			 << ", \"saturated\": " << jsonBool(saturated[i]) << ",\n   \"constraint\": ";
		writeConstraint(preamble, *assumptions[i].constraint, theory);
		preamble << "}";
		sep = ",\n  ";
	}
	preamble << "]";

	Checker checker(*module, {.parallel = false});
	std::vector<std::string> inclusions;
	checker.setEvidenceSink([&](const SubsetConstraint & /*cst*/, const Checker::Evidence &ev) {
		std::ostringstream out;
		writeInclusion(out, ev, theory);
		inclusions.push_back(out.str());
	});

	auto stem = std::filesystem::path(file).stem().string();
	auto k = 0U;
	auto proved = 0U;
	for (const auto &assrt : module->asserts()) {
		k++;
		auto original = assrt->getConstraint()->clone();
		inclusions.clear();
		if (!checker.checkAssertion(*assrt->getConstraint()).result) {
			if (verbose)
				std::cout << file << ": Kater does not prove "
					  << WithTheory(*original, theory) << "\n";
			continue;
		}
		proved++;
		std::ofstream out(dir / std::format("{}.a{}.json", stem, k));
		out << "{\"file\": " << jsonString(file)
		    << ",\n \"assertion\": " << jsonString(toString(*original, theory))
		    << ",\n \"constraint\": ";
		writeConstraint(out, *original, theory);
		out << preamble.str() << ",\n \"inclusions\": [";
		sep = "\n ";
		for (const auto &inc : inclusions) {
			out << sep << inc;
			sep = ",\n ";
		}
		out << "]}\n";
	}
	std::cout << file << ": evidence of " << proved << " of " << k << " assertions\n";
	return true;
}

} // namespace oracle
