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
#include "Config.hpp"
#include "Constraint.hpp"
#include "Exporter.hpp"
#include "ParsingDriver.hpp"
#include "Theory.hpp"
#include "Utils.hpp"

#include <unistd.h>

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
 * {"minus": [E, E]}, {"rot": E}, {"rec": {"relation": ID, "relations":
 * [ID, ...], "defs": [E, ...]}}, or {"inv": E}, the inverse of a "rec" (a
 * MutRecRE flagged flipped); a constraint is {"subset": SIDES},
 * {"equal": SIDES} or {"total": E}, SIDES being {"lhs": E, "rhs": E,
 * "sameEnds": B, "rotated": B}. An inclusion is SIDES with the "steps" of
 * the left side, each {"stage": NAME, "nfa": A, "origins": O}, the "chain"
 * of passes of the right side, the "chainOrigins" of its start and of each
 * pass's result, and the "certificate"; O lists, for each state, the states
 * of the automaton before it that it stands for. An inclusion of
 * decideExitWords has "lhs": null, and its steps start at the words.
 * Letters, automata, chains and certificates are as in the certificates'
 * JSON (Certificate.cpp).
 *
 * The evidence of an extensibility check is {"re": E, "single": B, "ppo":
 * E, "pporf": E, "cycles": A, "words": [{"backToEvent": B, "inclusion":
 * I}, ...]}: the expression of the constraint, the automaton the exits are
 * taken from, and an inclusion for each words automaton
 * (Checker::ExtensibilityEvidence).
 *
 * A file has the evidence of one claim: {"file": F, "assertion": TEXT,
 * "constraint": C, MODULE, "inclusions": [I, ...]} for an assertion, or a
 * claim of an export, and {"file": F, "claim": TEXT, "extensibility": X,
 * MODULE} for an extensibility check, MODULE being the members
 * "disjoint": [[ID, ...], ...], "perLoc": [[ID, ID], ...] and
 * "assumptions": [{"text": TEXT, "builtin": B, "saturated": B,
 * "temporary": B, "constraint": C}, ...].
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
		if (m->isFlipped())
			out << "{\"inv\": ";
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
		if (m->isFlipped())
			out << "}";
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
	case Words:
		return "words";
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
	if (ev.lhs)
		writeExp(out, *ev.lhs, theory);
	else
		out << "null";
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

/* An extensibility check's evidence */
void writeExtensibility(std::ostream &out, const Checker::ExtensibilityEvidence &ev,
			const Theory &theory)
{
	out << "{\"re\": ";
	writeExp(out, *ev.re, theory);
	out << ",\n \"single\": " << jsonBool(ev.single) << ",\n \"ppo\": ";
	writeExp(out, *ev.ppo, theory);
	out << ",\n \"pporf\": ";
	writeExp(out, *ev.pporf, theory);
	out << ",\n \"cycles\": ";
	writeNFA(out, ev.cycles, theory);
	out << ",\n \"words\": [";
	const auto *sep = "\n ";
	for (const auto &w : ev.words) {
		out << sep << "{\"backToEvent\": " << jsonBool(w.backToEvent)
		    << ",\n \"inclusion\": ";
		writeInclusion(out, w.evidence, theory);
		out << "}";
		sep = ",\n ";
	}
	out << "]}";
}

/* An assumption, as the evidence lists it: TEMPORARY if the exporter made
 * it for a while (an "unless" clause), SATURATED if the theory did not take
 * it in */
struct Assumed {
	std::unique_ptr<Constraint> constraint;
	std::string text;
	bool builtin;
	bool saturated;
	bool temporary;
};

/* The assumptions of MODULE as declared, after its theory takes in those it
 * does, which drops them from the module's list */
auto incorporateAssumptions(KatModule &module) -> std::vector<Assumed>
{
	const auto &theory = module.getTheory();
	std::vector<Assumed> assumptions;
	std::map<const AssumeStatement *, unsigned> numbers;
	for (const auto &a : module.getAssumptions()) {
		numbers.emplace(&*a, assumptions.size());
		assumptions.push_back({.constraint = a->getConstraint()->clone(),
				       .text = toString(*a->getConstraint(), theory),
				       .builtin = !a->getDbgInfo().has_value(),
				       .saturated = false,
				       .temporary = false});
	}
	module.getAssumptions().incorporateInto(module.getTheory());
	for (const auto &a : module.getAssumptions())
		assumptions[numbers.at(&*a)].saturated = true;
	return assumptions;
}

/* DECLARED, and the temporary assumptions MODULE has now */
auto withTemporaries(const KatModule &module, const std::vector<Assumed> &declared)
	-> std::vector<Assumed>
{
	std::vector<Assumed> result;
	for (const auto &a : declared)
		result.push_back({.constraint = a.constraint->clone(),
				  .text = a.text,
				  .builtin = a.builtin,
				  .saturated = a.saturated,
				  .temporary = false});
	for (const auto &a : module.getAssumptions())
		if (a->isTemporary())
			result.push_back({.constraint = a->getConstraint()->clone(),
					  .text = toString(*a->getConstraint(), module.getTheory()),
					  .builtin = false,
					  .saturated = true,
					  .temporary = true});
	return result;
}

/* What the evidence of a claim about MODULE says of it: its declarations
 * and ASSUMPTIONS, as members of the claim's object */
auto preamble(const KatModule &module, const std::vector<Assumed> &assumptions) -> std::string
{
	const auto &theory = module.getTheory();
	std::ostringstream out;
	out << ",\n \"disjoint\": [";
	const auto *sep = "";
	for (const auto &preds : module.disjointDeclarations()) {
		out << sep << "[";
		const auto *comma = "";
		for (auto p : preds) {
			out << comma << p;
			comma = ", ";
		}
		out << "]";
		sep = ", ";
	}
	/* The per-location variants of user relations: every declared relation
	 * has a let of its own name */
	out << "],\n \"perLoc\": [";
	sep = "";
	for (const auto &let : module.lets()) {
		const auto *charRE = dynamic_cast<const CharRE *>(let->getRE());
		if (charRE == nullptr || !charRE->getLabel().isRelation())
			continue;
		const auto &lab = charRE->getLabel();
		auto r = *lab.getRelation();
		if (!r.isUser() || r.isInverse() || lab.hasPreChecks() || lab.hasPostChecks() ||
		    !theory.hasPerLoc(r))
			continue;
		out << sep << "[" << r.getID() << ", " << theory.getPerLoc(r).getID() << "]";
		sep = ", ";
	}
	out << "],\n \"assumptions\": [";
	sep = "\n  ";
	for (const auto &a : assumptions) {
		out << sep << "{\"text\": " << jsonString(a.text)
		    << ", \"builtin\": " << jsonBool(a.builtin)
		    << ", \"saturated\": " << jsonBool(a.saturated)
		    << ", \"temporary\": " << jsonBool(a.temporary) << ",\n   \"constraint\": ";
		writeConstraint(out, *a.constraint, theory);
		out << "}";
		sep = ",\n  ";
	}
	out << "]";
	return out.str();
}

/* Writes to PATH the evidence of a subset or equality constraint proved by
 * INCLUSIONS, whose text is CLAIM */
void writeClaim(const std::filesystem::path &path, const std::string &file,
		const std::string &claim, const Constraint &cst, const std::string &preamble,
		const std::vector<std::string> &inclusions, const Theory &theory)
{
	std::ofstream out(path);
	out << "{\"file\": " << jsonString(file) << ",\n \"assertion\": " << jsonString(claim)
	    << ",\n \"constraint\": ";
	writeConstraint(out, cst, theory);
	out << preamble << ",\n \"inclusions\": [";
	const auto *sep = "\n ";
	for (const auto &inc : inclusions) {
		out << sep << inc;
		sep = ",\n ";
	}
	out << "]}\n";
}
/* formal: end EvidenceJSON */

} // namespace

auto writeEvidence(const std::string &file, const std::filesystem::path &dir, bool verbose) -> bool
{
	ParsingDriver driver;
	if (driver.parse(file) != 0)
		return false;
	auto module = driver.takeModule();
	const auto &theory = module->getTheory();
	auto declared = preamble(*module, incorporateAssumptions(*module));

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
		writeClaim(dir / std::format("{}.a{}.json", stem, k), file,
			   toString(*original, theory), *original, declared, inclusions, theory);
	}
	std::cout << file << ": evidence of " << proved << " of " << k << " assertions\n";
	return true;
}

auto writeExportEvidence(const std::string &file, const std::filesystem::path &dir, bool verbose)
	-> bool
{
	ParsingDriver driver;
	if (driver.parse(file) != 0)
		return false;
	auto module = driver.takeModule();
	const auto &theory = module->getTheory();
	auto declared = incorporateAssumptions(*module);
	auto stem = std::filesystem::path(file).stem().string();

	Checker checker(*module, {.parallel = false});

	/* The claims checkAssertion decides: each inclusion it proves, and the
	 * sides of the first, before expandRfs changed them */
	std::vector<std::string> inclusions;
	std::unique_ptr<RegExp> lhs;
	std::unique_ptr<RegExp> rhs;
	checker.setEvidenceSink([&](const SubsetConstraint & /*cst*/, const Checker::Evidence &ev) {
		if (inclusions.empty()) {
			lhs = ev.lhs->clone();
			rhs = ev.rhs->clone();
		}
		std::ostringstream out;
		writeInclusion(out, ev, theory);
		inclusions.push_back(out.str());
	});
	auto subsets = 0U;
	auto unproved = 0U;
	checker.setObserver([&](const Constraint &cst, const Checker::InclusionResult &r) {
		if (!r.result || inclusions.empty()) {
			unproved++;
			if (verbose)
				std::cout << file << ": Kater does not prove "
					  << WithTheory(cst, theory) << "\n";
			inclusions.clear();
			return;
		}
		const auto &sub = dynamic_cast<const SubsetConstraint &>(cst);
		std::unique_ptr<Constraint> original;
		if (dynamic_cast<const EqualityConstraint *>(&cst) != nullptr)
			original = EqualityConstraint::create(std::move(lhs), std::move(rhs),
							      sub.sameEnds(), sub.rotated());
		else
			original = SubsetConstraint::create(std::move(lhs), std::move(rhs),
							    sub.sameEnds(), sub.rotated());
		writeClaim(dir / std::format("{}.c{}.json", stem, ++subsets), file,
			   toString(*original, theory), *original,
			   preamble(*module, withTemporaries(*module, declared)), inclusions,
			   theory);
		inclusions.clear();
	});

	/* ... and the extensibility checks, which build automata of their own */
	auto extensible = 0U;
	checker.setExtensibilityEvidenceSink(
		[&](const Constraint &cst, const Checker::ExtensibilityEvidence &ev) {
			std::ofstream out(dir / std::format("{}.x{}.json", stem, ++extensible));
			out << "{\"file\": " << jsonString(file)
			    << ",\n \"claim\": " << jsonString(toString(cst, theory))
			    << ",\n \"extensibility\": ";
			writeExtensibility(out, ev, theory);
			out << preamble(*module, withTemporaries(*module, declared)) << "}\n";
		});

	/* Export into a scratch directory: only the claims matter here */
	auto scratch = std::filesystem::temp_directory_path() /
		       ("kater-oracle-evidence-" + std::to_string(getpid()));
	std::filesystem::create_directories(scratch);
	Config conf{};
	conf.generate = true;
	conf.name = stem;
	conf.dir = scratch.string();
	Exporter exporter(*module, checker, conf);
	auto exported = exporter.exportCode();
	std::filesystem::remove_all(scratch);
	std::cout << file << ": evidence of " << subsets << " inclusion claims and " << extensible
		  << " extensibility checks"
		  << (unproved != 0 ? std::format(" ({} claims not proved)", unproved) : "")
		  << (exported ? "" : "; the export failed") << "\n";
	return exported;
}

} // namespace oracle
