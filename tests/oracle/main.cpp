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

/*
 * kater-oracle: checks Kater's verdicts against the reference semantics.
 *
 *   kater-oracle check [-n EVENTS] [-t SECONDS] [--refutable] FILE...
 *       For every assertion of every FILE, compares Kater's verdict with a
 *       bounded search for a counterexample graph. A counterexample to an
 *       assertion Kater proved is a soundness bug (exit status 1). With
 *       --refutable, an assertion without a counterexample is an error too:
 *       the files are claims Kater must reject because they are false.
 *
 *   kater-oracle audit [-n EVENTS] [-t SECONDS]
 *       Checks every fact Kater's Theory states about the builtin relations
 *       and predicates against their meaning in GenMC.
 *
 *   kater-oracle explain FILE
 *       Prints the automaton of the left-hand side of each assertion of
 *       FILE through the stages of Kater's inclusion check.
 *
 *   kater-oracle transforms [-n EVENTS] [-t SECONDS] [--cases N] [--seed S]
 *                           [--depth D] [--only NAME]
 *       Tests the automaton transformations of the decision procedure
 *       against their semantic contracts, on random expressions.
 */

#include "Audit.hpp"
#include "Search.hpp"
#include "Transforms.hpp"

#include "Checker.hpp"
#include "Logger.hpp"
#include "NFAUtils.hpp"
#include "ParsingDriver.hpp"
#include "Saturation.hpp"
#include "Utils.hpp"

#include <cstdlib>
#include <iostream>
#include <memory>
#include <string>
#include <vector>

using namespace oracle;

/* Passes of the decision procedure with external linkage in Checker.cpp */
void normalize(NFA &nfa, const Theory &theory);

namespace {

struct Options {
	SearchOptions search;
	TransformOptions transforms;
	bool verbose = false;
	bool refutable = false;
	std::vector<std::string> files;
};

[[noreturn]] void usage()
{
	std::cerr
		<< "usage: kater-oracle check [-n EVENTS] [-t SECONDS] [--refutable] [-v] FILE...\n"
		   "       kater-oracle explain FILE...\n"
		   "       kater-oracle audit [-n EVENTS] [-t SECONDS] [-v]\n"
		   "       kater-oracle transforms [-n EVENTS] [-t SECONDS] [--cases N]\n"
		   "                               [--seed S] [--depth D] [--only NAME] [-v]\n";
	exit(2); // NOLINT(concurrency-mt-unsafe): single-threaded
}

auto parseOptions(int argc, char **argv, int first) -> Options
{
	Options opts;
	for (auto i = first; i < argc; i++) {
		std::string arg =
			argv[i]; // NOLINT(cppcoreguidelines-pro-bounds-pointer-arithmetic)
		auto value = [&]() -> unsigned {
			if (i + 1 >= argc)
				usage();
			// NOLINTNEXTLINE(cppcoreguidelines-pro-bounds-pointer-arithmetic)
			return static_cast<unsigned>(std::stoul(argv[++i]));
		};
		if (arg == "-n")
			opts.search.maxEvents = value();
		else if (arg == "-t")
			opts.search.timeoutMs = value() * 1000;
		else if (arg == "-v")
			opts.verbose = true;
		else if (arg == "--refutable")
			opts.refutable = true;
		else if (arg == "--cases")
			opts.transforms.cases = value();
		else if (arg == "--seed")
			opts.transforms.seed = value();
		else if (arg == "--depth")
			opts.transforms.depth = value();
		else if (arg == "--only" && i + 1 < argc)
			opts.transforms.only = argv
				[++i]; // NOLINT(cppcoreguidelines-pro-bounds-pointer-arithmetic)
		else if (!arg.empty() && arg[0] == '-')
			usage();
		else
			opts.files.push_back(arg);
	}
	return opts;
}

/* The hypotheses of a module: its user assumptions and disjointness declarations */
struct Hypotheses {
	std::vector<std::unique_ptr<Constraint>> assumptions;
	VSet<VSet<Predicate::ID>> disjoint;
};

/*
 * Kater folds some assumptions into its theory, and drops them, before it
 * checks anything: the hypotheses have to be taken before that. Built-in
 * assumptions are not hypotheses but claims about GenMC; audit checks them.
 */
auto takeHypotheses(const KatModule &module) -> Hypotheses
{
	Hypotheses h;
	for (const auto &assm : module.getAssumptions())
		if (assm->getDbgInfo().has_value())
			h.assumptions.push_back(assm->getConstraint()->clone());
	for (const auto &set : module.getTheory().disjointPredicateSets())
		if (std::ranges::any_of(set, [](auto id) { return id < 0; }))
			h.disjoint.insert(set);
	return h;
}

auto describe(const Search &s) -> std::string
{
	switch (s.outcome) {
	case Search::Outcome::NoCounterexample:
		return "no counterexample with up to " + std::to_string(s.events) + " events";
	case Search::Outcome::Counterexample:
		return "counterexample with " + std::to_string(s.events) + " events";
	case Search::Outcome::Unsupported:
		return "unsupported (" + s.detail + ")";
	case Search::Outcome::Unknown:
		return "unknown at " + std::to_string(s.events) + " events (" + s.detail + ")";
	}
	return {};
}

auto checkFile(const std::string &file, const Options &opts) -> bool
{
	ParsingDriver driver;
	if (driver.parse(file) != 0) {
		std::cerr << file << ": parse error\n";
		return false;
	}
	auto module = driver.takeModule();
	auto hyps = takeHypotheses(*module);

	std::vector<std::unique_ptr<Constraint>> goals;
	for (const auto &assrt : module->asserts())
		goals.push_back(assrt->getConstraint()->clone());

	module->getAssumptions().incorporateInto(module->getTheory());
	Checker checker(*module, {.parallel = false});

	auto sound = true;
	auto hypotheses = [&](Graph &g, Semantics &sem) -> Term {
		auto t = sem.declarationAxioms(hyps.disjoint);
		for (const auto &a : hyps.assumptions)
			t = t && sem.holds(*a);
		return t;
	};

	auto i = 0U;
	for (const auto &assrt : module->asserts()) {
		const auto &goal = *goals[i++];
		auto katerHolds = checker.checkAssertion(*assrt->getConstraint()).result;
		auto found = search(
			*module, hypotheses,
			[&](Graph & /*g*/, Semantics &sem) { return !sem.holds(goal); },
			opts.search);

		auto unsound = katerHolds && found.outcome == Search::Outcome::Counterexample;
		auto unrefuted = opts.refutable && found.outcome != Search::Outcome::Counterexample;
		sound &= !unsound && !unrefuted;

		std::cout << assrt->getDbgInfo() << ": assert "
			  << WithTheory(goal, module->getTheory())
			  << "\n    kater: " << (katerHolds ? "holds" : "does not hold")
			  << "; oracle: " << describe(found) << (unsound ? "  <-- UNSOUND" : "")
			  << (unrefuted ? "  <-- expected a counterexample" : "") << "\n";
		if (found.outcome == Search::Outcome::Counterexample && (unsound || opts.verbose))
			std::cout << found.detail;
	}
	return sound;
}

/* The left-hand side of each assertion through the stages of checkInclusion */
auto explainFile(const std::string &file) -> bool
{
	ParsingDriver driver;
	if (driver.parse(file) != 0)
		return false;
	auto module = driver.takeModule();
	module->getAssumptions().incorporateInto(module->getTheory());
	const auto &theory = module->getTheory();

	for (const auto &assrt : module->asserts()) {
		const auto *sub = dynamic_cast<const SubsetConstraint *>(assrt->getConstraint());
		if (sub == nullptr)
			continue;
		std::cout << assrt->getDbgInfo() << ": " << WithTheory(*sub, theory) << "\n";
		auto nfa = sub->getLHS()->toNFA();
		std::cout << "  toNFA:\n" << nfa;
		normalize(nfa, theory);
		std::cout << "  normalize:\n" << nfa;
		removeSimilarTransitions(nfa);
		if (sub->sameEnds()) {
			saturateInitFinalPreds(nfa, theory);
			std::cout << "  saturateInitFinalPreds:\n" << nfa;
			saturateLoc(nfa, theory);
			std::cout << "  saturateLoc:\n" << nfa;
		}
	}
	return true;
}

} // namespace

auto main(int argc, char **argv) -> int
{
	if (argc < 2)
		usage();
	std::string cmd = argv[1]; // NOLINT(cppcoreguidelines-pro-bounds-pointer-arithmetic)
	auto opts = parseOptions(argc, argv, 2);
	logLevel = VerbosityLevel::Error;

	if (cmd == "check") {
		if (opts.files.empty())
			usage();
		auto sound = true;
		for (const auto &f : opts.files)
			sound &= checkFile(f, opts);
		return sound ? 0 : 1;
	}
	if (cmd == "audit")
		return audit(opts.search, opts.verbose) ? 0 : 1;
	if (cmd == "explain") {
		auto ok = true;
		for (const auto &f : opts.files)
			ok &= explainFile(f);
		return ok ? 0 : 1;
	}
	if (cmd == "transforms") {
		opts.transforms.search = opts.search;
		opts.transforms.verbose = opts.verbose;
		return testTransforms(opts.transforms) ? 0 : 1;
	}
	usage();
}
