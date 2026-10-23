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
 *   kater-oracle check [-n EVENTS] [-t SECONDS] FILE...
 *       For every assertion of every FILE, compares Kater's verdict with a
 *       bounded search for a counterexample graph. A counterexample to an
 *       assertion Kater proved is a soundness bug (exit status 1).
 *
 *   kater-oracle audit [-n EVENTS] [-t SECONDS]
 *       Checks every fact Kater's Theory states about the builtin relations
 *       and predicates against their meaning in GenMC.
 */

#include "Audit.hpp"
#include "Search.hpp"

#include "Checker.hpp"
#include "Logger.hpp"
#include "ParsingDriver.hpp"
#include "Utils.hpp"

#include <cstdlib>
#include <iostream>
#include <memory>
#include <string>
#include <vector>

using namespace oracle;

namespace {

struct Options {
	SearchOptions search;
	bool verbose = false;
	std::vector<std::string> files;
};

[[noreturn]] void usage()
{
	std::cerr << "usage: kater-oracle check [-n EVENTS] [-t SECONDS] [-v] FILE...\n"
		     "       kater-oracle audit [-n EVENTS] [-t SECONDS]\n";
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
		sound &= !unsound;

		std::cout << assrt->getDbgInfo() << ": assert "
			  << WithTheory(goal, module->getTheory())
			  << "\n    kater: " << (katerHolds ? "holds" : "does not hold")
			  << "; oracle: " << describe(found) << (unsound ? "  <-- UNSOUND" : "")
			  << "\n";
		if (found.outcome == Search::Outcome::Counterexample && (unsound || opts.verbose))
			std::cout << found.detail;
	}
	return sound;
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
	usage();
}
