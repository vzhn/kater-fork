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

#include "Export.hpp"

#include "Checker.hpp"
#include "Config.hpp"
#include "Exporter.hpp"
#include "ParsingDriver.hpp"
#include "SavedExp.hpp"
#include "Statement.hpp"
#include "Utils.hpp"

#include <unistd.h>

#include <filesystem>
#include <iostream>
#include <map>
#include <memory>
#include <string>
#include <vector>

namespace oracle {

namespace {

/* A claim the Checker made, with the temporary assumptions it was made under */
struct Claim {
	std::unique_ptr<Constraint> constraint;
	std::vector<std::unique_ptr<Constraint>> temporaries;
	bool holds;
};

/* What the module defines: lets and views by name, and the export constraints */
struct Definitions {
	std::map<std::string, std::unique_ptr<RegExp>> lets;
	std::map<std::string, std::unique_ptr<RegExp>> views;
	std::vector<std::unique_ptr<Constraint>> exports;
};

auto takeDefinitions(const KatModule &module) -> Definitions
{
	Definitions d;
	for (const auto &let : module.lets()) {
		d.lets.emplace(let->getName(), let->getRE()->clone());
		if (const auto *view = dynamic_cast<const ViewExp *>(let->getSaved()))
			d.views.emplace(let->getName(), view->getRE()->clone());
	}
	for (const auto &e : module.exports()) {
		d.exports.push_back(e->getConstraint()->clone());
		d.exports.push_back(e->getUnless() != nullptr ? e->getUnless()->clone() : nullptr);
	}
	return d;
}

/*
 * What a view computes. GenMC computes a recursive view from its body, in
 * which the view's own relation stands for its value so far: the view
 * means the fixpoint of its definitions, with the body in place of its own.
 */
auto viewMeaning(const RegExp &let, const RegExp &body) -> std::unique_ptr<RegExp>
{
	const auto *mutRec = dynamic_cast<const MutRecRE *>(&let);
	if (mutRec == nullptr)
		return body.clone();
	std::vector<std::unique_ptr<RegExp>> kids;
	auto recs = mutRec->recs();
	for (auto i = 0U; i < mutRec->getNumKids(); i++)
		kids.push_back(recs[i] == mutRec->getRelation() ? body.clone()
								: mutRec->getKid(i)->clone());
	return MutRecRE::create(mutRec->getRelation(),
				std::vector<Relation>(recs.begin(), recs.end()), std::move(kids));
}

/* The expressions a constraint is about */
auto exprsOf(const Constraint *c) -> std::vector<const RegExp *>
{
	if (const auto *sub = dynamic_cast<const SubsetConstraint *>(c))
		return {sub->getLHS(), sub->getRHS()};
	if (const auto *acyc = dynamic_cast<const AcyclicConstraint *>(c))
		return {acyc->getRE()};
	return {};
}

class Validator {

public:
	Validator(const KatModule &module, const Hypotheses &hyps, const SearchOptions &opts,
		  bool verbose)
		: module_(&module), hyps_(&hyps), opts_(opts), verbose_(verbose)
	{
	}

	/* Searches for a graph where VIOLATION holds, reporting WHAT on one */
	void expectNone(const std::string &what, const Query &extraHypotheses,
			const Query &violation)
	{
		auto s = search(
			*module_,
			[&](Graph &g, Semantics &sem) {
				return (*hyps_)(g, sem) && extraHypotheses(g, sem);
			},
			violation, opts_);
		switch (s.outcome) {
		case Search::Outcome::NoCounterexample:
			holding_++;
			if (verbose_)
				std::cout << "ok:       " << what << "\n";
			break;
		case Search::Outcome::Counterexample:
			failing_++;
			std::cout << "FALSE:    " << what << "\n" << s.detail;
			break;
		case Search::Outcome::Unsupported:
		case Search::Outcome::Unknown:
			unchecked_++;
			std::cout << "unchecked: " << what << " (" << s.detail << ")\n";
			break;
		}
	}

	void summary(const std::string &file) const
	{
		std::cout << file << ": " << holding_ << " hold, " << failing_ << " are false, "
			  << unchecked_ << " were not checked (up to " << opts_.maxEvents
			  << " events)\n";
	}

	[[nodiscard]] auto ok() const -> bool { return failing_ == 0; }

private:
	const KatModule *module_;
	const Hypotheses *hyps_;
	SearchOptions opts_;
	bool verbose_;
	unsigned holding_ = 0;
	unsigned failing_ = 0;
	unsigned unchecked_ = 0;
};

auto noExtra(Graph &g, Semantics & /*sem*/) -> Term { return Term::constant(g.ctx(), true); }

} // namespace

auto validateExport(const std::string &file, const SearchOptions &opts, bool verbose) -> bool
{
	ParsingDriver driver;
	if (driver.parse(file) != 0)
		return false;
	auto module = driver.takeModule();
	auto hyps = takeHypotheses(*module);
	auto before = takeDefinitions(*module);
	const auto &theory = module->getTheory();

	module->getAssumptions().incorporateInto(module->getTheory());
	Checker checker(*module, {.parallel = false});
	std::vector<Claim> claims;
	checker.setObserver([&](const Constraint &c, const Checker::InclusionResult &r) {
		Claim claim{.constraint = c.clone(), .temporaries = {}, .holds = r.result};
		for (const auto &a : module->getAssumptions())
			if (a->isTemporary())
				claim.temporaries.push_back(a->getConstraint()->clone());
		claims.push_back(std::move(claim));
	});

	/* Export into a scratch directory: only the module's rewriting matters here */
	auto dir = std::filesystem::temp_directory_path() /
		   ("kater-oracle-export-" + std::to_string(getpid()));
	std::filesystem::create_directories(dir);
	Config conf{};
	conf.generate = true;
	conf.name = std::filesystem::path(file).stem().string();
	conf.dir = dir.string();
	Exporter exporter(*module, checker, conf);
	auto exported = exporter.exportCode();
	std::filesystem::remove_all(dir);
	if (!exported) {
		std::cout << file << ": the export failed\n";
		return false;
	}

	Validator v(*module, hyps, opts, verbose);

	/* What the Checker claimed on the way */
	for (const auto &claim : claims) {
		if (!claim.holds)
			continue;
		v.expectNone(
			"claim " + toString(*claim.constraint, theory),
			[&](Graph &g, Semantics &sem) {
				auto t = Term::constant(g.ctx(), true);
				for (const auto &tmp : claim.temporaries)
					t = t && sem.holds(*tmp);
				return t;
			},
			[&](Graph & /*g*/, Semantics &sem) {
				return !sem.holds(*claim.constraint);
			});
	}

	/* What the exporter rewrote: the definitions, and what the views compute */
	auto after = takeDefinitions(*module);
	auto sameMeaning = [&](const std::string &what, const RegExp &old, const RegExp &now) {
		v.expectNone(what + ": " + toString(old, theory) + "  ~>  " + toString(now, theory),
			     noExtra, [&](Graph & /*g*/, Semantics &sem) {
				     return sem.eval(old).differsFrom(sem.eval(now));
			     });
	};
	for (const auto &[name, re] : after.lets) {
		auto it = before.lets.find(name);
		if (it != before.lets.end() && *it->second != *re)
			sameMeaning("rewrite of " + name, *it->second, *re);
	}
	for (const auto &[name, body] : after.views) {
		auto old = before.views.find(name);
		if (old != before.views.end() && *old->second == *body)
			continue;
		sameMeaning("view " + name, *before.lets.at(name),
			    *viewMeaning(*after.lets.at(name), *body));
	}
	for (auto i = 0U; i < after.exports.size() && i < before.exports.size(); i++) {
		auto olds = exprsOf(before.exports[i].get());
		auto news = exprsOf(after.exports[i].get());
		for (auto k = 0U; k < olds.size() && k < news.size(); k++)
			if (*olds[k] != *news[k])
				sameMeaning("rewrite in an export", *olds[k], *news[k]);
	}

	v.summary(file);
	return v.ok();
}

} // namespace oracle
