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

#include "Audit.hpp"

#include "ParsingDriver.hpp"
#include "Theory.hpp"
#include "Utils.hpp"

#include <iostream>
#include <vector>

namespace oracle {

namespace {

using RB = Relation::BuiltinID;
using PB = Predicate::BuiltinID;

class Auditor {

public:
	Auditor(const KatModule &module, const SearchOptions &opts, bool verbose)
		: module_(&module), theory_(&module.getTheory()), opts_(opts), verbose_(verbose)
	{
	}

	/* Checks the fact WHAT, which is false in a graph iff VIOLATION holds there */
	void claim(const std::string &what, const Query &violation)
	{
		auto noHypotheses = [](Graph &g, Semantics & /*sem*/) {
			return Term::constant(g.ctx(), true);
		};
		auto s = search(*module_, noHypotheses, violation, opts_);
		switch (s.outcome) {
		case Search::Outcome::NoCounterexample:
			holding_++;
			if (verbose_)
				std::cout << "holds:    " << what << "\n";
			break;
		case Search::Outcome::Counterexample:
			failing_++;
			std::cout << "FALSE:    " << what << "\n" << s.detail;
			break;
		case Search::Outcome::Unsupported:
			unchecked_++;
			if (verbose_)
				std::cout << "skipped:  " << what << " (" << s.detail << ")\n";
			break;
		case Search::Outcome::Unknown:
			unchecked_++;
			std::cout << "unknown:  " << what << " (" << s.detail << ")\n";
			break;
		}
	}

	[[nodiscard]] auto name(const TransLabel &lab) const -> std::string
	{
		return toString(lab, *theory_);
	}
	[[nodiscard]] auto name(const Predicate &p) const -> std::string
	{
		return nameOf(p, theory_);
	}

	void summary() const
	{
		std::cout << "\n"
			  << holding_ << " facts hold, " << failing_ << " are false, " << unchecked_
			  << " were not checked (up to " << opts_.maxEvents << " events)\n";
	}

	[[nodiscard]] auto allHold() const -> bool { return failing_ == 0; }

	[[nodiscard]] auto theory() const -> const Theory & { return *theory_; }

private:
	const KatModule *module_;
	const Theory *theory_;
	SearchOptions opts_;
	bool verbose_;
	unsigned holding_ = 0;
	unsigned failing_ = 0;
	unsigned unchecked_ = 0;
};

auto builtinRelations(const Theory &theory) -> std::vector<Relation>
{
	std::vector<Relation> rels;
	for (auto id = 0; id <= static_cast<int>(RB::any); id++) {
		auto r = Relation::createBuiltin(static_cast<RB>(id));
		if (theory.hasInfo(r)) {
			rels.push_back(r);
			rels.push_back(r.invert());
		}
	}
	return rels;
}

auto builtinPredicates(const Theory &theory) -> std::vector<Predicate>
{
	std::vector<Predicate> preds;
	for (auto id = 0; id <= static_cast<int>(PB::LOC); id++) {
		auto p = Predicate::createBuiltin(static_cast<PB>(id));
		if (theory.hasInfo(p)) {
			preds.push_back(p);
			preds.push_back(p.complement());
		}
	}
	return preds;
}

/* r(i, j) and not s(i, j), for some i, j */
auto notIncluded(const Matrix &r, const Matrix &s) -> Term { return !r.includedIn(s); }

} // namespace

auto audit(const SearchOptions &opts, bool verbose) -> bool
{
	ParsingDriver driver; /* registers the builtins */
	auto module = driver.takeModule();
	Auditor a(*module, opts, verbose);
	const auto &theory = a.theory();

	auto rels = builtinRelations(theory);
	auto preds = builtinPredicates(theory);

	/* Inclusions between relations, as Theory::isIncludedIn answers them */
	for (const auto &r1 : rels) {
		for (const auto &r2 : rels) {
			if (r1 == r2 || !theory.isIncludedIn(r1, r2))
				continue;
			a.claim(a.name(TransLabel(r1)) + " <= " + a.name(TransLabel(r2)),
				[&](Graph & /*g*/, Semantics &sem) {
					return notIncluded(sem.eval(r1), sem.eval(r2));
				});
		}
	}

	/* Domains and codomains */
	for (const auto &r : rels) {
		const auto &dom = theory.getDomain(r);
		const auto &codom = theory.getCodomain(r);
		if (dom.empty() && codom.empty())
			continue;
		a.claim(a.name(TransLabel(r)) + " <= " + a.name(TransLabel(r, dom, codom)),
			[&](Graph & /*g*/, Semantics &sem) {
				return notIncluded(sem.eval(TransLabel(r)),
						   sem.eval(TransLabel(r, dom, codom)));
			});
	}

	/* Inclusions between predicates, and the pairs that do not compose */
	for (const auto &p1 : preds) {
		for (const auto &p2 : preds) {
			if (p1 == p2)
				continue;
			if (theory.isIncludedIn(p1, p2))
				a.claim("[" + a.name(p1) + "] <= [" + a.name(p2) + "]",
					[&](Graph &g, Semantics &sem) {
						std::vector<Term> bad;
						for (auto e = 0U; e < g.size(); e++)
							bad.push_back(sem.eval(p1, e) &&
								      !sem.eval(p2, e));
						return anyOf(g.ctx(), bad);
					});
			if (p1 < p2 && !theory.composes(PredicateSet{p1}, PredicateSet{p2}))
				a.claim("[" + a.name(p1) + "] & [" + a.name(p2) + "] = 0",
					[&](Graph &g, Semantics &sem) {
						std::vector<Term> bad;
						for (auto e = 0U; e < g.size(); e++)
							bad.push_back(sem.eval(p1, e) &&
								      sem.eval(p2, e));
						return anyOf(g.ctx(), bad);
					});
		}
	}

	/* Inclusions between whole letters: predicate letters, relation letters,
	 * and relation letters with a check, as the inclusion check compares them */
	std::vector<TransLabel> letters;
	for (const auto &p : preds)
		letters.emplace_back(std::nullopt, PredicateSet{p});
	for (const auto &r : rels) {
		letters.emplace_back(r);
		letters.emplace_back(r, PredicateSet{Predicate::createBuiltin(PB::R)});
		letters.emplace_back(r, PredicateSet{},
				     PredicateSet{Predicate::createBuiltin(PB::W)});
	}
	for (const auto &l1 : letters) {
		for (const auto &l2 : letters) {
			if (l1 == l2 || !theory.isIncludedIn(l1, l2))
				continue;
			/* The inclusions of relations alone are checked above */
			if (l1.isRelation() && l2.isRelation() && !l1.hasPreChecks() &&
			    !l1.hasPostChecks() && !l2.hasPreChecks() && !l2.hasPostChecks())
				continue;
			a.claim("letter " + a.name(l1) + " <= " + a.name(l2),
				[&](Graph & /*g*/, Semantics &sem) {
					return notIncluded(sem.eval(l1), sem.eval(l2));
				});
		}
	}

	/* Labels that do not compose: relation;relation, relation;[p] and [p];relation */
	auto emptyComposition = [&](const TransLabel &l1, const TransLabel &l2) {
		if (theory.composes(l1, l2))
			return;
		a.claim(a.name(l1) + " ; " + a.name(l2) + " = 0",
			[&](Graph & /*g*/, Semantics &sem) {
				return !sem.eval(l1).compose(sem.eval(l2)).isEmpty();
			});
	};
	for (const auto &r1 : rels) {
		for (const auto &r2 : rels)
			emptyComposition(TransLabel(r1), TransLabel(r2));
		for (const auto &p : preds) {
			emptyComposition(TransLabel(r1), TransLabel(std::nullopt, {p}));
			emptyComposition(TransLabel(std::nullopt, {p}), TransLabel(r1));
		}
	}

	/* The relations Kater treats as eco keep the location */
	for (const auto &r : rels) {
		if (!theory.isEco(TransLabel(r)))
			continue;
		a.claim(a.name(TransLabel(r)) + " is eco: <= (rf | mo | fr) & loc",
			[&](Graph &g, Semantics &sem) {
				auto eco =
					sem.eval(Relation::createBuiltin(RB::rf))
						.unite(sem.eval(Relation::createBuiltin(RB::mo)))
						.unite(sem.eval(Relation::createBuiltin(RB::fr)));
				auto ecoInv = eco.transpose();
				auto target = r.isInverse() ? ecoInv : eco;
				return notIncluded(sem.eval(r),
						   target.intersect(g.sameLocRelation()));
			});
	}

	/* Per-location variants: saturateLoc swaps R for its variant on R & loc */
	for (const auto &r : rels) {
		if (!theory.hasPerLoc(TransLabel(r)))
			continue;
		auto rloc = theory.getPerLoc(r);
		if (r.isInverse())
			rloc.invert();
		a.claim(a.name(TransLabel(r)) + " & loc <= " + a.name(TransLabel(rloc)),
			[&](Graph &g, Semantics &sem) {
				return notIncluded(sem.eval(r).intersect(g.sameLocRelation()),
						   sem.eval(rloc));
			});
	}

	/* The built-in assumptions */
	for (const auto &assm : module->getAssumptions()) {
		a.claim("assume " + toString(*assm->getConstraint(), theory),
			[&](Graph & /*g*/, Semantics &sem) {
				return !sem.holds(*assm->getConstraint());
			});
	}

	a.summary();
	return a.allHold();
}

} // namespace oracle
