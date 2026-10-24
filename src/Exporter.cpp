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

#include "Exporter.hpp"

#include "AdjList.hpp"
#include "Checker.hpp"
#include "Constraint.hpp"
#include "Counterexample.hpp"
#include "GenMCPrinter.hpp"
#include "Logger.hpp"
#include "RegExp.hpp"
#include "RegExpUtils.hpp"
#include "Relation.hpp"
#include "SavedExp.hpp"
#include "Statement.hpp"
#include "Utils.hpp"
#include "VSet.hpp"

#include <algorithm>
#include <cassert>
#include <memory>
#include <numeric>
#include <ranges>
#include <string>
#include <utility>
#include <vector>

#define DEBUG_TYPE "exporter"

/*
 * Checks whether each kid of some MutRecRE is using productive recursive calls.
 * E.g., :
 *  - let rec x = x        => not productive
 *  - let rec x = x? ; po  => productive
 *  - let rec x = y | po
 *        and y = [REL]    => productive (x non productive, y productive)
 *
 * Returns a vector of pairs denoting whether each kid is productive, and its starting rec symbols
 */
auto collectProductiveRecursions(const MutRecRE *re) -> std::vector<std::pair<bool, VSet<Relation>>>
{
	/* Helper lambda to recurse to all kids */
	auto checkProdRec = [&](const RegExp *re, const VSet<Relation> &recs,
				auto &funRef) -> std::pair<bool, VSet<Relation>> {
		if (auto *charRE = dynamic_cast<const CharRE *>(re)) {
			/* [] are non-productive */
			if (charRE->isPredicate())
				return {false, {}};
			/* r in recs is also non productive, because it can only appear at the
			 * leftmost place of composition */
			if (recs.contains(*charRE->getLabel().getRelation()))
				return {false, {*charRE->getLabel().getRelation()}};
			/* all other relations are productive */
			return {true, {}};
		}
		/* r?, r* are non-productive */
		auto *qmarkRE = dynamic_cast<const QMarkRE *>(re);
		auto *starRE = dynamic_cast<const StarRE *>(re);
		if (qmarkRE || starRE) {
			return {false, funRef(re->getKid(0), recs, funRef).second};
		}
		/* r=r1;...;rn is productive if tail(r) is productive */
		if (auto *seqRE = dynamic_cast<const SeqRE *>(re)) {
			assert(seqRE->getNumKids() > 1);
			auto tailProductive =
				std::any_of(seqRE->kid_begin() + 1, seqRE->kid_end(), [&](auto &k) {
					return funRef(&*k, recs, funRef).first;
				});
			return {tailProductive, funRef(seqRE->getKid(0), recs, funRef).second};
		}

		/* In all other cases, just accumulate kid results */
		return std::accumulate(
			re->kid_begin(), re->kid_end(), std::pair<bool, VSet<Relation>>(true, {}),
			[&](auto acc, auto &elem) {
				auto result = funRef(&*elem, recs, funRef);
				if (!result.first)
					acc.second.insert(result.second);
				return std::make_pair(acc.first && result.first, acc.second);
			});
	};

	auto recs = re->recs();
	VSet<Relation> rels(std::ranges::begin(recs), std::ranges::end(recs));
	return std::accumulate(re->kid_begin(), re->kid_end(),
			       std::vector<std::pair<bool, VSet<Relation>>>(),
			       [&](auto acc, auto &elem) {
				       acc.push_back(checkProdRec(&*elem, rels, checkProdRec));
				       return std::move(acc);
			       });
}

/*
 * Returns a "call-graph" of productive calls:
 *  whenever a recursive relation X non-productively calls Y (see checkProductiveRecusion),
 *  the graph contains an edge Y->X
 */
auto constructRecCallGraph(const MutRecRE *re) -> AdjList<Relation, RelationHasher>
{
	auto recs = re->recs();
	std::vector<Relation> rels(std::ranges::begin(recs), std::ranges::end(recs));
	AdjList<Relation, RelationHasher> graph(rels);
	auto i = 0U;
	for (auto &[prod, starting] : collectProductiveRecursions(re)) {
		if (!prod) {
			for (auto &rel : starting)
				graph.addEdge(rel, re->getRec(i));
		}
		i++;
	}
	return graph;
}

auto containsMandatoryRegistrations(const KatModule &module) -> bool
{
	auto ppo = module.getPPODeclaration();
	if (!ppo) {
		LOG(VerbosityLevel::Error) << "no top-level 'ppo' definition provided";
		return false;
	}
	auto hb = module.getHBDeclaration();
	if (!hb) {
		LOG(VerbosityLevel::Error) << "no top-level 'hb' definition provided";
		return false;
	}
	if (!dynamic_cast<const ViewExp *>(hb->getSaved())) {
		LOG_AT(VerbosityLevel::Error, hb->getDbgInfo())
			<< "'hb' must be stored in a view\n"
			   "  note: declare it as \"view hb = ...\" instead of \"let hb = ...\"";
		return false;
	}
	auto coh = module.getCOHDeclaration();
	if (!coh) {
		LOG(VerbosityLevel::Error) << "no coherence constraint provided";
		return false;
	}
	if (!dynamic_cast<const ViewExp *>(coh->getSaved())) {
		LOG_AT(VerbosityLevel::Error, coh->getDbgInfo())
			<< "coherence constraint must take a view argument";
		return false;
	}
	return true;
}

/**
 * Ensure that all saved relations are included in pporf and are transitive.
 * For mutually recursive relations: Check that some possible export order exists */
auto Exporter::checkSavedRelsExportRequirements(const RegExp &pporf) -> bool
{
	auto status = true;
	auto &module = getModule();
	const auto *ppo = module.getPPODeclaration()->getRE();
	for (auto &let : module.lets()) {
		if (dynamic_cast<const NoSavedExp *>(let->getSaved()) != nullptr)
			continue;

		const auto *view = dynamic_cast<const ViewExp *>(let->getSaved());
		const auto *mutRec = dynamic_cast<const MutRecRE *>(let->getRE());

		auto require = [&](std::unique_ptr<Constraint> cst, const char *what) -> bool {
			auto result = getChecker().checkAssertion(*cst);
			if (result.result)
				return true;
			LOG_AT(VerbosityLevel::Error, let->getDbgInfo())
				<< what << ": " << WithTheory(*let->getRE(), getTheory())
				<< cexNote(result.cex, getTheory());
			return false;
		};

		if (view == nullptr)
			status &= require(SubsetConstraint::create(let->getRE()->clone(),
								   StarRE::createOpt(pporf.clone()),
								   false, false),
					  "saved relation not included in pporf");
		else
			status &= require(
				SubsetConstraint::create(
					let->getRE()->clone(),
					AltRE::createOpt(StarRE::createOpt(module.createPORF()),
							 RegExp::createId()),
					false, false),
				"view not included in porf | id");

		// FIXME: prefix should be the reduced RE if we ever allow custom reductions
		status &= require(SubsetConstraint::createOpt(
					  SeqRE::createOpt(ppo->clone(), let->getRE()->clone()),
					  let->getRE()->clone(), false, false),
				  "reduced relation not transitive");

		/* For mutually recursive views, check that we can export them in some order
		 */
		if (view != nullptr && mutRec != nullptr) {
			if (!constructRecCallGraph(mutRec).transClosure().isIrreflexive()) {
				LOG_AT(VerbosityLevel::Error, let->getDbgInfo())
					<< "could not resolve view calculation order: "
					<< WithTheory(*let->getRE(), getTheory());
				status = false;
			}
		}
	}
	return status;
}

auto Exporter::checkExportRequirements() -> bool
{
	auto &module = getModule();

	if (!containsMandatoryRegistrations(module))
		return false;

	/* Ensure that pporf is implied by the acyclicity constraints */
	auto pporf = module.createPPORF();
	auto acycsView =
		module.exports() | std::views::filter([&](auto &stmt) {
			return dynamic_cast<const AcyclicConstraint *>(stmt->getConstraint());
		}) |
		std::views::transform([&](auto &stmt) {
			return dynamic_cast<const AcyclicConstraint *>(stmt->getConstraint());
		});
	auto acycDisj = std::accumulate(acycsView.begin(), acycsView.end(), RegExp::createFalse(),
					[&](auto re1, auto *acyc) {
						return AltRE::createOpt(re1->clone(),
									acyc->getRE()->clone());
					});
	auto noOOTA = SubsetConstraint::create(
		pporf->clone(), StarRE::createOpt(std::move(acycDisj)), false, false);
	auto [status, cex] = getChecker().checkAssertion(*noOOTA);
	if (!status) {
		LOG(VerbosityLevel::Warning)
			<< "acyclicity constraints do not preclude OOTA" << note
			<< "OOTA has to be enforced by the model checker"
			<< cexNote(cex, getTheory());
		status = true; /* treat as a soft error */
	}

	/* Check extensibility: GenMC can add an event to a consistent graph
	 * without breaking a constraint (doc/verification.md). Of an export
	 * the model says is not extensible, only warn */
	for (auto &stmt : module.exports()) {
		const auto *cst = stmt->getConstraint();
		const auto *acyc = dynamic_cast<const AcyclicConstraint *>(cst);
		const auto *coh = dynamic_cast<const CoherenceConstraint *>(cst);
		if (acyc == nullptr && coh == nullptr) {
			if (stmt->isNonExtensible())
				LOG_AT(VerbosityLevel::Warning, stmt->getDbgInfo())
					<< "nonextensible means nothing for "
					<< WithTheory(*cst, getTheory());
			continue;
		}
		auto [ok, cex] = acyc != nullptr ? getChecker().isPPOIntersectionInPPO(acyc)
						 : getChecker().isCoherenceExtensible(coh);
		if (ok) {
			if (stmt->isNonExtensible())
				LOG_AT(VerbosityLevel::Warning, stmt->getDbgInfo())
					<< "declared nonextensible, but Kater shows it extensible: "
					<< WithTheory(*cst, getTheory());
			continue;
		}
		LOG_AT(stmt->isNonExtensible() ? VerbosityLevel::Warning : VerbosityLevel::Error,
		       stmt->getDbgInfo())
			<< "not extensible: a cycle of " << WithTheory(*cst, getTheory())
			<< " may leave an event GenMC adds by a step that is not pporf" << note
			<< "the counterexample reads the cycle from the event"
			<< cexNote(cex, getTheory());
		status &= stmt->isNonExtensible();
	}

	/* Check correctness of "unless" clauses in acyclicity constraints */
	for (auto &stmt : module.exports()) {
		auto *currentCst = dynamic_cast<const AcyclicConstraint *>(stmt->getConstraint());
		if (!currentCst || !stmt->getUnless())
			continue;

		/* A: all acyclicity constraints */
		auto acycDisj = std::accumulate(acycsView.begin(), acycsView.end(),
						RegExp::createFalse(), [&](auto re1, auto *ac) {
							return AltRE::createOpt(
								re1->clone(), ac->getRE()->clone());
						});
		/* A_R: acyclicity constraints w/o the current one */
		auto acycDisjRest = std::accumulate(
			acycsView.begin(), acycsView.end(), RegExp::createFalse(),
			[&](auto re1, auto *ac) {
				return *ac->getRE() == *currentCst->getRE()
					       ? std::move(re1)
					       : AltRE::createOpt(re1->clone(),
								  ac->getRE()->clone());
			});

		/* A <= A_R | id; the id case is sound only if A is irreflexive */
		module.getAssumptions().add(
			AssumeStatement::create(stmt->getUnless()->clone(), true));
		auto unlessOK = SubsetConstraint::create(
			std::move(acycDisj),
			AltRE::createOpt(std::move(acycDisjRest), RegExp::createId()), false,
			false);
		auto [unlessStatus, cex] = getChecker().checkAssertion(*unlessOK);
		if (!unlessStatus) {
			LOG_AT(VerbosityLevel::Error, stmt->getDbgInfo())
				<< "\"unless\" clause does not imply acyclicity constraint: "
				<< WithTheory(*currentCst, getTheory())
				<< cexNote(cex, getTheory());
			status = false;
		}
		module.getAssumptions().clearTemporary();
	}

	if (!checkSavedRelsExportRequirements(*pporf))
		status = false;
	return status;
}

/* Helper function that, given an expression r ~ A | C;b+ applies FUN to b+ */
template <typename F> void foreachTrailingTransBuiltin(std::unique_ptr<RegExp> &reUP, F &&fun)
{
	if (auto *charRE = dynamic_cast<const CharRE *>(&*reUP))
		return;

	/* If r ~ A | B or r ~ A? or r ~ A* or r ~ r;A, recurse to kids */
	auto *qmarkRE = dynamic_cast<const QMarkRE *>(&*reUP);
	auto *altRE = dynamic_cast<const AltRE *>(&*reUP);
	auto *starRE = dynamic_cast<const StarRE *>(&*reUP);
	auto *mutRecRE = dynamic_cast<const MutRecRE *>(&*reUP);
	if (qmarkRE || altRE || starRE || mutRecRE) {
		for (auto &kRE : reUP->kids())
			foreachTrailingTransBuiltin(kRE, fun);
		return;
	}

	/* If r ~ A;...;C recurse to C */
	if (auto *seqRE = dynamic_cast<const SeqRE *>(&*reUP)) {
		foreachTrailingTransBuiltin(reUP->getKid(reUP->getNumKids() - 1), fun);
		return;
	}

	/* If r ~ B+ apply FUN if B is builtin; recurse otherwise */
	auto *plusRE = dynamic_cast<const PlusRE *>(&*reUP);
	assert(plusRE);
	if (auto *charRE = dynamic_cast<const CharRE *>(plusRE->getKid(0))) {
		if (charRE->isRelation() && charRE->getLabel().getRelation()->isBuiltin())
			fun(reUP);
		return;
	}
	foreachTrailingTransBuiltin(reUP->getKid(0), fun);
}

/*
 * Given the definition of a recursive expression r,
 * returns all builtins b such that r ~ r?;A;...;b+
 * Quits if r is not of the form r ~ r1;A;...;b+ | ... | rN;A;...;b+
 */
auto collectTrailingTransBuiltins(Relation rel, std::unique_ptr<RegExp> &re)
	-> VSet<std::unique_ptr<CharRE>>
{
	/* Helper function to determine whether we should collect trailing builtins */
	auto collectSeqREs = [&](std::unique_ptr<RegExp> &re) {
		std::vector<const SeqRE *> res;
		if (auto *seqRE = dynamic_cast<const SeqRE *>(&*re)) {
			res.push_back(seqRE);
			return res;
		}
		auto *altRE = dynamic_cast<const AltRE *>(&*re);
		if (!altRE || std::ranges::any_of(altRE->kids(), [](auto &kid) {
			    return !dynamic_cast<const SeqRE *>(&*kid);
		    }))
			return res;
		for (auto &k : altRE->kids())
			res.push_back(dynamic_cast<const SeqRE *>(&*k));
		return res;
	};

	/* If it's not a sequence, quit */
	auto seqs = collectSeqREs(re);
	if (seqs.empty())
		return {};

	/* Otherwise, collect CharRE UPs, as we might want to edit those REs in place later */
	VSet<std::unique_ptr<CharRE>> result;

	/* Helper function that will be applied to collect builtins (re ~ b+) */
	auto collectTrailingFun = [&](std::unique_ptr<RegExp> &re) {
		result.insert(std::unique_ptr<CharRE>(
			dynamic_cast<CharRE *>(re->getKid(0)->clone().release())));
	};

	for (auto *seqRE : seqs) {
		/* If r is a sequence, it has to start with r or r? (i.e., be recursive) */
		if (auto *charRE = dynamic_cast<const CharRE *>(seqRE->getKid(0))) {
			if (charRE->isRelation() && *charRE->getLabel().getRelation() == rel)
				foreachTrailingTransBuiltin(re->getKid(1), collectTrailingFun);
		}
		if (auto *qmarkRE = dynamic_cast<const QMarkRE *>(seqRE->getKid(0))) {
			auto *charRE = dynamic_cast<const CharRE *>(qmarkRE->getKid(0));
			if (charRE && charRE->isRelation() &&
			    *charRE->getLabel().getRelation() == rel)
				foreachTrailingTransBuiltin(re->getKid(1), collectTrailingFun);
		}
	}
	return result;
}

static void warnNonIncrementalView(const LetStatement &let, const RegExp *builtin,
				   const Theory &theory)
{
	auto reason = builtin != nullptr ? "it is not closed under " + toString(*builtin, theory)
					 : std::string("it does not end in a transitive relation");
	LOG_AT(VerbosityLevel::Warning, let.getDbgInfo())
		<< "view '" << let.getName() << "' cannot be computed incrementally: " << reason
		<< note
		<< "the generated checker will walk the whole chain for every event, which is "
		   "quadratic in the thread length";
}

void Exporter::optimizeModuleForExport()
{
	auto &module = getModule();
	auto &theory = module.getTheory();

	/* Calculate export order for views */
	// FIXME: When we update to C++23, consider chunk_by()
	auto svars = module.lets();
	for (auto it = svars.begin(), ie = svars.end(); it != ie; ++it) {
		if (!dynamic_cast<const MutRecRE *>((*it)->getRE())) {
			continue;
		}

		auto prevIt = it;
		auto *mutRecRE = dynamic_cast<const MutRecRE *>((*it)->getRE());
		auto recs = mutRecRE->recs();
		auto graph = constructRecCallGraph(mutRecRE).transClosure();
		while (it != ie && dynamic_cast<const MutRecRE *>((*it)->getRE()) &&
		       std::ranges::find(recs, dynamic_cast<const MutRecRE *>((*it)->getRE())
						       ->getRelation()) != recs.end()) {
			++it;
		}
		std::sort(prevIt, it, [&](auto &let1, auto &let2) {
			auto rel1 = dynamic_cast<const MutRecRE *>(let1->getRE())->getRelation();
			auto rel2 = dynamic_cast<const MutRecRE *>(let2->getRE())->getRelation();
			return graph(rel1, rel2);
		});
		--it;
	}

	/* Optimize calculation for transitive views */
	for (auto &let : module.lets()) {
		auto *plusRE = dynamic_cast<const PlusRE *>(let->getRE());
		if (!plusRE || !dynamic_cast<const ViewExp *>(let->getSaved())) {
			continue;
		}

		auto rel = Relation::createUser();
		theory.registerRelation(
			rel, RelationInfo{.name = let->getName(), .dbg = let->getDbgInfo()});
		auto newViewRE =
			SeqRE::createOpt(QMarkRE::createOpt(CharRE::create(TransLabel(rel))),
					 plusRE->getKid(0)->clone());
		std::vector<std::unique_ptr<RegExp>> defs;
		defs.emplace_back(newViewRE->clone());
		auto newRE = MutRecRE::createOpt(rel, {rel}, std::move(defs));
		LOG_AT(VerbosityLevel::Note, let->getDbgInfo())
			<< "rewriting transitive view '" << let->getName()
			<< "' as a recursive definition" << note
			<< "before: " << WithTheory(*let->getRE(), theory) << note
			<< "after:  " << WithTheory(*newRE, theory);

		auto oldRE = plusRE->clone(); // copy so that it doesn't get replaced in place
		module.replaceAllUsesWith(&*oldRE, &*newRE);
		for (auto &let : module.lets()) {
			auto *viewExp = dynamic_cast<ViewExp *>(let->getSaved());
			if (!viewExp)
				continue;
			if (*viewExp->getRE() == *newRE)
				viewExp->setRE(newViewRE->clone());
		}
	}

	/* Replace builtins with their transitive counterparts for more efficient codegen */
	auto oldPo = module.getRegisteredRE("po")->clone();
	auto newPo = PlusRE::createOpt(module.getRegisteredRE("po-imm")->clone());
	auto oldPoloc = module.getRegisteredRE("po-loc")->clone();
	auto newPoloc = PlusRE::createOpt(module.getRegisteredRE("po-loc-imm")->clone());
	auto oldMo = module.getRegisteredRE("mo")->clone();
	auto newMo = PlusRE::createOpt(module.getRegisteredRE("mo-imm")->clone());
	auto oldFr = module.getRegisteredRE("fr")->clone();
	auto newFr = SeqRE::createOpt(module.getRegisteredRE("fr-imm")->clone(),
				      StarRE::createOpt(module.getRegisteredRE("mo-imm")->clone()));
	auto oldRmw = module.getRegisteredRE("rmw")->clone();
	auto newRmw = SeqRE::createOpt(module.getRegisteredRE("UR")->clone(),
				       module.getRegisteredRE("po-imm")->clone(),
				       module.getRegisteredRE("UW")->clone());
	module.replaceAllUsesWith(&*oldPo, &*newPo);
	module.replaceAllUsesWith(&*oldPoloc, &*newPoloc);
	module.replaceAllUsesWith(&*oldMo, &*newMo);
	module.replaceAllUsesWith(&*oldFr, &*newFr);
	module.replaceAllUsesWith(&*oldRmw, &*newRmw);

	makeViewsIncremental();
}

/*
 * Rewrites each recursive view to step along an immediate relation where it is
 * closed under it, so that the generated calculation does not re-walk the whole
 * transitive chain for every event.
 */
void Exporter::makeViewsIncremental()
{
	auto &module = getModule();
	auto &theory = module.getTheory();

	for (auto &let : module.lets()) {
		auto *mutRecRE = dynamic_cast<MutRecRE *>(let->getRE());
		auto *viewExp = dynamic_cast<ViewExp *>(let->getSaved());
		if (!mutRecRE || !viewExp) {
			continue;
		}

		/* Helper function to check if a relation is closed w.r.t. some builtin */
		auto isRecREClosedWRTBuiltin = [&](const auto &builtinRE) -> bool {
			auto recBuiltin = SeqRE::createOpt(mutRecRE->clone(), builtinRE->clone());
			auto recBuiltinInRec = SubsetConstraint::create(
				std::move(recBuiltin), mutRecRE->clone(), false, false);
			return getChecker().checkAssertion(*recBuiltinInRec).result;
		};

		/* Get the respective recursive def */
		std::vector<std::pair<std::unique_ptr<RegExp>, std::unique_ptr<RegExp>>> toRepl;
		auto builtins =
			collectTrailingTransBuiltins(mutRecRE->getRelation(), viewExp->getRERef());
		if (builtins.empty())
			warnNonIncrementalView(*let, nullptr, theory);
		for (const auto &builtinRE : builtins) {
			if (!isRecREClosedWRTBuiltin(builtinRE)) {
				warnNonIncrementalView(*let, &*builtinRE, theory);
				continue;
			}
			auto newRE = viewExp->getRE()->clone();
			auto toReplaceRE = PlusRE::create(builtinRE->clone());
			foreachTrailingTransBuiltin(newRE, [&](std::unique_ptr<RegExp> &builtin) {
				replaceREWith(builtin, &*toReplaceRE, &*builtinRE);
			});
			const auto name = toString(*builtinRE, theory);
			LOG_AT(VerbosityLevel::Note, let->getDbgInfo())
				<< "computing '" << let->getName() << "' along " << name
				<< " instead of its transitive " << name << "+" << note
				<< "before: " << WithTheory(*viewExp->getRE(), theory) << note
				<< "after:  " << WithTheory(*newRE, theory);

			toRepl.emplace_back(viewExp->getRE()->clone(), std::move(newRE));
		}

		for (auto &[from, to] : toRepl)
			module.replaceAllUsesWith(&*from, &*to);
	}
}

auto Exporter::exportCode() -> bool
{
	if (!checkExportRequirements())
		return false;

	optimizeModuleForExport();

	GenMCPrinter p(getModule(), getConf());
	return p.output();
}
