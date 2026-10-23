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

#include "Assumptions.hpp"

#include "Constraint.hpp"
#include "Predicate.hpp"
#include "RegExp.hpp"
#include "Statement.hpp"
#include "Theory.hpp"
#include "VSet.hpp"

#include <algorithm>
#include <cassert>
#include <numeric>

auto Assumptions::tryIncorporateDomAssumption(const AssumeStatement *assm, Theory &theory) -> bool
{
	/*
	 * LHS has to be a base relation; RHS a base or a sequence.
	 * (Given the parsing assumption, RHS will be a sequence but this
	 * function can be a bit more generic.)
	 */
	const auto *cst = assm->getConstraint();
	const auto *subsetC = dynamic_cast<const SubsetConstraint *>(cst);
	/* `r & id <= [A];r;[B]` is about the cycles of r alone */
	if (!subsetC || subsetC->sameEnds() || subsetC->rotated() ||
	    !dynamic_cast<const CharRE *>(subsetC->getLHS()) ||
	    (!dynamic_cast<const SeqRE *>(subsetC->getRHS()) &&
	     !dynamic_cast<const CharRE *>(subsetC->getRHS())))
		return false;

	/* Ensure LHS is _just_ a base relation */
	const auto *lhs = dynamic_cast<const CharRE *>(subsetC->getLHS());
	if (!lhs->getLabel().isRelation() || !lhs->getLabel().getPreChecks().empty() ||
	    !lhs->getLabel().getPostChecks().empty())
		return false;

	PredicateSet dom;
	PredicateSet codom;
	/* Extract dom/codom if RHS contains the same base relation */
	if (const auto *rhs = dynamic_cast<const CharRE *>(subsetC->getRHS())) {
		/* If RHS is a base relation, it has to match the LHS */
		if (lhs->getLabel().getRelation() != rhs->getLabel().getRelation())
			return false;
		dom = rhs->getLabel().getPreChecks();
		codom = rhs->getLabel().getPostChecks();
	} else if (const auto *rhs = dynamic_cast<const SeqRE *>(subsetC->getRHS())) {
		/* If RHS is a sequence, it needs to contain exactly one relation */
		auto relIt = std::ranges::find_if(rhs->kids(), [&](auto &re) {
			const auto *charRE = dynamic_cast<const CharRE *>(&*re);
			return charRE &&
			       charRE->getLabel().getRelation() == lhs->getLabel().getRelation();
		});
		if (relIt == rhs->kid_end() ||
		    std::ranges::any_of(rhs->kid_begin(), relIt,
					[&](auto &re) { return !re->isPredicate(); }) ||
		    std::ranges::any_of(relIt + 1, rhs->kid_end(),
					[&](auto &re) { return !re->isPredicate(); }))
			return false;

		dom = std::accumulate(rhs->kid_begin(), relIt, PredicateSet{},
				      [&](auto acc, auto &re) {
					      auto *charRE = dynamic_cast<const CharRE *>(&*re);
					      acc.insert(charRE->getLabel().getPreChecks());
					      return acc;
				      });
		codom = std::accumulate(relIt + 1, rhs->kid_end(), PredicateSet{},
					[&](auto acc, auto &re) {
						auto *charRE = dynamic_cast<const CharRE *>(&*re);
						acc.insert(charRE->getLabel().getPreChecks());
						return acc;
					});
	} else {
		assert(0);
	}

	theory.registerDomain(*lhs->getLabel().getRelation(), dom);
	theory.registerCodomain(*lhs->getLabel().getRelation(), codom);
	return true;
}

auto Assumptions::tryIncorporateIncompatAssumption(const AssumeStatement *assm, Theory &theory)
	-> bool
{
	if (!assm->getConstraint()->isEmpty())
		return false;

	const auto *cst = dynamic_cast<const SubsetConstraint *>(assm->getConstraint());
	if (!dynamic_cast<const SeqRE *>(cst->getLHS()) ||
	    std::ranges::any_of(cst->getLHS()->kids(),
				[&](auto &re) { return !re->isPredicate(); }))
		return false;

	const auto *seqRE = dynamic_cast<const SeqRE *>(cst->getLHS());
	assert(std::ranges::all_of(seqRE->kids(), [](auto &re) {
		return re->isPredicate() &&
		       dynamic_cast<const CharRE *>(&*re)->getLabel().getPreChecks().size() == 1;
	}));

	/* Collect all incompatible predicates */
	auto incompat = std::accumulate(seqRE->kid_begin(), seqRE->kid_end(), VSet<Predicate::ID>{},
					[](auto acc, const auto &re) {
						acc.insert(dynamic_cast<const CharRE *>(&*re)
								   ->getLabel()
								   .getPreChecks()
								   .begin()
								   ->getID());
						return acc;
					});

	/* Should this be incorporates to disjoint preds? */
	if (incompat.size() == 2) {
		theory.registerDisjointPreds(incompat);
	} else {
		/* It's an invalidity assumption */
		theory.registerInvalidPreds(incompat);
	}
	return true;
}

void Assumptions::incorporateInto(Theory &theory)
{
	/*
	 * We can drop assumptions of the following forms:
	 *   - r <= [A];r;[B], where r is some base relation ([A] and [B] are optional)
	 *   - [A;...;B] <= 0
	 */
	auto isDroppable = [&theory](auto &stmtUP) -> bool {
		return tryIncorporateDomAssumption(&*stmtUP, theory) ||
		       tryIncorporateIncompatAssumption(&*stmtUP, theory);
	};

	std::erase_if(assumes_, isDroppable);
}
