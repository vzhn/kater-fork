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

#include "Theory.hpp"

#include "Predicate.hpp"
#include "Relation.hpp"

#include <ranges>
#include <string>

auto nameOf(const Relation &rel, const Theory *theory) -> std::string
{
	auto name = theory != nullptr && theory->hasInfo(rel) ? theory->getInfo(rel).name
							      : "$" + std::to_string(rel.getID());
	return rel.isInverse() ? name + "^-1" : name;
}

auto nameOf(const Predicate &pred, const Theory *theory) -> std::string
{
	auto name = theory != nullptr && theory->hasInfo(pred) ? theory->getInfo(pred).name
							       : "#" + std::to_string(pred.getID());
	return pred.isComplement() ? "~" + name : name;
}

auto Theory::isEco(const TransLabel &label) const -> bool
{
	if (label.isPredicate())
		return false;

	auto rel = *label.getRelation();
	return isIncludedIn(rel, Relation::createBuiltin(Relation::BuiltinID::rf)) ||
	       isIncludedIn(rel, Relation::createBuiltin(Relation::BuiltinID::mo)) ||
	       isIncludedIn(rel, Relation::createBuiltin(Relation::BuiltinID::fr));
}

/* formal: begin RelationInclusion, mirrored by formal/KaterCert/Builtin.lean */
auto Theory::isIncludedIn(const Relation &a, const Relation &b) const -> bool
{
	using RB = Relation::BuiltinID;

	if (a == b) {
		return true;
	}

	/* r <= any */
	if (b.isBuiltin() && b.toBuiltin() == RB::any) {
		return true;
	}
	if (a.isBuiltin() && a.toBuiltin() == RB::any) {
		return false;
	}

	/* flipped? */
	if (a.isInverse() != b.isInverse()) {
		return false;
	}

	/* r&loc <= r. The variant of po-imm is the exception: po-loc-imm is the
	 * next event on the same location, which need not be the next event */
	if (hasPerLoc(b) && getPerLoc(b) == a && !(b.isBuiltin() && b.toBuiltin() == RB::po_imm)) {
		return true;
	}

	/* special cases for builtins */
	if (!a.isBuiltin() || !b.isBuiltin()) {
		return false;
	}

	auto lb = a.toBuiltin();
	auto rb = b.toBuiltin();

	/* rfe, rfi <= rf */
	if (rb == RB::rf && (lb == RB::rfi || lb == RB::rfe)) {
		return true;
	}
	/* moe, moi, mo_imm <= mo */
	if (rb == RB::mo && (lb == RB::moi || lb == RB::moe || lb == RB::mo_imm)) {
		return true;
	}
	/* fre, fri, fr_imm <= fr */
	if (rb == RB::fr && (lb == RB::fri || lb == RB::fre || lb == RB::fr_imm)) {
		return true;
	}

	/* The relations within a thread are in po. Those that keep the location
	 * (rfi, moi, fri, detour, rmw, po-loc-imm) are in po-loc too; the
	 * dependencies and po-imm are not */
	const auto withinPo = RB::WithinPoBegin <= lb && lb <= RB::WithinPoLast;
	if (rb == RB::po && withinPo) {
		return true;
	}
	if (rb == RB::po_loc && withinPo && hasInfo(a) &&
	    getInfo(a).locInfo == RelLocInfo::KeepsLoc) {
		return true;
	}
	return false;
}
/* formal: end RelationInclusion */

/* formal: begin LetterInclusion, mirrored by formal/KaterCert/Theory.lean */
auto Theory::isIncludedIn(const Predicate &a, const Predicate &b) const -> bool
{
	return a == b ||
	       (!a.isComplement() && !b.isComplement() && isSubPredOf(a.getID(), b.getID())) ||
	       (a.isComplement() && b.isComplement() && isSubPredOf(b.getID(), a.getID()));
}

auto Theory::isIncludedIn(const PredicateSet &a, const PredicateSet &b) const -> bool
{
	/* [...] <= [] */
	if (b.empty())
		return true;
	if (a.empty())
		return false;

	/* Otherwise, A has to be more specific than B */
	namespace RG = std::ranges;
	return a.contains(b) || RG::all_of(b.preds(), [&](auto &bp) {
		       /* Each predicate of B needs to have a more specific one in A */
		       return RG::find_if(a.preds(), [&](auto &ap) {
				      return isIncludedIn(ap, bp);
			      }) != a.end();
	       });
}

auto Theory::isIncludedIn(const TransLabel &a, const TransLabel &b) const -> bool
{
	/* A predicate relates events to themselves, which, of the relations,
	 * only `any` is sure to do: [R] is not within po */
	auto relationIncluded = [&] {
		if (a.isRelation())
			return b.isRelation() && isIncludedIn(*a.getRelation(), *b.getRelation());
		return b.isPredicate() ||
		       (b.getRelation()->isBuiltin() &&
			b.getRelation()->toBuiltin() == Relation::BuiltinID::any);
	};
	return isIncludedIn(a.getPreChecks(), b.getPreChecks()) && relationIncluded() &&
	       isIncludedIn(a.getPostChecks(), b.getPostChecks());
}
/* formal: end LetterInclusion */

auto Theory::composes(const PredicateSet &preds1, const PredicateSet &preds2) const -> bool
{
	if (preds1.empty() || preds2.empty())
		return true;
	if (preds1 == preds2)
		return true;
	/* Whether exists p1 in PREDS1 and p2 in PREDS2 s.t. p1 = ~p2 */
	for (const auto &p1 : preds1) {
		for (const auto &p2 : preds2) {
			if (p1.getID() == p2.getID() && p1.isComplement() != p2.isComplement())
				return false;
		}
	}

	/* Whether PREDS contains any pair (p1,p2) s.t. p1 in PREDS1 and p2 in PREDS2 */
	auto hasPairFun = [&](const VSet<Predicate::ID> &preds) {
		for (const auto &p1 : preds1) {
			for (const auto &p2 : preds2) {
				if (p1.getID() != p2.getID() && !p1.isComplement() &&
				    !p2.isComplement() && preds.contains(p1.getID()) &&
				    preds.contains(p2.getID()))
					return true;
			}
		}
		return false;
	};
	if (std::ranges::any_of(disjointPreds_, hasPairFun))
		return false;

	/* Whether the combination has been declared invalid */
	VSet<Predicate::ID> combo;
	for (const auto &p1 : preds1)
		combo.insert(p1.getID());
	for (const auto &p2 : preds2)
		combo.insert(p2.getID());
	return isValid(combo);
}

auto Theory::composes(const TransLabel &a, const TransLabel &b) const -> bool
{
	// Should we register relations w/ domains builtin and simplify to below?
	// Then we would only have to saturate user-provided relations.
	//
	// return a.isPredicate() ?
	//        composes(a.getPreChecks(), b.getPreChecks()) :
	//        composes(a.getPostChecks(), b.getPreChecks());

	if (a.isPredicate() && b.isPredicate())
		return composes(a.getPreChecks(), b.getPreChecks());

	if (!a.isPredicate() && b.isPredicate()) {
		return composes(a.getPostChecks(), b.getPreChecks()) &&
		       (!hasInfo(*a.getRelation()) ||
			composes(getCodomain(*a.getRelation()), b.getPreChecks()));
	}

	if (a.isPredicate() && !b.isPredicate()) {
		return composes(a.getPreChecks(), b.getPreChecks()) &&
		       (!hasInfo(*b.getRelation()) ||
			composes(a.getPreChecks(), getDomain(*b.getRelation())));
	}

	return composes(a.getPostChecks(), b.getPreChecks()) &&
	       (!hasInfo(*a.getRelation()) ||
		(composes(getCodomain(*a.getRelation()), b.getPreChecks()) &&
		 (!hasInfo(*b.getRelation()) ||
		  composes(getCodomain(*a.getRelation()), getDomain(*b.getRelation()))))) &&
	       (!hasInfo(*b.getRelation()) ||
		composes(a.getPostChecks(), getDomain(*b.getRelation())));
}
