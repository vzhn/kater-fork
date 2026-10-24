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

#ifndef KATER_THEORY_HPP
#define KATER_THEORY_HPP

#include "Predicate.hpp"
#include "Relation.hpp"
#include "TransLabel.hpp"
#include "VSet.hpp"

#include <cassert>
#include <ranges>

/*
 * Represents the structural knowledge about a model's relations and
 * predicates: their names, domains and codomains, per-location variants,
 * which predicates include or exclude one another, and which relations
 * are included in which.
 *
 * Every answer the Theory gives is a hypothesis the decision procedure
 * builds on, so this is part of the trusted base. Hypotheses stated as
 * constraints between expressions live in Assumptions instead.
 *
 *  - A Theory object could hold knowledge taken from different
 *    modules, if we ever decide to support this (currently a single
 *    module is supported).
 */
class Theory {

public:
	/** Creates an empty theory */
	Theory() = default;

	[[nodiscard]] auto relations() const { return std::ranges::ref_view(relations_); }

	void registerRelation(Relation r, RelationInfo info)
	{
		relations_[r.getID()] = std::move(info);
	}

	void registerPerLocPair(Relation r, Relation rloc) { perlocs_.insert({r.getID(), rloc}); }

	[[nodiscard]] auto getPerLoc(Relation r) const -> Relation
	{
		assert(hasPerLoc(r));
		return perlocs_.find(r.getID())->second;
	}
	[[nodiscard]] auto getPerLoc(const TransLabel &lab) const -> Relation
	{
		return getPerLoc(*lab.getRelation());
	}

	[[nodiscard]] auto hasPerLoc(Relation r) const -> bool
	{
		return perlocs_.contains(r.getID());
	}
	[[nodiscard]] auto hasPerLoc(const TransLabel &lab) const -> bool
	{
		return lab.isRelation() && perlocs_.contains(lab.getRelation()->getID());
	}

	void registerPredicate(Predicate p, PredicateInfo info)
	{
		predicates_[p.getID()] = std::move(info);
	}

	/* The domain of r^-1 is the codomain of r, as getDomain reads it */
	void registerDomain(Relation r, PredicateSet dom)
	{
		assert(relations_.contains(r.getID()));
		auto &info = relations_[r.getID()];
		(r.isInverse() ? info.codom : info.dom).insert(dom);
	}

	/* The codomain of r^-1 is the domain of r, as getCodomain reads it */
	void registerCodomain(Relation r, PredicateSet codom)
	{
		assert(relations_.contains(r.getID()));
		auto &info = relations_[r.getID()];
		(r.isInverse() ? info.dom : info.codom).insert(codom);
	}

	void registerDisjointPreds(VSet<Predicate::ID> preds)
	{
		disjointPreds_.insert(preds);

		/* ∀ b ∈ preds, ∀ a ⊆ b: disjoint((preds \ {b}) ∪ a) */
		namespace RV = std::ranges::views;
		for (const auto &subsetKV : subsetPreds_) {
			for (auto &b : preds | RV::filter([&](auto &b) {
					       return subsetKV.second.contains(b);
				       })) {
				auto disjNew = preds;
				disjNew.erase(b);
				disjNew.insert(subsetKV.first);
				registerDisjointPreds(std::move(disjNew));
			}
		}
	}

	void registerInvalidPreds(VSet<Predicate::ID> preds)
	{
		if (preds.size() == 2) {
			registerDisjointPreds(preds);
			return;
		}
		invalidPreds_.insert(preds);
	}

	void registerSubsetPair(Predicate::ID a, Predicate::ID b)
	{
		subsetPreds_[a].insert(b);
		/* ∀ disjoint(S) st a ∈ S: disjoint((S \ {a}) ∪ b) */
		for (const auto &disjSet : disjointPreds_) {
			if (disjSet.contains(a)) {
				auto disjNew = disjSet;
				disjNew.erase(a);
				disjNew.insert(b);
				registerDisjointPreds(std::move(disjNew));
			}
		}
	}

	auto isSubPredOf(const Predicate::ID &a, const Predicate::ID &b) const -> bool
	{
		auto pIt = subsetPreds_.find(a);
		return pIt != subsetPreds_.end() && pIt->second.contains(b);
	}

	/** Returns true if A <= B */
	[[nodiscard]] auto isIncludedIn(const Relation &a, const Relation &b) const -> bool;
	[[nodiscard]] auto isIncludedIn(const Predicate &a, const Predicate &b) const -> bool;
	[[nodiscard]] auto isIncludedIn(const PredicateSet &a, const PredicateSet &b) const -> bool;
	[[nodiscard]] auto isIncludedIn(const TransLabel &a, const TransLabel &b) const -> bool;

	/** Returns whether two predicates compose */
	[[nodiscard]] auto composes(const PredicateSet &preds1, const PredicateSet &preds2) const
		-> bool;

	/**
	 * Returns whether two transitions A and B compose:
	 *    - post(A) ~ pre(B)
	 *    - codom(A) ~ dom(B) (even if domains are not explicitly present in the labels)
	 */
	[[nodiscard]] auto composes(const TransLabel &a, const TransLabel &b) const -> bool;

	auto isValid(const VSet<Predicate::ID> &preds) const -> bool
	{
		return std::ranges::find(invalidPreds_, preds) == invalidPreds_.end();
	}

	/** The sets of pairwise disjoint predicates, builtin and user-declared */
	[[nodiscard]] auto disjointPredicateSets() const -> const VSet<VSet<Predicate::ID>> &
	{
		return disjointPreds_;
	}

	auto isEco(const TransLabel &lab) const -> bool;

	auto hasInfo(const Relation &r) const -> bool { return relations_.contains(r.getID()); }

	auto hasInfo(const Predicate &p) const -> bool { return predicates_.contains(p.getID()); }

	auto getInfo(const Relation &r) const -> const RelationInfo &
	{
		assert(relations_.contains(r.getID()));
		return relations_.find(r.getID())->second;
	}

	auto getInfo(const Predicate &p) const -> const PredicateInfo &
	{
		assert(predicates_.contains(p.getID()));
		return predicates_.find(p.getID())->second;
	}

	auto getDomain(const Relation &r) const -> const PredicateSet &
	{
		const auto &info = getInfo(r);
		return r.isInverse() ? info.codom : info.dom;
	}

	auto getCodomain(const Relation &r) const -> const PredicateSet &
	{
		const auto &info = getInfo(r);
		return r.isInverse() ? info.dom : info.codom;
	}

private:
	/* It is tempting to use Relation as Key below; doing so, however,
	 * would force us to store duplicate information (for the reverse relation) */
	std::unordered_map<Relation::ID, RelationInfo> relations_{};
	std::unordered_map<Relation::ID, Relation> perlocs_{};
	std::unordered_map<Predicate::ID, PredicateInfo> predicates_{};
	std::unordered_map<Predicate::ID, VSet<Predicate::ID>> subsetPreds_{};
	VSet<VSet<Predicate::ID>> disjointPreds_{};
	VSet<VSet<Predicate::ID>> invalidPreds_{};
};

#endif /* KATER_THEORY_HPP */
