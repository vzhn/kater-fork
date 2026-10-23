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

#ifndef KATER_ASSUMPTIONS_HPP
#define KATER_ASSUMPTIONS_HPP

#include "Statement.hpp"

#include <memory>
#include <ranges>
#include <vector>

class Theory;

/*
 * The hypotheses of a module stated as constraints between expressions:
 * the built-in ones (po and mo are transitive, rf;fr <= mo, ...) and the
 * user's "assume" declarations.
 *
 * Unlike the Theory, which holds structural facts about relations and
 * predicates, these are formulae that the decision procedure has to
 * realize by saturating automata. The ones that merely state a domain,
 * a codomain or an incompatibility of predicates are folded into the
 * Theory by incorporateInto() and dropped from the list.
 */
class Assumptions {

public:
	Assumptions() = default;

	auto begin() { return assumes_.begin(); }
	auto end() { return assumes_.end(); }
	[[nodiscard]] auto begin() const { return assumes_.begin(); }
	[[nodiscard]] auto end() const { return assumes_.end(); }

	auto all() { return std::ranges::ref_view(assumes_); }
	[[nodiscard]] auto all() const { return std::ranges::ref_view(assumes_); }

	[[nodiscard]] auto size() const -> size_t { return assumes_.size(); }

	/* Registers an "assume c" declaration */
	void add(std::unique_ptr<AssumeStatement> assm) { assumes_.push_back(std::move(assm)); }

	/* Drops the assumptions registered as temporary */
	void clearTemporary()
	{
		std::erase_if(assumes_, [](auto &stmtUP) -> bool { return stmtUP->isTemporary(); });
	}

	/* Folds into THEORY the assumptions that are plain theory facts,
	 * and drops them from the list. Idempotent. */
	void incorporateInto(Theory &theory);

private:
	/* If ASSM states a domain or a codomain of a relation, registers
	 * it with THEORY. Returns whether that was the case. */
	static auto tryIncorporateDomAssumption(const AssumeStatement *assm, Theory &theory)
		-> bool;

	/* If ASSM states that some predicates are incompatible, registers
	 * them with THEORY. Returns whether that was the case. */
	static auto tryIncorporateIncompatAssumption(const AssumeStatement *assm, Theory &theory)
		-> bool;

	std::vector<std::unique_ptr<AssumeStatement>> assumes_;
};

#endif /* KATER_ASSUMPTIONS_HPP */
