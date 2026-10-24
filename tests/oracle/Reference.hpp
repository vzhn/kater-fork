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

#ifndef KATER_ORACLE_REFERENCE_HPP
#define KATER_ORACLE_REFERENCE_HPP

#include "Enumerate.hpp"
#include "Execution.hpp"
#include "Matrix.hpp"

#include "Constraint.hpp"
#include "KatModule.hpp"
#include "RegExp.hpp"
#include "Relation.hpp"

#include <z3++.h>

#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <vector>

namespace oracle {

class Graph;
class Semantics;

/* A relation over the events of a concrete graph */
using Pairs = std::vector<std::vector<bool>>;

/* The value a formula, or each entry of a relation, folds to on a concrete graph */
auto constant(const Term &t) -> bool;
auto constant(const Matrix &m) -> Pairs;

/* The name of a declared symbol without the module it is in */
auto baseName(const std::string &name) -> std::string;

/*
 * The meaning of LKMM's user predicates, from the GenMC code that
 * kat/lkmm-genmc.kat gives them, on the labels kater-oracle-runner makes
 * of the events. Returns nullopt for a name it does not know.
 */
auto lkmmPredicate(const std::string &name, const Execution &x, unsigned e) -> std::optional<bool>;

/*
 * The meaning of a GenMC model's export in the reference semantics: what
 * isConsistent() checks, coherence, the views every event saves, and the
 * prefix GenMC keeps of it. Evaluated on concrete graphs.
 */
class Reference {

public:
	struct Facts {
		bool wellFormed = false;       /* the axioms of Graph hold */
		bool consistent = false;       /* the acyclicity and inclusion exports */
		bool consistentUnless = false; /* each of them, or its unless clause */
		bool coherent = false;	   /* the view of `export coherence` ; eco is irreflexive */
		bool porfAcyclic = false;  /* po | rf | tc | tj | lin */
		bool pporfAcyclic = false; /* ppo | rfe | tc | tj | lin (GenMC's prefix) */
	};

	explicit Reference(std::unique_ptr<KatModule> module);

	[[nodiscard]] auto isDepTracking() const -> bool { return module_->isDepTracking(); }
	[[nodiscard]] auto viewName(unsigned i) const -> const std::string &
	{
		return views_[i].first;
	}

	auto facts(const Execution &x) -> Facts;
	auto coherent(const Execution &x) -> bool;

	/* The relation each view saves, in the order of GenMC's view indices */
	auto views(const Execution &x) -> std::vector<Pairs>;

	/* GenMC's prefix relation (KatModule::createPPORF) */
	auto prefix(const Execution &x) -> Pairs;

	/* The prefix a write's revisits keep, if the model declares rppo */
	[[nodiscard]] auto hasRevisitPrefix() const -> bool { return rpporf_ != nullptr; }
	auto revisitPrefix(const Execution &x) -> Pairs;

private:
	auto isCoherent(Graph &g, Semantics &sem) -> bool;

	template <typename F>
	auto evaluate(const Execution &x, F f) -> std::invoke_result_t<F, Graph &, Semantics &>;

	std::unique_ptr<KatModule> module_;
	z3::context ctx_;

	struct Export {
		const Constraint *constraint;
		const Constraint *unless;
	};
	std::vector<Export> consistency_;
	const RegExp *coherence_ = nullptr;
	std::vector<std::pair<std::string, const RegExp *>> views_;
	std::unique_ptr<RegExp> pporf_;
	std::unique_ptr<RegExp> rpporf_;
	const RegExp *prop_ = nullptr;
	std::optional<Relation> propInt_;
};

/* The events of the model's graphs: the orderings and labels it tells apart */
auto alphabetOf(const std::string &model) -> Alphabet;

/* The model a kat/NAME-genmc.kat defines: NAME */
auto modelOf(const std::string &file) -> std::string;

} // namespace oracle

#endif /* KATER_ORACLE_REFERENCE_HPP */
