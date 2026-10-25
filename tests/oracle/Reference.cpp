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

#include "Reference.hpp"

#include "Enumerate.hpp"
#include "Execution.hpp"
#include "Graph.hpp"
#include "Matrix.hpp"
#include "Semantics.hpp"

#include "Constraint.hpp"
#include "KatModule.hpp"
#include "Predicate.hpp"
#include "RegExp.hpp"
#include "Relation.hpp"
#include "SavedExp.hpp"
#include "Statement.hpp"

#include <filesystem>
#include <fstream>
#include <initializer_list>
#include <map>
#include <memory>
#include <optional>
#include <sstream>
#include <stdexcept>
#include <string>
#include <type_traits>
#include <utility>
#include <vector>

namespace oracle {

using RB = Relation::BuiltinID;

auto constant(const Term &t) -> bool
{
	if (!t.isTrue() && !t.isFalse())
		throw std::logic_error(
			"a formula over a concrete graph did not fold to a constant");
	return t.isTrue();
}

auto constant(const Matrix &m) -> Pairs
{
	Pairs p(m.size(), std::vector<bool>(m.size()));
	for (auto i = 0U; i < m.size(); i++)
		for (auto j = 0U; j < m.size(); j++)
			p[i][j] = constant(m(i, j));
	return p;
}

auto baseName(const std::string &name) -> std::string
{
	auto colons = name.rfind("::");
	return colons == std::string::npos ? name : name.substr(colons + 2);
}

auto lkmmPredicate(const std::string &name, const Execution &x, unsigned e) -> std::optional<bool>
{
	const auto &ev = x.events[e];
	auto isR = ev.kind == Kind::R;
	auto isW = ev.kind == Kind::W;
	static const std::map<std::string, unsigned> fences = {
		{"Fmb", 0},  {"Frmb", 1}, {"Fwmb", 2}, {"Fba", 3},   {"Faa", 4},    {"Fas", 5},
		{"Faul", 6}, {"Frl", 7},  {"Fru", 8},  {"Fsync", 9}, {"Fasru", 10}, {"Fsyncs", 11}};
	if (auto it = fences.find(name); it != fences.end())
		return ev.kind == Kind::F && ev.flavor == Flavor::LkmmFence &&
		       ev.fence == it->second;
	auto atLeastAcq = ev.order == Order::ACQ || ev.order == Order::ACQ_REL ||
			  ev.order == Order::SC;
	auto atLeastRel = ev.order == Order::REL || ev.order == Order::ACQ_REL ||
			  ev.order == Order::SC;
	if (name == "SrcuU")
		return isW && ev.flavor == Flavor::SrcuUnlock;
	if (name == "NotSrcuU")
		return !(isW && ev.flavor == Flavor::SrcuUnlock);
	if (name == "MbR")
		return isR && ev.flavor == Flavor::Mb && ev.excl;
	if (name == "MbW")
		return isW && ev.flavor == Flavor::Mb && ev.excl;
	if (name == "R4rmb")
		return isR && ev.flavor != Flavor::NoRet;
	/* The runner makes the reads of these RMWs FaiReadLabels of an add
	 * (genmc/Runner.cpp); executions have no xchg() */
	if (name == "FopR")
		return isR && ev.excl &&
		       (ev.flavor == Flavor::Plain || ev.flavor == Flavor::Mb ||
			ev.flavor == Flavor::NoRet);
	if (name == "Acq")
		return isR && atLeastAcq && ev.flavor != Flavor::FailedCas &&
		       (ev.flavor != Flavor::Lock || ev.excl);
	if (name == "Rel")
		return isW && atLeastRel;
	if (name == "LKR")
		return isR && ev.flavor == Flavor::Lock && ev.excl;
	if (name == "LKW")
		return isW && ev.flavor == Flavor::Lock;
	if (name == "UL")
		return isW && ev.flavor == Flavor::Unlock;
	if (name == "NotPlain")
		return !(ev.isAccess() && ev.order == Order::NA);
	return std::nullopt;
}

/* An error or warning export as its line of the .kat has it, from the
 * error's name on, without comments; empty if the line is not at hand */
static auto sourceOf(const ExportStatement &stmt) -> std::string
{
	const auto &dbg = stmt.getDbgInfo();
	if (!dbg || dbg->filename.empty())
		return {};
	std::ifstream is(dbg->filename);
	std::string line;
	for (auto i = 0; i < dbg->line && std::getline(is, line); i++)
		;
	if (auto comment = line.find("//"); comment != std::string::npos)
		line.resize(comment);
	std::istringstream words(line);
	std::string word;
	std::string text;
	auto named = false;
	while (words >> word) {
		if (named)
			text += (text.empty() ? "" : " ") + word;
		named |= word == "error" || word == "warning";
	}
	return text;
}

Reference::Reference(std::unique_ptr<KatModule> module) : module_(std::move(module))
{
	for (const auto &stmt : module_->exports()) {
		const auto *c = stmt->getConstraint();
		if (stmt->isExtra())
			continue;
		if (dynamic_cast<const AcyclicConstraint *>(c) != nullptr ||
		    dynamic_cast<const SubsetConstraint *>(c) != nullptr)
			consistency_.push_back({.constraint = c, .unless = stmt->getUnless()});
		if (const auto *w = dynamic_cast<const WarningConstraint *>(c)) {
			auto text = sourceOf(*stmt);
			if (text.empty()) {
				std::ostringstream dump;
				dump << w->getWarningName();
				if (const auto *u = stmt->getUnless()) {
					dump << " unless ";
					u->dump(dump, &module_->getTheory());
				}
				text = dump.str();
			}
			clauses_.push_back(
				{.code = w->getWarningName(),
				 .error = dynamic_cast<const ErrorConstraint *>(c) != nullptr,
				 .unless =
					 dynamic_cast<const SubsetConstraint *>(stmt->getUnless()),
				 .text = text});
		}
	}
	if (const auto *coh = module_->getCOHDeclaration())
		coherence_ = coh->getRE();
	for (const auto &let : module_->lets()) {
		if (dynamic_cast<const ViewExp *>(let->getSaved()) != nullptr)
			views_.emplace_back(baseName(let->getName()), let->getRE());
		const auto *charRE = dynamic_cast<const CharRE *>(let->getRE());
		auto name = baseName(let->getName());
		if (name == "prop")
			prop_ = let->getRE();
		if (name == "prop-int" && charRE != nullptr &&
		    charRE->getLabel().getRelation().has_value())
			propInt_ = *charRE->getLabel().getRelation();
	}
	pporf_ = module_->createPPORF();
	if (module_->getRPPODeclaration() != nullptr && module_->isDepTracking())
		rpporf_ = module_->createRPPORF();
}

template <typename F>
auto Reference::evaluate(const Execution &x, F f, std::optional<std::vector<unsigned>> order)
	-> std::invoke_result_t<F, Graph &, Semantics &>
{
	Graph g(
		ctx_, x,
		[&](const Predicate &p, unsigned e) {
			auto name = baseName(nameOf(p, &module_->getTheory()));
			auto v = lkmmPredicate(name, x, e);
			if (!v)
				throw Unsupported("user predicate " + name);
			return *v;
		},
		std::move(order));
	Semantics sem(g, *module_);
	/* prop-int is (prop \ id) & int, which GenMC computes by hand */
	if (propInt_ && prop_ != nullptr) {
		auto prop = sem.eval(*prop_);
		Matrix m(ctx_, x.size());
		for (auto i = 0U; i < x.size(); i++)
			for (auto j = 0U; j < x.size(); j++)
				if (i != j)
					m.set(i, j, prop(i, j) && g.sameThread(i, j));
		g.fixUserRelation(*propInt_, m);
	}
	return f(g, sem);
}

auto Reference::isCoherent(Graph &g, Semantics &sem) -> bool
{
	if (coherence_ == nullptr)
		return true;
	auto eco = g.relation(RB::rf)->unite(*g.relation(RB::mo)).unite(*g.relation(RB::fr)).plus();
	return !constant(sem.eval(*coherence_).compose(eco).anyReflexive());
}

auto Reference::factsOf(Graph &g, Semantics &sem) -> Facts
{
	Facts f;
	f.wellFormed = g.axioms().empty();
	f.consistent = true;
	f.consistentUnless = true;
	for (const auto &[c, unless] : consistency_) {
		auto holds = constant(sem.holds(*c));
		f.consistent &= holds;
		f.consistentUnless &= holds || (unless && constant(sem.holds(*unless)));
	}
	f.coherent = isCoherent(g, sem);
	auto porf = g.relation(RB::po)
			    ->unite(*g.relation(RB::rf))
			    .unite(*g.relation(RB::tc))
			    .unite(*g.relation(RB::tj))
			    .unite(*g.relation(RB::lin));
	f.porfAcyclic = !constant(porf.plus().anyReflexive());
	f.pporfAcyclic = !constant(sem.eval(*pporf_).anyReflexive());
	return f;
}

auto Reference::facts(const Execution &x) -> Facts
{
	return evaluate(x, [&](Graph &g, Semantics &sem) { return factsOf(g, sem); });
}

auto Reference::factsWithPrefix(const Execution &x) -> std::pair<Facts, Pairs>
{
	return evaluate(x, [&](Graph &g, Semantics &sem) {
		auto f = factsOf(g, sem);
		return std::make_pair(f, constant(sem.eval(*pporf_)));
	});
}

auto Reference::coherent(const Execution &x) -> bool
{
	return evaluate(x, [&](Graph &g, Semantics &sem) { return isCoherent(g, sem); });
}

auto Reference::views(const Execution &x) -> std::vector<Pairs>
{
	return evaluate(x, [&](Graph & /*g*/, Semantics &sem) {
		std::vector<Pairs> vs;
		vs.reserve(views_.size());
		for (const auto &[name, re] : views_)
			vs.push_back(constant(sem.eval(*re)));
		return vs;
	});
}

auto Reference::prefix(const Execution &x) -> Pairs
{
	return evaluate(x,
			[&](Graph & /*g*/, Semantics &sem) { return constant(sem.eval(*pporf_)); });
}

auto Reference::revisitPrefix(const Execution &x) -> Pairs
{
	return evaluate(
		x, [&](Graph & /*g*/, Semantics &sem) { return constant(sem.eval(*rpporf_)); });
}

auto Reference::checks(const Execution &x, const std::vector<unsigned> &order)
	-> std::vector<std::vector<Verdict>>
{
	std::vector<std::vector<Verdict>> result(x.size());
	std::vector<bool> related(x.size(), false);
	auto at = [&](const Execution &y, const std::vector<unsigned> &events) {
		evaluate(
			y,
			[&](Graph &g, Semantics &sem) {
				for (const auto &c : clauses_)
					verdicts(g, sem, c, events, result, related);
				return 0;
			},
			order);
	};
	std::vector<unsigned> checked;
	for (auto e = 0U; e < x.size(); e++)
		if (x.events[e].isChecked())
			checked.push_back(e);
	at(x, checked);
	/* A read, without its rf, where a clause relates events to it (its
	 * left-hand side reads the execution state, which holds the events
	 * before the read, not its rf) */
	for (auto e : checked) {
		if (x.events[e].kind != Kind::R || x.rf[e] < 0 || !related[e])
			continue;
		auto y = x;
		y.rf[e] = -1;
		result[e].clear();
		at(y, {e});
	}
	return result;
}

void Reference::verdicts(Graph &g, Semantics &sem, const Clause &c,
			 const std::vector<unsigned> &events,
			 std::vector<std::vector<Verdict>> &result, std::vector<bool> &related)
{
	auto n = g.size();
	if (c.unless == nullptr) {
		for (auto e : events)
			result[e].push_back({.holds = false, .witnesses = {}});
		return;
	}
	const auto &lhs = sem.evalShared(*c.unless->getLHS());
	const auto &rhs = sem.evalShared(*c.unless->getRHS());
	auto both = dynamic_cast<const EqualityConstraint *>(c.unless) != nullptr;
	for (auto e : events) {
		Verdict v;
		for (auto f = 0U; f < n; f++) {
			if (c.unless->sameEnds() && f != e)
				continue;
			auto l = constant(lhs(f, e));
			auto r = constant(rhs(f, e));
			related[e] = related[e] || l || (both && r);
			if ((l && !r) || (both && r && !l)) {
				v.holds = false;
				v.witnesses.push_back(static_cast<int>(f));
			}
		}
		result[e].push_back(v);
	}
}

auto alphabetOf(const std::string &model) -> Alphabet
{
	using enum Order;
	using I = Alphabet::Instruction;
	Alphabet a;
	auto add = [&](Kind k, std::initializer_list<Order> orders, bool rmw = false,
		       Flavor flavor = Flavor::Plain) {
		for (auto o : orders)
			a.instructions.push_back(
				I{.kind = k, .order = o, .rmw = rmw, .flavor = flavor});
	};
	if (model == "sc") {
		add(Kind::R, {NA, SC});
		add(Kind::W, {NA, SC});
		add(Kind::R, {SC}, true);
		add(Kind::F, {SC});
	} else if (model == "tso") {
		add(Kind::R, {RLX, ACQ, SC});
		add(Kind::W, {RLX, REL, SC});
		add(Kind::R, {RLX, ACQ_REL, SC}, true);
		add(Kind::F, {ACQ, REL, SC});
	} else if (model == "ra") {
		add(Kind::R, {RLX, ACQ});
		add(Kind::W, {RLX, REL});
		add(Kind::R, {RLX, ACQ, REL, ACQ_REL}, true);
		add(Kind::F, {ACQ, REL});
	} else if (model == "lkmm") {
		/* Plain and marked accesses, the kernel's RMWs, locks, SRCU, fences */
		add(Kind::R, {NA, RLX, ACQ});
		add(Kind::W, {NA, RLX, REL});
		add(Kind::R, {RLX, ACQ, REL}, true);
		add(Kind::R, {RLX}, true, Flavor::Mb);
		add(Kind::R, {RLX}, true, Flavor::NoRet);
		add(Kind::R, {ACQ}, true, Flavor::Lock);
		add(Kind::W, {REL}, false, Flavor::Unlock);
		add(Kind::R, {RLX, ACQ}, false, Flavor::FailedCas);
		add(Kind::R, {RLX}, false, Flavor::SrcuLock);
		add(Kind::W, {RLX}, false, Flavor::SrcuUnlock);
		/* LkmmFenceLabel::orderingOf() */
		for (auto k = 0U; k < numLkmmFences; k++)
			a.instructions.push_back(I{.kind = Kind::F,
						   .order = k == 1 || k == 7   ? ACQ
							    : k == 2 || k == 8 ? REL
									       : SC,
						   .flavor = Flavor::LkmmFence,
						   .fence = k});
		a.deps = {&Execution::addr, &Execution::data, &Execution::ctrl, &Execution::pctrl};
	} else {
		/* rc11, imm, and any other model: every ordering */
		add(Kind::R, {NA, RLX, ACQ, SC});
		add(Kind::W, {NA, RLX, REL, SC});
		add(Kind::R, {RLX, ACQ, REL, ACQ_REL, SC}, true);
		add(Kind::F, {ACQ, REL, ACQ_REL, SC});
		if (model == "imm")
			a.deps = {&Execution::addr, &Execution::data, &Execution::ctrl};
	}
	a.threadEvents = true;
	a.methods = true;
	return a;
}

auto heapAlphabetOf(const std::string &model, unsigned hazards) -> Alphabet
{
	using enum Order;
	using I = Alphabet::Instruction;
	Alphabet a;
	auto add = [&](Kind k, std::initializer_list<Order> orders) {
		for (auto o : orders)
			a.instructions.push_back(I{.kind = k, .order = o});
	};
	add(Kind::Alloc, {NA});
	add(Kind::Free, {NA});
	add(Kind::HpRetire, {NA});
	for (auto h = 0U; h < hazards; h++)
		a.instructions.push_back(I{.kind = Kind::HpProtect, .order = REL, .hp = h});
	if (model == "sc") {
		add(Kind::R, {NA, SC});
		add(Kind::W, {NA, SC});
	} else {
		add(Kind::R, {NA, RLX, ACQ});
		add(Kind::W, {NA, RLX, REL});
	}
	return a;
}

auto modelOf(const std::string &file) -> std::string
{
	auto stem = std::filesystem::path(file).stem().string();
	if (stem.ends_with("-genmc"))
		stem.resize(stem.size() - 6);
	return stem;
}

} // namespace oracle
