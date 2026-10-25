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

#include "GraphJSON.hpp"

#include "Graph.hpp"
#include "Reference.hpp"
#include "Semantics.hpp"

#include "ParsingDriver.hpp"
#include "Theory.hpp"

#include <fstream>
#include <iostream>
#include <optional>
#include <random>

namespace oracle {

namespace {

using PB = Predicate::BuiltinID;
using RB = Relation::BuiltinID;

constexpr unsigned numPredicates = static_cast<unsigned>(PB::LOC) + 1;

/* The builtin relations, by id: the markers between them aside */
auto builtinRelationIDs() -> std::vector<RB>
{
	std::vector<RB> ids;
	for (auto id = 0; id <= static_cast<int>(RB::any); id++) {
		auto r = static_cast<RB>(id);
		if (r != RB::PerLocBegin && r != RB::WithinPoBegin && r != RB::PerLocLast &&
		    r != RB::WithinPoLast)
			ids.push_back(r);
	}
	return ids;
}

/* The values of a graph's terms: constants, if it is concrete, or in a model */
class Values {

public:
	explicit Values(std::optional<z3::model> m = std::nullopt) : model_(std::move(m)) {}

	[[nodiscard]] auto holds(const Term &t) const -> bool
	{
		if (t.isTrue() || t.isFalse())
			return t.isTrue();
		return model_ ? model_->eval(t.expr(), true).is_true()
			      : t.expr().simplify().is_true();
	}

	[[nodiscard]] auto value(const z3::expr &e) const -> int
	{
		return (model_ ? model_->eval(e, true) : e.simplify()).get_numeral_int();
	}

private:
	std::optional<z3::model> model_;
};

/* What the oracle has of a graph, as a JSON object */
class Writer {

public:
	Writer(std::ostream &os, const Theory &theory) : os_(&os), theory_(&theory) {}

	/* The names of the builtins, in the order the graphs give their meanings in */
	void header()
	{
		auto &os = *os_;
		os << R"({"preds":[)";
		for (auto p = 0U; p < numPredicates; p++)
			os << (p > 0 ? "," : "") << "[" << p << ",\""
			   << nameOf(Predicate::createBuiltin(static_cast<PB>(p)), theory_)
			   << "\"]";
		os << R"(],"rels":[)";
		auto first = true;
		for (auto r : builtinRelationIDs()) {
			os << (first ? "" : ",") << "[" << static_cast<int>(r) << ",\""
			   << nameOf(Relation::createBuiltin(r), theory_) << "\"]";
			first = false;
		}
		os << "]}\n";
	}

	/* Graph G, where HB is GenMC's hb, as SOURCE (NAME) has it */
	void graph(Graph &g, const Matrix &hb, const Values &v, const std::string &source,
		   const std::string &name)
	{
		auto &os = *os_;
		auto n = g.size();
		auto bits = [&](const std::function<bool(unsigned)> &f, unsigned count) {
			std::string s;
			for (auto i = 0U; i < count; i++)
				s += f(i) ? '1' : '0';
			return "\"" + s + "\"";
		};
		auto events = [&](const std::function<Term(unsigned)> &f) {
			return bits([&](unsigned e) { return v.holds(f(e)); }, n);
		};
		auto pairs = [&](const Matrix &m) {
			return bits([&](unsigned i) { return v.holds(m(i / n, i % n)); }, n * n);
		};
		auto list = [&](const std::function<std::string(unsigned)> &f) {
			std::string s = "[";
			for (auto e = 0U; e < n; e++)
				s += (e > 0 ? "," : "") + f(e);
			return s + "]";
		};
		auto quoted = [](const std::string &s) { return "\"" + s + "\""; };

		os << R"({"source":)" << quoted(source) << R"(,"name":)" << quoted(name)
		   << R"(,"n":)" << n;

		/* Threads are contiguous */
		std::vector<unsigned> thread(n, 0);
		for (auto e = 1U; e < n; e++)
			thread[e] = thread[e - 1] + (v.holds(g.sameThread(e - 1, e)) ? 0 : 1);
		os << R"(,"thread":)"
		   << list([&](unsigned e) { return std::to_string(thread[e]); });
		os << R"(,"kind":)" << list([&](unsigned e) {
			for (auto k = 0U; k < numKinds; k++)
				if (v.holds(g.is(e, static_cast<Kind>(k))))
					return quoted(kindName(static_cast<Kind>(k)));
			return quoted("");
		});
		os << R"(,"order":)" << list([&](unsigned e) {
			for (auto o = 0U; o < numOrders; o++)
				if (v.holds(g.hasOrder(e, static_cast<Order>(o))))
					return quoted(orderName(static_cast<Order>(o)));
			return quoted("");
		});
		os << R"(,"loc":)"
		   << list([&](unsigned e) { return std::to_string(v.value(g.location(e))); });
		os << R"(,"hp":)"
		   << list([&](unsigned e) { return std::to_string(v.value(g.hazard(e))); });
		os << R"(,"excl":)" << events([&](unsigned e) { return g.isExclusive(e); });
		os << R"(,"durable":)"
		   << events([&](unsigned e) { return *g.predicate(PB::D, e); });
		os << R"(,"recovery":)"
		   << events([&](unsigned e) { return *g.predicate(PB::REC, e); });
		os << R"(,"abstractLock":)"
		   << events([&](unsigned e) { return *g.predicate(PB::PLK, e); });
		os << R"(,"dependableOther":)"
		   << events([&](unsigned e) { return g.isDependableOther(e); });
		for (auto [key, r] : {std::pair{"rf", RB::rf},
				      {"mo", RB::mo},
				      {"ctrl", RB::ctrl},
				      {"addr", RB::addr},
				      {"data", RB::data},
				      {"pctrl", RB::pctrl},
				      {"tc", RB::tc},
				      {"tj", RB::tj},
				      {"lin", RB::lin}})
			os << ",\"" << key << "\":" << pairs(*g.relation(r));
		Matrix added(g.ctx(), n);
		for (auto i = 0U; i < n; i++)
			for (auto j = 0U; j < n; j++)
				if (i != j)
					added.set(i, j, g.addedBefore(i, j));
		os << R"(,"added":)" << pairs(added) << R"(,"hb":)" << pairs(hb);

		os << R"(,"pred":[)";
		for (auto p = 0U; p < numPredicates; p++) {
			os << (p > 0 ? "," : "");
			if (g.predicate(static_cast<PB>(p), 0))
				os << events([&](unsigned e) {
					return *g.predicate(static_cast<PB>(p), e);
				});
			else
				os << "null";
		}
		os << R"(],"rel":[)";
		auto first = true;
		for (auto r : builtinRelationIDs()) {
			os << (first ? "" : ",");
			first = false;
			if (r == RB::same_thread) {
				Matrix same(g.ctx(), n);
				for (auto i = 0U; i < n; i++)
					for (auto j = 0U; j < n; j++)
						same.set(i, j, g.sameThread(i, j));
				os << pairs(same);
			} else if (isHbPositional(r)) {
				os << pairs(hbPositional(g, r, hb));
			} else if (const auto *m = g.relation(r)) {
				os << pairs(*m);
			} else {
				os << "null";
			}
		}
		/* The oracle's axioms a concrete graph violates */
		os << R"(],"axioms":)" << (g.isConcrete() ? g.axioms().size() : 0) << "}\n";
		count_++;
	}

	[[nodiscard]] auto count() const -> unsigned { return count_; }

private:
	std::ostream *os_;
	const Theory *theory_;
	unsigned count_ = 0;
};

/* (po | rf | tc | tj)+: GenMC's hb, for a concrete graph */
auto causalOrder(Graph &g) -> Matrix
{
	return g.relation(RB::po)
		->unite(*g.relation(RB::rf))
		.unite(*g.relation(RB::tc))
		.unite(*g.relation(RB::tj))
		.plus();
}

/* Every kind of access, fence and dependency */
auto accessAlphabet() -> Alphabet
{
	using enum Order;
	using I = Alphabet::Instruction;
	Alphabet a;
	auto add = [&](Kind k, std::initializer_list<Order> orders, bool rmw = false) {
		for (auto o : orders)
			a.instructions.push_back(I{.kind = k, .order = o, .rmw = rmw});
	};
	add(Kind::R, {NA, RLX, ACQ, SC});
	add(Kind::W, {NA, RLX, REL, SC});
	add(Kind::R, {RLX, ACQ, REL, ACQ_REL, SC}, true);
	add(Kind::F, {ACQ, REL, ACQ_REL, SC});
	a.deps = {&Execution::addr, &Execution::data, &Execution::ctrl, &Execution::pctrl};
	return a;
}

/* The other kinds of events, with a read and a write that may depend on it */
auto kindsAlphabet() -> Alphabet
{
	using enum Order;
	using I = Alphabet::Instruction;
	Alphabet a;
	for (auto [k, o] : {std::pair{Kind::TC, REL},
			    {Kind::TJ, ACQ},
			    {Kind::TE, REL},
			    {Kind::TK, NA},
			    {Kind::MethodBegin, NA},
			    {Kind::MethodEnd, NA},
			    {Kind::Other, NA},
			    {Kind::Other, SC},
			    {Kind::R, RLX},
			    {Kind::W, RLX}})
		a.instructions.push_back(I{.kind = k, .order = o});
	a.deps = {&Execution::ctrl};
	return a;
}

/* The models of the symbolic graph's axioms: SAMPLES of them, each of up to
 * EVENTS events, made different by fixing some of their unknowns at random */
void writeSymbolic(Writer &w, unsigned samples, unsigned events, std::mt19937 &rng)
{
	z3::set_param("smt.phase_selection", 5);
	auto pick = [&](unsigned n) {
		return std::uniform_int_distribution<unsigned>(0, n - 1)(rng);
	};
	for (auto written = 0U; written < samples;) {
		auto n = 1 + pick(events);
		z3::context ctx;
		Graph g(ctx, n);

		/* Every builtin, with the axioms of those built on first use */
		for (auto p = 0U; p < numPredicates; p++)
			for (auto e = 0U; e < n; e++)
				(void)g.predicate(static_cast<PB>(p), e);
		for (auto r : builtinRelationIDs())
			(void)g.relation(r);
		for (auto e = 0U; e < n; e++)
			(void)g.protectedWhenAdded(e);
		auto hb = *g.genmcHb();

		z3::solver solver(ctx);
		z3::params params(ctx);
		params.set("random_seed", static_cast<unsigned>(rng()));
		solver.set(params);
		solver.add(g.axioms());
		if (solver.check() != z3::sat)
			continue;
		/* Each constraint kept if the axioms allow it with the ones before */
		auto tryAdd = [&](const Term &t) {
			solver.push();
			solver.add(t.expr());
			if (solver.check() != z3::sat)
				solver.pop();
		};
		for (auto e = 0U; e < n; e++) {
			if (pick(4) > 0)
				tryAdd(g.is(e, static_cast<Kind>(pick(numKinds))));
			for (auto pred : {PB::D, PB::REC, PB::PLK})
				if (pick(3) == 0)
					tryAdd(*g.predicate(pred, e));
			if (pick(3) == 0)
				tryAdd(g.isDependableOther(e));
		}
		for (auto r : {RB::rf, RB::mo, RB::ctrl, RB::addr, RB::data, RB::pctrl, RB::tc,
			       RB::tj, RB::lin})
			if (pick(2) == 0)
				tryAdd((*g.relation(r))(pick(n), pick(n)));
		if (solver.check() != z3::sat)
			continue;
		w.graph(g, hb, Values(solver.get_model()), "symbolic", std::to_string(written));
		written++;
	}
}

} // namespace

auto writeGraphs(const std::filesystem::path &out, const GraphJSONOptions &opts) -> bool
{
	ParsingDriver driver; /* registers the builtins */
	auto module = driver.takeModule();
	std::ofstream os(out);
	if (!os) {
		std::cerr << out.string() << ": cannot write\n";
		return false;
	}
	Writer w(os, module->getTheory());
	w.header();

	z3::context ctx;
	auto concrete = [&](const Execution &x, const std::string &source, const std::string &name,
			    bool byPo) {
		Graph g(ctx, x);
		auto hb = byPo ? *g.relation(RB::po) : causalOrder(g);
		w.graph(g, hb, Values(), source, name);
		return true;
	};
	auto report = [&](const std::string &what, unsigned before) {
		std::cout << what << ": " << w.count() - before << " graphs\n" << std::flush;
	};

	auto ok = true;
	for (const auto &file : opts.graphs) {
		std::ifstream is(file);
		std::string error;
		auto x = Execution::parse(is, error);
		if (!x) {
			std::cerr << file << ": " << error << "\n";
			ok = false;
			continue;
		}
		concrete(*x, "file", file, false);
	}
	report("graph files", 0);

	auto before = w.count();
	auto i = 0U;
	enumerate(accessAlphabet(), opts.bounds, true, [&](const Execution &x) {
		return concrete(x, "enumerated", std::to_string(i++), false);
	});
	report("accesses, fences and dependencies up to " + std::to_string(opts.bounds.events) +
		       " events",
	       before);

	before = w.count();
	enumerate(kindsAlphabet(), opts.bounds, true, [&](const Execution &x) {
		return concrete(x, "kinds", std::to_string(i++), false);
	});
	report("other kinds of events up to " + std::to_string(opts.bounds.events) + " events",
	       before);

	before = w.count();
	enumerate(heapAlphabetOf("rc11", 2), opts.heapBounds, true, [&](const Execution &x) {
		return concrete(x, "heap", std::to_string(i++), false);
	});
	report("heaps up to " + std::to_string(opts.heapBounds.events) + " events", before);

	std::mt19937 rng(opts.seed);
	if (opts.random > 0) {
		before = w.count();
		auto alphabet = accessAlphabet();
		for (const auto &ins : heapAlphabetOf("rc11", 2).instructions)
			if (ins.kind != Kind::R && ins.kind != Kind::W)
				alphabet.instructions.push_back(ins);
		alphabet.threadEvents = true;
		alphabet.methods = true;
		for (auto r = 0U; r < opts.random; r++)
			concrete(randomExecution(alphabet, opts.randomBounds, true, rng), "random",
				 std::to_string(r), true);
		report("random up to " + std::to_string(opts.randomBounds.events) + " events",
		       before);
	}
	if (opts.symbolic > 0) {
		before = w.count();
		writeSymbolic(w, opts.symbolic, opts.symbolicEvents, rng);
		report("models of the symbolic graph up to " + std::to_string(opts.symbolicEvents) +
			       " events",
		       before);
	}
	return ok && static_cast<bool>(os);
}

} // namespace oracle
