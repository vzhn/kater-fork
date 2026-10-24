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

#include "GenMC.hpp"

#include "Graph.hpp"
#include "Matrix.hpp"
#include "Semantics.hpp"

#include "Constraint.hpp"
#include "KatModule.hpp"
#include "ParsingDriver.hpp"
#include "SavedExp.hpp"
#include "Statement.hpp"
#include "Theory.hpp"
#include "Utils.hpp"

#include <poll.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

#include <algorithm>
#include <array>
#include <csignal>
#include <cstdio>
#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <map>
#include <memory>
#include <optional>
#include <random>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <type_traits>
#include <utility>
#include <vector>

namespace oracle {

namespace {

using RB = Relation::BuiltinID;

/* A relation over the events of a concrete graph */
using Pairs = std::vector<std::vector<bool>>;

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

/* The name of a declared symbol without the module it is in */
auto baseName(const std::string &name) -> std::string
{
	auto colons = name.rfind("::");
	return colons == std::string::npos ? name : name.substr(colons + 2);
}

/*
 * The meaning of LKMM's user predicates, from the GenMC code that
 * kat/lkmm-genmc.kat gives them, on the labels kater-oracle-runner makes
 * of the events. Returns nullopt for a name it does not know.
 */
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

	/* A clause's verdict at an event, and the events that refute it there */
	struct Verdict {
		bool holds = true;
		std::vector<int> witnesses;
	};

	explicit Reference(std::unique_ptr<KatModule> module) : module_(std::move(module))
	{
		for (const auto &stmt : module_->exports()) {
			const auto *c = stmt->getConstraint();
			if (stmt->isExtra())
				continue;
			if (dynamic_cast<const AcyclicConstraint *>(c) != nullptr ||
			    dynamic_cast<const SubsetConstraint *>(c) != nullptr)
				consistency_.push_back(
					{.constraint = c, .unless = stmt->getUnless()});
			if (const auto *w = dynamic_cast<const WarningConstraint *>(c)) {
				std::ostringstream text;
				text << w->getWarningName();
				if (const auto *u = stmt->getUnless()) {
					text << " unless ";
					u->dump(text, &module_->getTheory());
				}
				clauses_.push_back(
					{.code = w->getWarningName(),
					 .error = dynamic_cast<const ErrorConstraint *>(c) !=
						  nullptr,
					 .unless = dynamic_cast<const SubsetConstraint *>(
						 stmt->getUnless()),
					 .text = text.str()});
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

	[[nodiscard]] auto isDepTracking() const -> bool { return module_->isDepTracking(); }
	[[nodiscard]] auto viewName(unsigned i) const -> const std::string &
	{
		return views_[i].first;
	}

	auto facts(const Execution &x) -> Facts
	{
		return evaluate(x, [&](Graph &g, Semantics &sem) {
			Facts f;
			f.wellFormed = g.axioms().empty();
			f.consistent = true;
			f.consistentUnless = true;
			for (const auto &[c, unless] : consistency_) {
				auto holds = constant(sem.holds(*c));
				f.consistent &= holds;
				f.consistentUnless &= holds ||
						      (unless && constant(sem.holds(*unless)));
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
		});
	}

	auto coherent(const Execution &x) -> bool
	{
		return evaluate(x, [&](Graph &g, Semantics &sem) { return isCoherent(g, sem); });
	}

	/* The relation each view saves, in the order of GenMC's view indices */
	auto views(const Execution &x) -> std::vector<Pairs>
	{
		return evaluate(x, [&](Graph & /*g*/, Semantics &sem) {
			std::vector<Pairs> vs;
			vs.reserve(views_.size());
			for (const auto &[name, re] : views_)
				vs.push_back(constant(sem.eval(*re)));
			return vs;
		});
	}

	/* GenMC's prefix relation (KatModule::createPPORF) */
	auto prefix(const Execution &x) -> Pairs
	{
		return evaluate(x, [&](Graph & /*g*/, Semantics &sem) {
			return constant(sem.eval(*pporf_));
		});
	}

	/* The prefix a write's revisits keep, if the model declares rppo */
	[[nodiscard]] auto hasRevisitPrefix() const -> bool { return rpporf_ != nullptr; }
	auto revisitPrefix(const Execution &x) -> Pairs
	{
		return evaluate(x, [&](Graph & /*g*/, Semantics &sem) {
			return constant(sem.eval(*rpporf_));
		});
	}

	/* The error and warning exports, in their order */
	[[nodiscard]] auto numClauses() const -> unsigned
	{
		return static_cast<unsigned>(clauses_.size());
	}
	[[nodiscard]] auto clauseCode(unsigned i) const -> const std::string &
	{
		return clauses_[i].code;
	}
	[[nodiscard]] auto clauseIsError(unsigned i) const -> bool { return clauses_[i].error; }
	/* Whether clause I is A = 0, which leaves its race unset (vzhn/kater-fork#34) */
	[[nodiscard]] auto clauseIsEmpty(unsigned i) const -> bool
	{
		return clauses_[i].unless != nullptr && clauses_[i].unless->isEmpty();
	}
	[[nodiscard]] auto clauseText(unsigned i) const -> const std::string &
	{
		return clauses_[i].text;
	}

	/*
	 * Each clause's verdict at each event GenMC checks (by event), the
	 * events in the execution state in ORDER: on the graph as GenMC has it
	 * when it adds the event, a read without its rf. The unless clause
	 * A <= B holds at E when every A-predecessor of E is a B-predecessor
	 * (GenMCPrinter's check from the event just added), A = B in both
	 * directions, and a clause without unless never does.
	 */
	auto checks(const Execution &x, const std::vector<unsigned> &order)
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
		 * left-hand side reads the execution state, which holds the
		 * events before the read, not its rf) */
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

private:
	struct Clause {
		std::string code;
		bool error;
		const SubsetConstraint *unless;
		std::string text;
	};

	/* Clause C's verdicts at EVENTS; RELATED marks the events its left-hand
	 * side relates events to */
	static void verdicts(Graph &g, Semantics &sem, const Clause &c,
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

	auto isCoherent(Graph &g, Semantics &sem) -> bool
	{
		if (coherence_ == nullptr)
			return true;
		auto eco = g.relation(RB::rf)
				   ->unite(*g.relation(RB::mo))
				   .unite(*g.relation(RB::fr))
				   .plus();
		return !constant(sem.eval(*coherence_).compose(eco).anyReflexive());
	}

	/* F on the graph of X, its events entering the execution state in ORDER
	 * (by default, as kater-oracle-runner adds them) */
	template <typename F>
	auto evaluate(const Execution &x, F f, std::optional<std::vector<unsigned>> order = {})
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

	std::unique_ptr<KatModule> module_;
	z3::context ctx_;

	struct Export {
		const Constraint *constraint;
		const Constraint *unless;
	};
	std::vector<Export> consistency_;
	std::vector<Clause> clauses_;
	const RegExp *coherence_ = nullptr;
	std::vector<std::pair<std::string, const RegExp *>> views_;
	std::unique_ptr<RegExp> pporf_;
	std::unique_ptr<RegExp> rpporf_;
	const RegExp *prop_ = nullptr;
	std::optional<Relation> propInt_;
};

/*
 * kater-oracle-runner, as a child process: graphs and queries go down a
 * pipe, answers come back up another. A runner that dies, or takes longer
 * than a minute over a graph, is restarted for the next one.
 */
class Runner {

public:
	Runner(std::string path, std::string model)
		: path_(std::move(path)), model_(std::move(model))
	{
	}
	Runner(const Runner &) = delete;
	Runner(Runner &&) = delete;
	auto operator=(const Runner &) -> Runner & = delete;
	auto operator=(Runner &&) -> Runner & = delete;
	~Runner() { stop(); }

	/* The answers to QUERIES about X; nullopt if the runner died or hung */
	auto ask(const Execution &x, const std::vector<std::string> &queries)
		-> std::optional<std::vector<std::string>>
	{
		if (pid_ < 0 && !start())
			return std::nullopt;
		std::ostringstream req;
		req << "graph\n" << x << "end\n";
		for (const auto &q : queries)
			req << q << "\n";
		req << "go\n";
		auto s = req.str();
		if (std::fwrite(s.data(), 1, s.size(), to_) != s.size() || std::fflush(to_) != 0) {
			stop();
			return std::nullopt;
		}
		std::vector<std::string> answers;
		while (auto line = readLine()) {
			if (*line == "done")
				return answers;
			answers.push_back(*line);
		}
		stop();
		return std::nullopt;
	}

	/* How the last runner ended */
	[[nodiscard]] auto lastExit() const -> const std::string & { return lastExit_; }

private:
	static constexpr int timeoutMs = 60000;

	auto start() -> bool
	{
		std::array<int, 2> down{};
		std::array<int, 2> up{};
		if (pipe(down.data()) != 0 || pipe(up.data()) != 0)
			return false;
		pid_ = fork();
		if (pid_ == 0) {
			dup2(down[0], STDIN_FILENO);
			dup2(up[1], STDOUT_FILENO);
			for (auto fd : {down[0], down[1], up[0], up[1]})
				close(fd);
			execl(path_.c_str(), path_.c_str(), model_.c_str(), nullptr);
			_exit(127);
		}
		close(down[0]);
		close(up[1]);
		to_ = fdopen(down[1], "w");
		from_ = up[0];
		return pid_ > 0 && to_ != nullptr;
	}

	/* The runner's next line; nullopt when it stopped answering */
	auto readLine() -> std::optional<std::string>
	{
		for (;;) {
			if (auto nl = buffer_.find('\n'); nl != std::string::npos) {
				auto line = buffer_.substr(0, nl);
				buffer_.erase(0, nl + 1);
				return line;
			}
			pollfd p{.fd = from_, .events = POLLIN, .revents = 0};
			if (poll(&p, 1, timeoutMs) <= 0) {
				hung_ = true;
				return std::nullopt;
			}
			std::array<char, 4096> chunk{};
			auto got = read(from_, chunk.data(), chunk.size());
			if (got <= 0)
				return std::nullopt;
			buffer_.append(chunk.data(), static_cast<size_t>(got));
		}
	}

	void stop()
	{
		if (to_ != nullptr)
			std::fclose(to_);
		if (from_ >= 0)
			close(from_);
		to_ = nullptr;
		from_ = -1;
		buffer_.clear();
		if (pid_ > 0) {
			if (hung_)
				kill(pid_, SIGKILL);
			int status = 0;
			waitpid(pid_, &status, 0);
			lastExit_ = hung_ ? "no answer within a minute"
				    : WIFSIGNALED(status)
					    ? "killed by signal " + std::to_string(WTERMSIG(status))
					    : "exit status " + std::to_string(WEXITSTATUS(status));
		}
		pid_ = -1;
		hung_ = false;
	}

	std::string path_;
	std::string model_;
	pid_t pid_ = -1;
	FILE *to_ = nullptr;
	int from_ = -1;
	std::string buffer_;
	bool hung_ = false;
	std::string lastExit_;
};

auto bit(bool b) -> std::string { return b ? "1" : "0"; }

/* A list of events, as answers name them: init first, then by number */
auto eventSet(const std::vector<int> &events) -> std::string
{
	auto sorted = events;
	std::ranges::sort(sorted);
	sorted.erase(std::ranges::unique(sorted).begin(), sorted.end());
	std::string s;
	for (auto e : sorted)
		s += " " + (e < 0 ? std::string("init") : std::to_string(e));
	return s;
}

/* Whether KEY is of an error check, whose answer names the errors with their races */
auto isErrorCheck(const std::string &key) -> bool
{
	return key.starts_with("errors ") || key.starts_with("warnings ");
}

/* An answer "key: list" with its list normalized; thread starts dropped from views */
auto normalize(const std::string &answer, const Execution &x) -> std::pair<std::string, std::string>
{
	auto colon = answer.find(':');
	if (colon == std::string::npos) {
		auto space = answer.rfind(' ');
		return {answer.substr(0, space), answer.substr(space + 1)};
	}
	auto key = answer.substr(0, colon);
	if (isErrorCheck(key)) {
		auto value = answer.substr(colon + 1);
		value.erase(0, value.find_first_not_of(' '));
		return {key, value};
	}
	auto isView = key.starts_with("view ") || key.starts_with("prefix ") ||
		      key.starts_with("rprefix ");
	std::istringstream ls(answer.substr(colon + 1));
	std::vector<int> events;
	std::string item;
	while (ls >> item) {
		if (item == "init") {
			events.push_back(-1);
			continue;
		}
		auto e = std::stoi(item);
		if (isView && x.events[e].kind == Kind::TB)
			continue;
		events.push_back(e);
	}
	return {key, eventSet(events)};
}

/*
 * Whether GenMC's answer GOT to an error check (CODE RACE ..., or none) is
 * what WANT expects (CODE:W1,W2 ..., or none): the same errors, in the
 * same order, each with a race among the events that refute its clause
 */
auto errorsMatch(const std::string &want, const std::string &got) -> bool
{
	std::istringstream ws(want == "none" ? "" : want);
	std::istringstream gs(got == "none" ? "" : got);
	std::string w;
	std::string code;
	std::string race;
	while (ws >> w) {
		if (!(gs >> code >> race))
			return false;
		auto colon = w.find(':');
		auto races = w.substr(colon + 1);
		if (w.substr(0, colon) != code ||
		    (races != "*" && !("," + races + ",").contains("," + race + ",")))
			return false;
	}
	return !(gs >> code);
}

/* An answer to an error check as a reader takes it */
auto errorsValue(const std::string &v, bool expected) -> std::string
{
	if (v == "none" || v.empty())
		return expected ? "no error" : "none";
	std::istringstream vs(v);
	std::string item;
	std::string out;
	while (vs >> item) {
		std::string race;
		std::string code = item;
		if (expected) {
			auto colon = item.find(':');
			code = item.substr(0, colon);
			std::string set;
			std::istringstream ls(item.substr(colon + 1));
			std::string w;
			while (std::getline(ls, w, ','))
				set += (set.empty() ? "e" : ", e") + w;
			race = item.substr(colon + 1) == "*" ? "any race"
			       : set.empty()		     ? "no race"
							     : "the race one of {" + set + "}";
		} else {
			vs >> race;
			race = race == "none"
				       ? "no race"
				       : "the race " + (race == "?" || race == "init" ? race
										      : "e" + race);
		}
		out += (out.empty() ? "" : "; ") + code + " with " + race;
	}
	return out;
}

/* The events that may be added last: the last of their thread, which no
 * event reads from or follows as a thread event */
auto lastCandidates(const Execution &x) -> std::vector<unsigned>
{
	std::vector<unsigned> result;
	for (auto e = 0U; e < x.size(); e++) {
		const auto &ev = x.events[e];
		if (ev.kind == Kind::TB ||
		    (e + 1 < x.size() && x.events[e + 1].thread == ev.thread))
			continue;
		if (std::ranges::any_of(x.rf, [&](auto w) { return w == static_cast<int>(e); }))
			continue;
		auto from = [&](const Execution::Edges &edges) {
			return std::ranges::any_of(edges, [&](auto &p) { return p.first == e; });
		};
		if (from(x.tc) || from(x.tj) || from(x.lin))
			continue;
		result.push_back(e);
	}
	return result;
}

class Comparison {

public:
	Comparison(Reference &ref, Runner &runner, const GenMCOptions &opts)
		: ref_(&ref), runner_(&runner), opts_(&opts)
	{
	}

	void check(const Execution &x)
	{
		graphs_++;
		auto f = ref_->facts(x);
		if (!f.wellFormed)
			malformed_++;
		/* lin comes from Relinche, onto a graph GenMC built: that graph has
		 * to be one, whatever cycles lin closes */
		auto withoutLin = x;
		withoutLin.lin.clear();
		auto built = x.lin.empty() ? f : ref_->facts(withoutLin);
		if (!f.wellFormed || !isValid(withoutLin, built))
			return;
		valid_++;
		excluding_.clear();

		std::map<std::string, std::string> expected;
		std::vector<std::string> queries{"consistent"};
		expected["consistent"] = bit(f.consistent);

		/* GenMC has lin only in Relinche's check of complete graphs: their
		 * coherence, if it holds without lin, and their consistency */
		if (!x.lin.empty()) {
			if (built.coherent) {
				queries.emplace_back("relinche");
				expected["relinche"] = bit(f.coherent);
			}
			ask(x, f, queries, expected);
			return;
		}

		if (f.porfAcyclic) {
			queries.emplace_back("views");
			auto vs = ref_->views(x);
			for (auto e = 0U; e < x.size(); e++)
				for (auto i = 0U; i < vs.size(); i++)
					expected["view " + std::to_string(i) + " " +
						 std::to_string(e)] = contents(x, vs[i], e);
		}
		auto prefix = ref_->prefix(x);
		if (f.porfAcyclic || ref_->isDepTracking()) {
			queries.emplace_back("prefix");
			for (auto e = 0U; e < x.size(); e++)
				expected["prefix " + std::to_string(e)] = contents(x, prefix, e);
		}
		if (ref_->hasRevisitPrefix()) {
			queries.emplace_back("rprefix");
			auto p = ref_->revisitPrefix(x);
			for (auto e = 0U; e < x.size(); e++)
				expected["rprefix " + std::to_string(e)] = contents(x, p, e);
		}

		for (auto e : lastCandidates(x)) {
			auto y = withoutEvent(x, e);
			auto fy = ref_->facts(y);
			if (!isValid(y, fy))
				continue;
			auto key = std::to_string(e);
			/* The check looks for cycles through E: the rest must satisfy
			 * the constraints themselves (an unless clause excuses a cycle
			 * only in coherent graphs, the ones GenMC builds) */
			if (fy.consistent) {
				queries.push_back("incremental " + key);
				expected["incremental " + key] = bit(f.consistentUnless);
			}
			if (!fy.coherent)
				continue;
			const auto &ev = x.events[e];
			if (ev.kind == Kind::R) {
				expect(queries, expected, "stores " + key, coherentStores(x, e));
			} else if (ev.kind == Kind::W) {
				expect(queries, expected, "placings " + key,
				       ev.excl ? Choices{.chosen = {x.rf[e - 1]}, .rulesOut = false}
					       : coherentPlacings(x, e));
				/* Revisits under the dependency-tracking models keep a
				 * prefix with holes, which GenMC's driver works out */
				if (f.coherent && !ref_->isDepTracking())
					revisits(x, e, prefix, queries, expected);
			}
		}

		if (ref_->numClauses() > 0)
			for (auto e : lastCandidates(x))
				errors(x, e, queries, expected);

		ask(x, f, queries, expected);
	}

	/* Prints the counts; returns whether every answer agreed */
	[[nodiscard]] auto summary(const std::string &file) const -> bool
	{
		std::cout << file << ": " << graphs_ << " graphs, " << valid_ << " GenMC can build";
		if (malformed_ > 0)
			std::cout << " (" << malformed_ << " violate the oracle's axioms)";
		std::cout << "\n";
		/* What a check's negative answers are */
		auto negative = [](const std::string &kind) -> std::string {
			if (kind == "stores" || kind == "placings" || kind == "revisits")
				return "ruling some out";
			if (kind == "errors")
				return "with an error";
			if (kind == "warnings")
				return "with a warning";
			return "false";
		};
		for (const auto &[kind, n] : checked_) {
			auto it = failed_.find(kind);
			std::cout << "  " << kind << ": " << n << " checked";
			if (auto no = negative_.find(kind); no != negative_.end())
				std::cout << " (" << no->second << " " << negative(kind) << ")";
			std::cout << ", " << (it == failed_.end() ? 0 : it->second)
				  << " disagree\n";
		}
		for (const auto &[kind, n] : failed_)
			if (!checked_.contains(kind))
				std::cout << "  " << kind << ": " << n << "\n";
		return failed_.empty();
	}

private:
	/* Asks the runner QUERIES about X and compares the answers with EXPECTED */
	void ask(const Execution &x, const Reference::Facts &f,
		 const std::vector<std::string> &queries,
		 const std::map<std::string, std::string> &expected)
	{
		auto answers = runner_->ask(x, queries);
		if (!answers) {
			report("crash", x, f, "the runner died (" + runner_->lastExit() + ")");
			return;
		}
		std::map<std::string, std::string> actual;
		for (const auto &a : *answers) {
			if (a.starts_with("error ")) {
				report("error", x, f, a);
				return;
			}
			actual.insert(normalize(a, x));
		}
		for (const auto &[key, want] : expected) {
			auto kind = key.substr(0, key.find(' '));
			checked_[kind]++;
			if (want == "0" || excluding_.contains(key) ||
			    (isErrorCheck(key) && want != "none" && !want.empty()))
				negative_[kind]++;
			auto it = actual.find(key);
			if (it == actual.end())
				report(kind, x, f, describe(key) + ": GenMC did not answer");
			else if (isErrorCheck(key) ? !errorsMatch(want, it->second)
						   : it->second != want)
				report(kind, x, f,
				       describe(key) + ": GenMC says " +
					       (isErrorCheck(key) ? errorsValue(it->second, false)
								  : value(it->second)) +
					       ", the reference semantics " +
					       (isErrorCheck(key) ? errorsValue(want, true)
								  : value(want)));
		}
		for (const auto &[key, got] : actual)
			if (!expected.contains(key))
				report("unexpected", x, f,
				       describe(key) + ": GenMC answered " + value(got) +
					       ", which nothing asked");
	}

	/* What the check of KEY calls in GenMC */
	[[nodiscard]] auto describe(const std::string &key) const -> std::string
	{
		std::istringstream ks(key);
		std::string kind;
		unsigned a = 0;
		unsigned b = 0;
		ks >> kind >> a;
		auto e = [](unsigned i) { return "e" + std::to_string(i); };
		if (kind == "consistent")
			return "isConsistent(G)";
		if (kind == "relinche")
			return "isCoherentRelinche(G)";
		if (kind == "incremental")
			return "isConsistent(" + e(a) + "), " + e(a) + " added last";
		if (kind == "view" && (ks >> b))
			return "view " + ref_->viewName(a) + " of " + e(b);
		if (kind == "prefix")
			return "calculatePrefixView(" + e(a) + ")";
		if (kind == "rprefix")
			return "calculateRevisitPrefixView(" + e(a) + ")";
		if (kind == "stores")
			return "getCoherentStores(" + e(a) + "), " + e(a) + " added last";
		if (kind == "placings")
			return "getCoherentPlacings(" + e(a) + "), " + e(a) + " added last";
		if (kind == "revisits")
			return "filterCoherentRevisits(" + e(a) + ", its revisitable reads)";
		auto order = [&] {
			return ", the events added as GenMC does with " + e(a) + " last";
		};
		unsigned i = 0;
		if (kind == "errors" && (ks >> b))
			return "checkErrors(" + e(b) + ")" + order();
		if (kind == "warnings" && (ks >> b))
			return "checkWarnings(" + e(b) + ")" + order();
		if (kind == "clause" && (ks >> b >> i) && i < ref_->numClauses())
			return "clause " + std::to_string(i) + " (" + ref_->clauseText(i) +
			       ") at " + e(b) + order();
		return key;
	}

	/* The error checks of the events GenMC checks, as it adds the events of
	 * X with E last, up to the first error, which stops the execution */
	void errors(const Execution &x, unsigned e, std::vector<std::string> &queries,
		    std::map<std::string, std::string> &expected)
	{
		auto order = x.additionOrder(e);
		/* GenMC rebuilds the state of a graph with a porf cycle in an order
		 * of its own (reconstructState()) */
		if (!order.causal)
			return;
		auto verdicts = ref_->checks(x, order.events);
		queries.push_back("errors " + std::to_string(e));
		/* CODE:W1,W2,...: clause I fails, refuted by events W1, W2, ...; any
		 * race for a clause A = 0 but with --all-races */
		auto failure = [&](unsigned i, const Reference::Verdict &v) {
			std::string s = ref_->clauseCode(i) + ":";
			if (ref_->clauseIsEmpty(i) && !opts_->allRaces)
				return s + "*";
			for (auto k = 0U; k < v.witnesses.size(); k++)
				s += (k == 0 ? "" : ",") + std::to_string(v.witnesses[k]);
			return s;
		};
		for (auto y : order.events) {
			if (!x.events[y].isChecked())
				continue;
			auto key = std::to_string(e) + " " + std::to_string(y);
			const auto &v = verdicts[y];
			std::optional<unsigned> error;
			std::string warnings;
			for (auto i = 0U; i < v.size(); i++) {
				expected["clause " + key + " " + std::to_string(i)] =
					bit(v[i].holds);
				if (v[i].holds)
					continue;
				if (!ref_->clauseIsError(i))
					warnings +=
						(warnings.empty() ? "" : " ") + failure(i, v[i]);
				else if (!error)
					error = i;
			}
			expected["errors " + key] = error ? failure(*error, v[*error]) : "none";
			if (error)
				return;
			expected["warnings " + key] = warnings;
		}
	}

	/* An answer as a reader takes it: true, false, or a set of events */
	static auto value(const std::string &v) -> std::string
	{
		if (v == "1")
			return "true";
		if (v == "0")
			return "false";
		std::istringstream vs(v);
		std::string item;
		std::string set;
		while (vs >> item)
			set += (set.empty() ? "" : ", ") + (item == "init" ? item : "e" + item);
		return "{" + set + "}";
	}

	[[nodiscard]] auto isValid(const Execution &x, const Reference::Facts &f) const -> bool
	{
		return f.wellFormed && isAtomic(x) &&
		       (ref_->isDepTracking() ? f.pporfAcyclic : f.porfAcyclic);
	}

	/* The choices a check leaves among the ones there are */
	struct Choices {
		std::vector<int> chosen;
		bool rulesOut;
	};

	void expect(std::vector<std::string> &queries, std::map<std::string, std::string> &expected,
		    const std::string &query, const Choices &c)
	{
		queries.push_back(query);
		auto key = query.substr(0, query.find(' ', query.find(' ') + 1));
		expected[key] = eventSet(c.chosen);
		if (c.rulesOut)
			excluding_.insert(key);
	}

	/* What event E's view of relation P contains: E and its P-predecessors */
	static auto contents(const Execution &x, const Pairs &p, unsigned e) -> std::string
	{
		std::vector<int> events;
		for (auto f = 0U; f < x.size(); f++)
			if ((f == e || p[f][e]) && x.events[f].kind != Kind::TB)
				events.push_back(static_cast<int>(f));
		return eventSet(events);
	}

	/* The writes read R may read from: those that leave the graph coherent */
	auto coherentStores(const Execution &x, unsigned r) -> Choices
	{
		std::vector<int> sources{-1};
		for (auto w : x.mo[x.events[r].loc])
			sources.push_back(static_cast<int>(w));
		std::vector<int> coherent;
		for (auto s : sources) {
			auto y = x;
			y.rf[r] = s;
			if (ref_->coherent(y))
				coherent.push_back(s);
		}
		return {.chosen = coherent, .rulesOut = coherent.size() < sources.size()};
	}

	/*
	 * The reads write W, just added to coherent graph X, may revisit: of
	 * the reads of its location outside its prefix (getRevisitable()), the
	 * ones that leave the revisited graph coherent. A revisit of read R
	 * keeps the events added up to R and W's prefix (getRevisitView()),
	 * and R reads from W.
	 */
	void revisits(const Execution &x, unsigned w, const Pairs &prefix,
		      std::vector<std::string> &queries,
		      std::map<std::string, std::string> &expected)
	{
		auto order = x.additionOrder(w).events;
		std::vector<unsigned> stamp(x.size());
		for (auto i = 0U; i < order.size(); i++)
			stamp[order[i]] = i;
		std::string query = "revisits " + std::to_string(w);
		std::vector<int> kept;
		auto candidates = 0U;
		for (auto r = 0U; r < x.size(); r++) {
			const auto &ev = x.events[r];
			if (ev.kind != Kind::R || ev.loc != x.events[w].loc || prefix[r][w])
				continue;
			query += " " + std::to_string(r);
			candidates++;
			std::vector<bool> keep(x.size());
			for (auto e = 0U; e < x.size(); e++)
				keep[e] = stamp[e] <= stamp[r] || prefix[e][w] || e == w;
			auto y = x;
			y.rf[r] = static_cast<int>(w);
			if (ref_->coherent(restrictTo(y, keep)))
				kept.push_back(static_cast<int>(r));
		}
		if (candidates > 0)
			expect(queries, expected, query,
			       {.chosen = kept, .rulesOut = kept.size() < candidates});
	}

	/* The writes write W may follow in co: those that leave the graph
	 * coherent, and RMWs atomic */
	auto coherentPlacings(const Execution &x, unsigned w) -> Choices
	{
		const auto &order = x.mo[x.events[w].loc];
		std::vector<unsigned> others;
		for (auto v : order)
			if (v != w)
				others.push_back(v);
		std::vector<int> placings;
		for (auto at = 0U; at <= others.size(); at++) {
			auto y = x;
			auto &o = y.mo[x.events[w].loc];
			o = others;
			o.insert(o.begin() + at, w);
			if (isAtomic(y) && ref_->coherent(y))
				placings.push_back(at == 0 ? -1 : static_cast<int>(others[at - 1]));
		}
		return {.chosen = placings, .rulesOut = placings.size() < others.size() + 1};
	}

	void report(const std::string &kind, const Execution &x, const Reference::Facts &f,
		    const std::string &what)
	{
		auto n = ++failed_[kind];
		if (n > opts_->shown)
			return;
		std::cout << "DISAGREE " << what << "\n"
			  << "  graph (" << (f.coherent ? "coherent" : "incoherent")
			  << (f.consistent ? ", consistent" : ", inconsistent")
			  << (f.consistentUnless != f.consistent ? " but for its unless clauses"
								 : "")
			  << "):\n";
		x.print(std::cout, "    ");
		std::cout.flush();
	}

	Reference *ref_;
	Runner *runner_;
	const GenMCOptions *opts_;
	unsigned graphs_ = 0;
	unsigned valid_ = 0;
	unsigned malformed_ = 0;
	std::map<std::string, unsigned> checked_;
	/* Checks whose answer is false, or rules some choice out */
	std::map<std::string, unsigned> negative_;
	/* This graph's checks that rule some choice out */
	std::set<std::string> excluding_;
	std::map<std::string, unsigned> failed_;
};

/* The events of the model's graphs: the orderings and labels it tells apart */
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

/*
 * The events of the graphs of the memory-error checks: allocations, frees,
 * retires and hazard-pointer protections (through HAZARDS hazard pointers),
 * plain accesses, and atomic ones of the orderings the model's hb tells
 * apart
 */
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

/* The model a kat/NAME-genmc.kat defines: NAME */
auto modelOf(const std::string &file) -> std::string
{
	auto stem = std::filesystem::path(file).stem().string();
	if (stem.ends_with("-genmc"))
		stem.resize(stem.size() - 6);
	return stem;
}

} // namespace

auto checkGenMC(const std::string &file, const GenMCOptions &opts) -> bool
{
	/* A runner that dies must not take us down with it */
	std::signal(SIGPIPE, SIG_IGN); // NOLINT(cert-err33-c)

	ParsingDriver driver;
	if (driver.parse(file) != 0) {
		std::cerr << file << ": parse error\n";
		return false;
	}
	auto model = modelOf(file);
	Reference ref(driver.takeModule());
	Runner runner(opts.runner, model);
	Comparison cmp(ref, runner, opts);

	auto count = 0U;
	auto within = [&]() { return opts.limit == 0 || count < opts.limit; };
	auto check = [&](const Execution &x) {
		count++;
		cmp.check(x);
		if (opts.verbose && count % 10000 == 0)
			std::cout << "... " << count << " graphs\n" << std::flush;
		return within();
	};

	if (!opts.graphs.empty()) {
		for (const auto &g : opts.graphs) {
			std::ifstream is(g);
			std::string error;
			auto x = Execution::parse(is, error);
			if (!x) {
				std::cerr << g << ": " << error << "\n";
				return false;
			}
			check(*x);
		}
		return cmp.summary(file);
	}

	auto alphabet = alphabetOf(model);
	auto exhaustive = alphabet;
	exhaustive.threadEvents = false;
	exhaustive.methods = false;
	auto enumerated = 0UL;
	auto visit = [&](const Execution &x) {
		if (enumerated++ % opts.shards != opts.shard || opts.count)
			return true;
		return check(x);
	};
	enumerate(exhaustive, opts.bounds, ref.isDepTracking(), visit);
	/* The graphs of the memory-error checks, up to a bound of their own:
	 * every one but those of the model's own instructions, which the
	 * model's alphabet has (TSO's and RA's have no plain accesses) */
	auto heap = heapAlphabetOf(model, 1);
	auto ownInstruction = [&](const Execution::Event &ev) {
		return ev.kind == Kind::TB ||
		       std::ranges::any_of(exhaustive.instructions, [&](const auto &i) {
			       return i.kind == ev.kind && i.order == ev.order && !i.rmw;
		       });
	};
	enumerate(heap, opts.heapBounds, ref.isDepTracking(), [&](const Execution &x) {
		return std::ranges::all_of(x.events, ownInstruction) || visit(x);
	});
	if (opts.count) {
		std::cout << file << ": " << enumerated << " graphs\n";
		return true;
	}

	/* Half the random graphs are built as GenMC builds them, coherent at
	 * every step; the others are any the axioms allow. Some have a heap */
	std::mt19937 rng(opts.seed);
	auto coherent = [&](const Execution &x) { return ref.coherent(x); };
	auto withHeap = alphabet;
	for (const auto &i : heapAlphabetOf(model, 2).instructions)
		if (std::ranges::none_of(withHeap.instructions, [&](const auto &j) {
			    return j.kind == i.kind && j.order == i.order && !j.rmw &&
				   j.flavor == Flavor::Plain && j.hp == i.hp;
		    }))
			withHeap.instructions.push_back(i);
	for (auto i = 0U; i < opts.random && within(); i++) {
		const auto &a = i % 4 < 2 ? alphabet : withHeap;
		check(i % 2 == 0 ? randomBuiltExecution(a, opts.randomBounds, rng, coherent)
				 : randomExecution(a, opts.randomBounds, ref.isDepTracking(), rng));
	}
	return cmp.summary(file);
}

} // namespace oracle
