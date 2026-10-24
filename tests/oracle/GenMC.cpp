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

#include "Reference.hpp"

#include "ParsingDriver.hpp"

#include <poll.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

#include <algorithm>
#include <array>
#include <csignal>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <map>
#include <memory>
#include <optional>
#include <random>
#include <set>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

namespace oracle {

namespace {

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

/* An answer "key: list" with its list normalized; thread starts dropped from views */
auto normalize(const std::string &answer, const Execution &x) -> std::pair<std::string, std::string>
{
	auto colon = answer.find(':');
	if (colon == std::string::npos) {
		auto space = answer.rfind(' ');
		return {answer.substr(0, space), answer.substr(space + 1)};
	}
	auto key = answer.substr(0, colon);
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

		ask(x, f, queries, expected);
	}

	/* Prints the counts; returns whether every answer agreed */
	[[nodiscard]] auto summary(const std::string &file) const -> bool
	{
		std::cout << file << ": " << graphs_ << " graphs, " << valid_ << " GenMC can build";
		if (malformed_ > 0)
			std::cout << " (" << malformed_ << " violate the oracle's axioms)";
		std::cout << "\n";
		for (const auto &[kind, n] : checked_) {
			auto it = failed_.find(kind);
			std::cout << "  " << kind << ": " << n << " checked";
			if (auto no = negative_.find(kind); no != negative_.end())
				std::cout << " (" << no->second
					  << (kind == "stores" || kind == "placings" ||
							      kind == "revisits"
						      ? " ruling some out)"
						      : " false)");
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
			if (a.starts_with("error")) {
				report("error", x, f, a);
				return;
			}
			actual.insert(normalize(a, x));
		}
		for (const auto &[key, want] : expected) {
			auto kind = key.substr(0, key.find(' '));
			checked_[kind]++;
			if (want == "0" || excluding_.contains(key))
				negative_[kind]++;
			auto it = actual.find(key);
			if (it == actual.end())
				report(kind, x, f, describe(key) + ": GenMC did not answer");
			else if (it->second != want)
				report(kind, x, f,
				       describe(key) + ": GenMC says " + value(it->second) +
					       ", the reference semantics " + value(want));
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
		return key;
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
	enumerate(exhaustive, opts.bounds, ref.isDepTracking(), [&](const Execution &x) {
		if (enumerated++ % opts.shards != opts.shard || opts.count)
			return true;
		return check(x);
	});
	if (opts.count) {
		std::cout << file << ": " << enumerated << " graphs\n";
		return true;
	}

	/* Half the random graphs are built as GenMC builds them, coherent at
	 * every step; the others are any the axioms allow */
	std::mt19937 rng(opts.seed);
	auto coherent = [&](const Execution &x) { return ref.coherent(x); };
	for (auto i = 0U; i < opts.random && within(); i++)
		check(i % 2 == 0 ? randomBuiltExecution(alphabet, opts.randomBounds, rng, coherent)
				 : randomExecution(alphabet, opts.randomBounds, ref.isDepTracking(),
						   rng));
	return cmp.summary(file);
}

} // namespace oracle
