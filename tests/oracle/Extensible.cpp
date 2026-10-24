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

#include "Extensible.hpp"

#include "Enumerate.hpp"
#include "Execution.hpp"
#include "Reference.hpp"

#include "ParsingDriver.hpp"

#include <algorithm>
#include <fstream>
#include <iostream>
#include <string>
#include <utility>
#include <vector>

namespace oracle {

namespace {

auto name(unsigned event) -> std::string { return "e" + std::to_string(event); }

/* Whether EVENT has a po-successor in GRAPH */
auto hasPoSuccessor(const Execution &graph, unsigned event) -> bool
{
	return event + 1 < graph.size() &&
	       graph.events[event + 1].thread == graph.events[event].thread;
}

/*
 * Whether GenMC may add EVENT to GRAPH without it last, as far as GRAPH's
 * structure tells: nothing reads from EVENT, and it is neither part of an
 * RMW (whose write GenMC adds right after its read) nor a thread start
 * (which every view contains). Nothing may follow it in GenMC's prefix
 * either.
 */
auto isAddable(const Execution &graph, unsigned event) -> bool
{
	const auto &label = graph.events[event];
	return label.kind != Kind::TB && !label.excl &&
	       std::ranges::none_of(
		       graph.rf, [&](auto src) -> bool { return src == static_cast<int>(event); });
}

/* Whether something follows EVENT in the prefix relation PREFIX */
auto hasPrefixSuccessor(const Pairs &prefix, unsigned event) -> bool
{
	return std::ranges::any_of(prefix[event], [](bool b) -> bool { return b; });
}

/* A way to add an event: where it reads from, or what it follows in mo */
struct Attachment {
	Execution graph;
	std::string how;
};

/*
 * The graphs that differ from GRAPH only in where EVENT reads from (a read)
 * or in its place in mo (a write), and keep rf, mo and fr respecting po: the
 * ways GenMC may add EVENT to GRAPH without it. GRAPH is among them.
 */
auto attachments(const Execution &graph, unsigned event) -> std::vector<Attachment>
{
	std::vector<Attachment> result;
	const auto &label = graph.events[event];
	auto add = [&](Execution way, std::string how) -> void {
		if (respectsPo(way))
			result.push_back({.graph = std::move(way), .how = std::move(how)});
	};
	if (label.kind == Kind::R) {
		auto way = graph;
		way.rf[event] = -1;
		add(way, "reading from init");
		for (auto write : graph.mo[label.loc]) {
			way.rf[event] = static_cast<int>(write);
			add(way, "reading from " + name(write));
		}
	} else if (label.kind == Kind::W) {
		std::vector<unsigned> others;
		for (auto write : graph.mo[label.loc])
			if (write != event)
				others.push_back(write);
		for (auto place = 0U; place <= others.size(); place++) {
			auto way = graph;
			auto &order = way.mo[label.loc];
			order = others;
			order.insert(order.begin() + place, event);
			add(way, place == 0 ? "first in mo"
					    : "after " + name(others[place - 1]) + " in mo");
		}
	} else {
		add(graph, "as it is");
	}
	return result;
}

/* Whether an event po-after EVENT in GRAPH accesses EVENT's location */
auto hasLaterAccess(const Execution &graph, unsigned event) -> bool
{
	const auto &label = graph.events[event];
	if (!label.isAccess())
		return false;
	for (auto later = event + 1;
	     later < graph.size() && graph.events[later].thread == label.thread; later++)
		if (graph.events[later].isAccess() && graph.events[later].loc == label.loc)
			return true;
	return false;
}

/* The way GenMC adds EVENT maximally: a read reads from the last write in mo
 * (from init if there is none), a write is last in mo */
auto maximalAttachment(const Execution &graph, unsigned event) -> Attachment
{
	auto way = graph;
	const auto &label = graph.events[event];
	if (label.kind == Kind::R) {
		const auto &order = graph.mo[label.loc];
		way.rf[event] = order.empty() ? -1 : static_cast<int>(order.back());
		return {.graph = std::move(way),
			.how = order.empty() ? "reading from init"
					     : "reading from " + name(order.back())};
	}
	if (label.kind == Kind::W) {
		auto &order = way.mo[label.loc];
		std::erase(order, event);
		order.push_back(event);
		return {.graph = std::move(way), .how = "last in mo"};
	}
	return {.graph = std::move(way), .how = "as it is"};
}

/* Whether GRAPH and OTHER attach EVENT the same way */
auto sameAttachment(const Execution &graph, const Execution &other, unsigned event) -> bool
{
	const auto &label = graph.events[event];
	if (label.kind == Kind::R)
		return graph.rf[event] == other.rf[event];
	if (label.kind == Kind::W)
		return graph.mo[label.loc] == other.mo[label.loc];
	return true;
}

class Extensibility {

public:
	Extensibility(Reference &ref, const ExtensibleOptions &opts) : ref_(&ref), opts_(&opts) {}

	/*
	 * Checks the events of GRAPH that GenMC may add last. With ONCE, each
	 * graph without the event is checked for only one of the graphs that
	 * attach the event to it (the first, in attachments() order): the
	 * others are enumerated too
	 */
	void check(const Execution &graph, bool once)
	{
		graphs_++;
		std::vector<std::pair<unsigned, std::vector<Attachment>>> candidates;
		for (auto event = 0U; event < graph.size(); event++) {
			if (!isAddable(graph, event))
				continue;
			auto ways = attachments(graph, event);
			if (once &&
			    (ways.empty() || !sameAttachment(ways.front().graph, graph, event)))
				continue;
			candidates.emplace_back(event, std::move(ways));
		}
		if (candidates.empty() && once)
			return;

		auto [facts, prefix] = ref_->factsWithPrefix(graph);
		if (!isValid(graph, facts)) {
			/* A graph given explicitly says why it is left out */
			if (!once)
				std::cout
					<< "not a graph GenMC builds: " << whyInvalid(graph, facts)
					<< "\n";
			return;
		}
		for (const auto &[event, ways] : candidates)
			if (!hasPrefixSuccessor(prefix, event))
				checkEvent(graph, facts, event, ways);
	}

	/* Prints the counts; returns whether no event failed to be added (with
	 * MAXIMAL, nor one with no later access to its location to be added
	 * maximally) */
	[[nodiscard]] auto summary(const std::string &file) const -> bool
	{
		std::cout << file << ": " << graphs_ << " graphs; " << checked_
			  << " events GenMC may add to a consistent graph (" << holes_
			  << " into a hole), " << failed_ << " cannot be added consistently; "
			  << maximalChecked_ << " have no later access to their location, "
			  << maximalFailed_
			  << " of them cannot be added maximally and consistently\n";
		return failed_ == 0 && (!opts_->maximal || maximalFailed_ == 0);
	}

private:
	/* Checks EVENT of GRAPH, which GenMC may add last: if the rest is
	 * consistent, one of WAYS of adding it is, and, when nothing after it
	 * accesses its location, the maximal one */
	void checkEvent(const Execution &graph, const Reference::Facts &facts, unsigned event,
			const std::vector<Attachment> &ways)
	{
		auto rest = withoutEvent(graph, event);
		if (!isConsistent(rest, ref_->facts(rest)))
			return;
		checked_++;
		auto hole = hasPoSuccessor(graph, event);
		if (hole)
			holes_++;
		/* GRAPH is one of the ways, whose facts are known */
		auto consistent = [&](const Attachment &way) -> bool {
			return isConsistent(way.graph, sameAttachment(way.graph, graph, event)
							       ? facts
							       : ref_->facts(way.graph));
		};
		if (!hasLaterAccess(graph, event)) {
			maximalChecked_++;
			auto way = maximalAttachment(graph, event);
			if (!consistent(way)) {
				maximalFailed_++;
				if (opts_->maximal)
					report(graph, event, hole, {way}, maximalFailed_);
			}
		}
		if (std::ranges::none_of(ways, consistent)) {
			failed_++;
			if (!opts_->maximal)
				report(graph, event, hole, ways, failed_);
		}
	}

	[[nodiscard]] auto isValid(const Execution &graph, const Reference::Facts &facts) const
		-> bool
	{
		return facts.wellFormed && isAtomic(graph) &&
		       (ref_->isDepTracking() ? facts.pporfAcyclic : facts.porfAcyclic);
	}

	[[nodiscard]] auto isConsistent(const Execution &graph, const Reference::Facts &facts) const
		-> bool
	{
		return isValid(graph, facts) && facts.consistent && facts.coherent;
	}

	static auto whyInvalid(const Execution &graph, const Reference::Facts &facts) -> const
		char *
	{
		if (!facts.wellFormed)
			return "it violates the oracle's axioms";
		if (!isAtomic(graph))
			return "an RMW is not atomic";
		return "it has a cycle of GenMC's prefix";
	}

	/* What is wrong with GRAPH, which is not consistent */
	[[nodiscard]] auto whyInconsistent(const Execution &graph) const -> const char *
	{
		auto facts = ref_->facts(graph);
		if (!isValid(graph, facts))
			return "not a graph GenMC builds";
		if (!facts.coherent)
			return "incoherent";
		return "inconsistent";
	}

	void report(const Execution &graph, unsigned event, bool hole,
		    const std::vector<Attachment> &ways, unsigned count) const
	{
		if (count > opts_->shown)
			return;
		std::cout << (opts_->maximal ? "NOT MAXIMALLY EXTENSIBLE: " : "NOT EXTENSIBLE: ")
			  << name(event) << (hole ? ", which has po-successors," : "")
			  << " cannot be added "
			  << (opts_->maximal ? "maximally and consistently" : "consistently")
			  << " to the rest of this graph, which is consistent:\n";
		graph.print(std::cout, "    ");
		std::cout << "  "
			  << (opts_->maximal ? std::string("added maximally")
					     : "each way " + name(event) + " can be added")
			  << ":\n";
		for (const auto &way : ways)
			std::cout << "    " << way.how << ": " << whyInconsistent(way.graph)
				  << "\n";
		std::cout.flush();
	}

	Reference *ref_;
	const ExtensibleOptions *opts_;
	unsigned graphs_ = 0;
	unsigned checked_ = 0;
	unsigned holes_ = 0;
	unsigned failed_ = 0;
	unsigned maximalChecked_ = 0;
	unsigned maximalFailed_ = 0;
};

} // namespace

auto checkExtensible(const std::string &file, const ExtensibleOptions &opts) -> bool
{
	ParsingDriver driver;
	if (driver.parse(file) != 0) {
		std::cerr << file << ": parse error\n";
		return false;
	}
	Reference ref(driver.takeModule());
	Extensibility ext(ref, opts);

	if (!opts.graphs.empty()) {
		for (const auto &path : opts.graphs) {
			std::ifstream input(path);
			std::string error;
			auto graph = Execution::parse(input, error);
			if (!graph) {
				std::cerr << path << ": " << error << "\n";
				return false;
			}
			canonicalizeLocations(*graph);
			ext.check(*graph, false);
		}
	} else {
		auto alphabet = alphabetOf(modelOf(file));
		alphabet.threadEvents = false;
		alphabet.methods = false;
		constexpr auto progressEvery = 100000UL;
		auto count = 0UL;
		enumerate(alphabet, opts.bounds, ref.isDepTracking(),
			  [&](const Execution &graph) -> bool {
				  ext.check(graph, true);
				  if (opts.verbose && ++count % progressEvery == 0)
					  std::cout << "... " << count << " graphs\n" << std::flush;
				  return true;
			  });
	}
	auto extensible = ext.summary(file);
	if (opts.refutable && extensible)
		std::cout << file << ": expected a counterexample\n";
	return extensible != opts.refutable;
}

} // namespace oracle
