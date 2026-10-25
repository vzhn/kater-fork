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

#include "Enumerate.hpp"

#include <algorithm>
#include <numeric>
#include <utility>

namespace oracle {

using Event = Execution::Event;

auto isAtomic(const Execution &x) -> bool
{
	for (auto w = 1U; w < x.size(); w++) {
		const auto &ev = x.events[w];
		if (ev.kind != Kind::W || !ev.excl)
			continue;
		const auto &order = x.mo[ev.loc];
		auto src = x.rf[w - 1];
		auto at = std::ranges::find(order, w) - order.begin();
		auto want = src < 0 ? 0 : (std::ranges::find(order, src) - order.begin()) + 1;
		if (at != want)
			return false;
	}
	return true;
}

auto isHeapWellFormed(const Execution &x) -> bool
{
	auto n = x.size();
	auto freed = [](const Execution::Event &ev) {
		return ev.kind == Kind::Free || ev.kind == Kind::HpRetire ||
		       ev.kind == Kind::HpProtect;
	};
	for (const auto &ev : x.events)
		if (freed(ev) && !x.allocationOf(ev.loc))
			return false;

	std::vector<std::vector<unsigned>> succs(n);
	for (auto e = 1U; e < n; e++)
		if (x.events[e].thread == x.events[e - 1].thread)
			succs[e - 1].push_back(e);
	for (auto r = 0U; r < n; r++)
		if (x.rf[r] >= 0)
			succs[x.rf[r]].push_back(r);
	for (const auto *edges : {&x.tc, &x.tj})
		for (const auto &[a, b] : *edges)
			succs[a].push_back(b);

	for (auto a = 0U; a < n; a++) {
		const auto &alloc = x.events[a];
		if (alloc.kind != Kind::Alloc)
			continue;
		std::vector<bool> reached(n, false);
		std::vector<unsigned> todo{a};
		while (!todo.empty()) {
			auto e = todo.back();
			todo.pop_back();
			for (auto s : succs[e])
				if (!reached[s]) {
					reached[s] = true;
					todo.push_back(s);
				}
		}
		for (auto e = 0U; e < n; e++) {
			const auto &ev = x.events[e];
			if (e != a && ev.hasLocation() && ev.loc == alloc.loc &&
			    (!reached[e] || ev.kind == Kind::Alloc))
				return false;
		}
	}
	return true;
}

auto hasPorfCycle(const Execution &x) -> bool
{
	auto n = x.size();
	std::vector<std::vector<unsigned>> succs(n);
	std::vector<unsigned> preds(n, 0);
	auto edge = [&](unsigned a, unsigned b) {
		succs[a].push_back(b);
		preds[b]++;
	};
	for (auto e = 1U; e < n; e++)
		if (x.events[e].thread == x.events[e - 1].thread)
			edge(e - 1, e);
	for (auto r = 0U; r < n; r++)
		if (x.rf[r] >= 0)
			edge(static_cast<unsigned>(x.rf[r]), r);
	for (const auto *edges : {&x.tc, &x.tj, &x.lin})
		for (const auto &[a, b] : *edges)
			edge(a, b);

	std::vector<unsigned> ready;
	for (auto e = 0U; e < n; e++)
		if (preds[e] == 0)
			ready.push_back(e);
	auto seen = 0U;
	while (!ready.empty()) {
		auto e = ready.back();
		ready.pop_back();
		seen++;
		for (auto s : succs[e])
			if (--preds[s] == 0)
				ready.push_back(s);
	}
	return seen < n;
}

void canonicalizeLocations(Execution &x)
{
	std::vector<int> rename(x.numLocations(), -1);
	auto next = 0;
	for (auto &ev : x.events) {
		if (!ev.hasLocation())
			continue;
		if (rename[ev.loc] < 0)
			rename[ev.loc] = next++;
		ev.loc = rename[ev.loc];
	}
	std::vector<std::vector<unsigned>> mo(next);
	for (auto l = 0U; l < rename.size(); l++)
		if (rename[l] >= 0)
			mo[rename[l]] = std::move(x.mo[l]);
	x.mo = std::move(mo);
}

auto restrictTo(const Execution &x, const std::vector<bool> &keep) -> Execution
{
	std::vector<int> index(x.size(), -1);
	Execution y;
	for (auto f = 0U; f < x.size(); f++) {
		if (!keep[f])
			continue;
		index[f] = static_cast<int>(y.size());
		y.events.push_back(x.events[f]);
	}
	for (auto f = 0U; f < x.size(); f++) {
		if (!keep[f])
			continue;
		auto w = x.rf[f];
		y.rf.push_back(w < 0 ? -1 : index[w]);
		/* The read of an RMW whose write is gone is no longer exclusive
		 * (GenMC's isRMW() asks for the write) */
		const auto &ev = x.events[f];
		if (ev.kind == Kind::R && ev.excl && (f + 1 == x.size() || !keep[f + 1]))
			y.events[index[f]].excl = false;
	}
	for (const auto &order : x.mo) {
		std::vector<unsigned> o;
		for (auto w : order)
			if (keep[w])
				o.push_back(static_cast<unsigned>(index[w]));
		y.mo.push_back(std::move(o));
	}
	auto edges = [&](const Execution::Edges &from, Execution::Edges &to) {
		for (const auto &[a, b] : from)
			if (keep[a] && keep[b])
				to.emplace_back(index[a], index[b]);
	};
	edges(x.ctrl, y.ctrl);
	edges(x.addr, y.addr);
	edges(x.data, y.data);
	edges(x.pctrl, y.pctrl);
	edges(x.tc, y.tc);
	edges(x.tj, y.tj);
	edges(x.lin, y.lin);
	canonicalizeLocations(y);
	return y;
}

auto withoutEvent(const Execution &x, unsigned e) -> Execution
{
	std::vector<bool> keep(x.size(), true);
	keep[e] = false;
	return restrictTo(x, keep);
}

namespace {

/* Whether fr respects po: no read reads a write older than one po-before it */
auto frRespectsPo(const Execution &x) -> bool
{
	for (auto r = 0U; r < x.size(); r++) {
		if (x.events[r].kind != Kind::R)
			continue;
		for (auto w = r; w-- > 0 && x.events[w].thread == x.events[r].thread;) {
			const auto &ev = x.events[w];
			if (ev.kind != Kind::W || ev.loc != x.events[r].loc)
				continue;
			auto src = x.rf[r];
			if (src < 0 || (src != static_cast<int>(w) &&
					!x.moBefore(w, static_cast<unsigned>(src))))
				return false;
		}
	}
	return true;
}

/* Whether ORDER, a coherence order of a location, respects po */
auto moRespectsPo(const Execution &x, const std::vector<unsigned> &order) -> bool
{
	for (auto i = 0U; i < order.size(); i++)
		for (auto j = i + 1; j < order.size(); j++)
			if (x.events[order[i]].thread == x.events[order[j]].thread &&
			    order[i] > order[j])
				return false;
	return true;
}

/* Whether instruction I's events have a location (fences and thread events
 * have none) */
auto isLocated(const Alphabet::Instruction &i) -> bool
{
	return Event{.kind = i.kind}.hasLocation();
}

/* The events of instruction I of THREAD, at location LOC */
auto eventsOf(const Alphabet::Instruction &i, unsigned thread, int loc) -> std::vector<Event>
{
	const Event ev{.thread = thread,
		       .kind = i.kind,
		       .order = i.order,
		       .loc = isLocated(i) ? loc : -1,
		       .excl = i.rmw,
		       .flavor = i.flavor,
		       .fence = i.fence,
		       .hp = i.hp};
	if (!i.rmw)
		return {ev};
	auto w = ev;
	w.kind = Kind::W;
	return {ev, w};
}

/* Whether GenMC gives an event's label dependencies: not to thread starts or
 * method calls, nor to the write of an RMW (made from its read) */
auto hasDeps(const Event &ev) -> bool
{
	return ev.kind != Kind::TB && ev.kind != Kind::MethodBegin && ev.kind != Kind::MethodEnd &&
	       !(ev.kind == Kind::W && ev.excl);
}

auto threadStart(unsigned thread) -> Event
{
	return {.thread = thread, .kind = Kind::TB, .order = Order::ACQ};
}

class Enumerator {

public:
	Enumerator(const Alphabet &a, const Bounds &b, bool cycles,
		   const std::function<bool(const Execution &)> &visit)
		: a_(&a), b_(b), cycles_(cycles), visit_(&visit)
	{
	}

	auto run() -> bool
	{
		instructions(0, 0, 0, 0);
		return !stop_;
	}

private:
	/* Adds instructions to THREAD, which has COUNT of them */
	void instructions(unsigned thread, unsigned used, unsigned locs, unsigned count)
	{
		if (stop_)
			return;
		if (count > 0) {
			finishEvents();
			if (thread + 1 < b_.threads && used < b_.events) {
				x_.events.push_back(threadStart(thread + 1));
				instructions(thread + 1, used, locs, 0);
				x_.events.pop_back();
			}
		}
		for (const auto &i : a_->instructions) {
			auto size = i.rmw ? 2U : 1U;
			if (used + size > b_.events)
				continue;
			auto maxLoc = isLocated(i) ? std::min(locs + 1, b_.locations) : 1U;
			for (auto l = 0U; l < maxLoc; l++) {
				auto evs = eventsOf(i, thread, static_cast<int>(l));
				x_.events.insert(x_.events.end(), evs.begin(), evs.end());
				instructions(thread, used + size,
					     isLocated(i) ? std::max(locs, l + 1) : locs,
					     count + 1);
				x_.events.resize(x_.events.size() - evs.size());
			}
		}
	}

	void finishEvents()
	{
		auto locs = 0;
		for (const auto &ev : x_.events)
			locs = std::max(locs, ev.loc + 1);
		x_.rf.assign(x_.size(), -1);
		x_.mo.assign(locs, {});
		for (auto e = 0U; e < x_.size(); e++)
			if (x_.events[e].kind == Kind::W)
				x_.mo[x_.events[e].loc].push_back(e);
		chooseRf(0);
	}

	void chooseRf(unsigned r)
	{
		if (stop_)
			return;
		while (r < x_.size() && x_.events[r].kind != Kind::R)
			r++;
		if (r == x_.size()) {
			chooseMo(0);
			return;
		}
		x_.rf[r] = -1;
		chooseRf(r + 1);
		for (auto w : x_.mo[x_.events[r].loc]) {
			/* rf never goes backwards in po */
			if (x_.events[w].thread == x_.events[r].thread && w > r)
				continue;
			x_.rf[r] = static_cast<int>(w);
			chooseRf(r + 1);
		}
		x_.rf[r] = -1;
	}

	void chooseMo(unsigned l)
	{
		if (stop_)
			return;
		if (l == x_.numLocations()) {
			if (!frRespectsPo(x_) || !isAtomic(x_))
				return;
			chooseDeps(0);
			return;
		}
		auto &order = x_.mo[l];
		std::ranges::sort(order);
		do {
			if (moRespectsPo(x_, order))
				chooseMo(l + 1);
		} while (!stop_ && std::ranges::next_permutation(order).found);
		std::ranges::sort(order);
	}

	/* A dependency on the closest read before each event, if any */
	void chooseDeps(unsigned e)
	{
		if (stop_)
			return;
		while (e < x_.size() && closestRead(e) < 0)
			e++;
		if (a_->deps.empty() || e == x_.size()) {
			finish();
			return;
		}
		chooseDeps(e + 1);
		auto r = static_cast<unsigned>(closestRead(e));
		for (auto dep : a_->deps) {
			auto &edges = x_.*dep;
			edges.emplace_back(r, e);
			chooseDeps(e + 1);
			edges.pop_back();
		}
	}

	/* The read right before E in its thread, which E may depend on */
	[[nodiscard]] auto closestRead(unsigned e) const -> int
	{
		const auto &ev = x_.events[e];
		if (!hasDeps(ev))
			return -1;
		for (auto r = e; r-- > 0 && x_.events[r].thread == ev.thread;)
			if (x_.events[r].kind == Kind::R)
				return static_cast<int>(r);
		return -1;
	}

	void finish()
	{
		if ((!cycles_ && hasPorfCycle(x_)) || !isHeapWellFormed(x_))
			return;
		if (!(*visit_)(x_))
			stop_ = true;
	}

	const Alphabet *a_;
	Bounds b_;
	bool cycles_;
	const std::function<bool(const Execution &)> *visit_;
	Execution x_;
	bool stop_ = false;
};

} // namespace

auto enumerate(const Alphabet &alphabet, const Bounds &bounds, bool cycles,
	       const std::function<bool(const Execution &)> &visit) -> bool
{
	return Enumerator(alphabet, bounds, cycles, visit).run();
}

auto respectsPo(const Execution &graph) -> bool
{
	for (auto read = 0U; read < graph.size(); read++) {
		auto src = graph.rf[read];
		/* rf never goes backwards in po */
		if (std::cmp_greater(src, read) &&
		    graph.events[src].thread == graph.events[read].thread)
			return false;
	}
	return frRespectsPo(graph) &&
	       std::ranges::all_of(
		       graph.mo,
		       [&](const auto &order) -> bool { return moRespectsPo(graph, order); }) &&
	       isAtomic(graph);
}

namespace {

/* Picks a coherence order of each location that respects po and atomicity:
 * write by write, among the ones whose po-earlier writes are placed, and
 * an RMW's write right after the write its read reads */
auto randomMo(Execution &x, std::mt19937 &rng) -> bool
{
	for (auto l = 0U; l < x.numLocations(); l++) {
		auto remaining = x.mo[l];
		std::vector<unsigned> order;
		auto sourceOf = [&](unsigned w) {
			return x.events[w].excl ? x.rf[w - 1] : -2; /* -2: no RMW */
		};
		while (!remaining.empty()) {
			auto last = order.empty() ? -1 : static_cast<int>(order.back());
			auto ready = [&](unsigned w) {
				return std::ranges::none_of(remaining, [&](auto v) {
					return v < w && x.events[v].thread == x.events[w].thread;
				});
			};
			std::vector<unsigned> candidates;
			for (auto w : remaining)
				if (sourceOf(w) == last)
					candidates.push_back(w);
			if (candidates.empty())
				for (auto w : remaining)
					if (sourceOf(w) == -2)
						candidates.push_back(w);
			std::erase_if(candidates, [&](auto w) { return !ready(w); });
			if (candidates.empty())
				return false;
			auto w = candidates[std::uniform_int_distribution<size_t>(
				0, candidates.size() - 1)(rng)];
			order.push_back(w);
			std::erase(remaining, w);
		}
		x.mo[l] = std::move(order);
	}
	return isAtomic(x) && frRespectsPo(x);
}

/* A random number below N */
auto pick(std::mt19937 &rng, size_t n) -> unsigned
{
	return std::uniform_int_distribution<unsigned>(0, static_cast<unsigned>(n) - 1)(rng);
}

/* The events of a random graph, with its dependencies, thread events and
 * lin; every read reads the initial value, every co is in thread order */
auto randomShape(const Alphabet &a, const Bounds &b, std::mt19937 &rng) -> Execution
{
	auto pick = [&](size_t n) { return oracle::pick(rng, n); };
	auto coin = [&](unsigned outOf) { return pick(outOf) == 0; };

	/* The instructions of each thread, of a few kinds: graphs of one
	 * ordering, of a few fences, ... (the cycles a model rules out need
	 * several events of the same kind). Allocations are placed below */
	std::vector<const Alphabet::Instruction *> kinds;
	const Alphabet::Instruction *alloc = nullptr;
	for (const auto &i : a.instructions)
		if (i.kind == Kind::Alloc)
			alloc = &i;
	if (coin(2)) {
		auto order = a.instructions[pick(a.instructions.size())].order;
		for (const auto &i : a.instructions)
			if (i.order == order && i.kind != Kind::Alloc)
				kinds.push_back(&i);
	}
	while (kinds.empty())
		for (const auto &i : a.instructions)
			if (i.kind != Kind::Alloc && coin(4))
				kinds.push_back(&i);
	/* Small graphs are the exhaustive ones' business: from half the bound up */
	auto threads = 1 + pick(b.threads);
	auto budget = ((b.events + 1) / 2) + pick((b.events / 2) + 1);
	std::vector<std::vector<Event>> code(threads);
	for (auto used = 0U; used < budget;) {
		const auto &i = *kinds[pick(kinds.size())];
		auto t = pick(threads);
		auto evs = eventsOf(i, t, static_cast<int>(pick(b.locations)));
		code[t].insert(code[t].end(), evs.begin(), evs.end());
		used += evs.size();
	}
	std::erase_if(code, [](auto &c) { return c.empty(); });
	threads = code.size();

	/* Per event of each thread's code: the child of a thread event, or
	 * the method call of a begin or end */
	std::vector<std::vector<int>> tagOf(threads);
	for (auto t = 0U; t < threads; t++)
		tagOf[t].assign(code[t].size(), -1);
	auto place = [&](unsigned t, unsigned from) {
		/* Not between the read and the write of an RMW */
		const auto &c = code[t];
		std::vector<unsigned> places;
		for (auto p = from; p <= c.size(); p++)
			if (p == 0 || p == c.size() || !(c[p - 1].excl && c[p - 1].kind == Kind::R))
				places.push_back(p);
		return places[pick(places.size())];
	};
	auto insertAt = [&](unsigned t, unsigned at, Event ev, int tag) {
		code[t].insert(code[t].begin() + at, ev);
		tagOf[t].insert(tagOf[t].begin() + at, tag);
	};
	auto insert = [&](unsigned t, unsigned from, Event ev, int tag) -> unsigned {
		auto at = place(t, from);
		insertAt(t, at, ev, tag);
		return at;
	};

	/* Method calls: a begin and an end around some of a thread's code */
	auto calls = 0;
	if (a.methods) {
		for (auto t = 0U; t < threads; t++) {
			if (!coin(2))
				continue;
			auto begin = place(t, 0);
			auto end = place(t, begin);
			insertAt(t, end, {.thread = t, .kind = Kind::MethodEnd}, calls);
			insertAt(t, begin, {.thread = t, .kind = Kind::MethodBegin}, calls);
			calls++;
		}
	}

	/* Thread creation and join: a thread may create a later one, and join
	 * it after it created it; a joined thread ends with its finish */
	std::vector<bool> joined(threads, false);
	if (a.threadEvents) {
		for (auto t = 1U; t < threads; t++) {
			if (!coin(2))
				continue;
			auto parent = pick(t);
			auto at = insert(parent, 0,
					 {.thread = parent, .kind = Kind::TC, .order = Order::REL},
					 static_cast<int>(t));
			if (coin(2)) {
				insert(parent, at + 1,
				       {.thread = parent, .kind = Kind::TJ, .order = Order::ACQ},
				       static_cast<int>(t));
				joined[t] = true;
			}
		}
		for (auto t = 1U; t < threads; t++) {
			if (!joined[t])
				continue;
			code[t].push_back({.thread = t, .kind = Kind::TE, .order = Order::REL});
			tagOf[t].push_back(-1);
		}
	}

	/* Heap blocks: the locations frees, retires and protections are of,
	 * and others at random, allocated at the start of the first thread
	 * with an event of them (porf has to reach the others) */
	if (alloc != nullptr) {
		for (auto l = 0; std::cmp_less(l, b.locations); l++) {
			auto first = -1;
			auto needed = false;
			for (auto t = 0U; t < threads; t++) {
				for (const auto &ev : code[t]) {
					if (!ev.hasLocation() || ev.loc != l)
						continue;
					if (first < 0)
						first = static_cast<int>(t);
					needed |= ev.kind == Kind::Free ||
						  ev.kind == Kind::HpRetire ||
						  ev.kind == Kind::HpProtect;
				}
			}
			if (first < 0 || !(needed || coin(2)))
				continue;
			auto t = static_cast<unsigned>(first);
			insertAt(t, 0, eventsOf(*alloc, t, l).front(), -1);
		}
	}

	/* Flatten: threads in order, each but the first after a thread start */
	Execution x;
	std::vector<unsigned> startOf(threads);
	std::vector<unsigned> endOf(threads);
	std::vector<std::pair<unsigned, unsigned>> tagged; /* (event, tag) */
	for (auto t = 0U; t < threads; t++) {
		startOf[t] = x.size();
		if (t > 0)
			x.events.push_back(threadStart(t));
		for (auto i = 0U; i < code[t].size(); i++) {
			auto ev = code[t][i];
			ev.thread = t;
			if (tagOf[t][i] >= 0)
				tagged.emplace_back(x.size(), tagOf[t][i]);
			x.events.push_back(ev);
		}
		endOf[t] = x.size() - 1;
	}
	std::vector<unsigned> beginOf(calls);
	std::vector<unsigned> endOfCall(calls);
	for (const auto &[e, tag] : tagged) {
		switch (x.events[e].kind) {
		case Kind::TC:
			x.tc.emplace_back(e, startOf[tag]);
			break;
		case Kind::TJ:
			x.tj.emplace_back(endOf[tag], e);
			break;
		case Kind::MethodBegin:
			beginOf[tag] = e;
			break;
		default:
			endOfCall[tag] = e;
			break;
		}
	}
	/* lin: some calls of different threads end before others begin */
	for (auto c1 = 0; c1 < calls; c1++)
		for (auto c2 = 0; c2 < calls; c2++)
			if (x.events[beginOf[c1]].thread != x.events[beginOf[c2]].thread &&
			    !Execution::has(x.lin, endOfCall[c2], beginOf[c1]) && coin(3))
				x.lin.emplace_back(endOfCall[c1], beginOf[c2]);

	auto locs = 0;
	for (const auto &ev : x.events)
		locs = std::max(locs, ev.loc + 1);
	x.rf.assign(x.size(), -1);
	x.mo.assign(locs, {});
	for (auto e = 0U; e < x.size(); e++)
		if (x.events[e].kind == Kind::W)
			x.mo[x.events[e].loc].push_back(e);

	/* Dependencies on reads before an event */
	if (!a.deps.empty()) {
		for (auto e = 0U; e < x.size(); e++) {
			if (!hasDeps(x.events[e]))
				continue;
			const auto &ev = x.events[e];
			for (auto r = e; r-- > 0 && x.events[r].thread == ev.thread;)
				if (x.events[r].kind == Kind::R && coin(3))
					(x.*a.deps[pick(a.deps.size())]).emplace_back(r, e);
		}
	}
	return x;
}

auto randomAttempt(const Alphabet &a, const Bounds &b, bool cycles, std::mt19937 &rng) -> Execution
{
	auto x = randomShape(a, b, rng);
	for (auto r = 0U; r < x.size(); r++) {
		const auto &ev = x.events[r];
		if (ev.kind != Kind::R)
			continue;
		std::vector<int> sources{-1};
		for (auto w : x.mo[ev.loc])
			if (x.events[w].thread != ev.thread || w < r)
				sources.push_back(static_cast<int>(w));
		x.rf[r] = sources[pick(rng, sources.size())];
	}
	if (!randomMo(x, rng) || (!cycles && hasPorfCycle(x)) || !isHeapWellFormed(x))
		return {};
	canonicalizeLocations(x);
	return x;
}

/* An order of X's events that respects po, tc, tj and lin, at random */
auto randomInterleaving(const Execution &x, std::mt19937 &rng) -> std::vector<unsigned>
{
	auto n = x.size();
	std::vector<std::vector<unsigned>> succs(n);
	std::vector<unsigned> preds(n, 0);
	auto edge = [&](unsigned a, unsigned b) {
		succs[a].push_back(b);
		preds[b]++;
	};
	for (auto e = 1U; e < n; e++)
		if (x.events[e].thread == x.events[e - 1].thread)
			edge(e - 1, e);
	for (const auto *edges : {&x.tc, &x.tj, &x.lin})
		for (const auto &[a, b] : *edges)
			edge(a, b);
	std::vector<unsigned> ready;
	for (auto e = 0U; e < n; e++)
		if (preds[e] == 0)
			ready.push_back(e);
	std::vector<unsigned> order;
	while (!ready.empty()) {
		auto i = pick(rng, ready.size());
		auto e = ready[i];
		ready.erase(ready.begin() + i);
		order.push_back(e);
		for (auto s : succs[e])
			if (--preds[s] == 0)
				ready.push_back(s);
	}
	return order;
}

/* Adds X's events in a random interleaving, each read reading, and each
 * write going in co, where ACCEPT allows it on the events added so far */
auto builtAttempt(const Alphabet &a, const Bounds &b, std::mt19937 &rng,
		  const std::function<bool(const Execution &)> &accept) -> Execution
{
	auto shape = a;
	shape.methods = false;
	auto x = randomShape(shape, b, rng);
	for (auto &order : x.mo)
		order.clear();
	std::vector<bool> present(x.size(), false);
	auto acceptable = [&]() { return accept(restrictTo(x, present)); };

	for (auto e : randomInterleaving(x, rng)) {
		present[e] = true;
		const auto &ev = x.events[e];
		if (ev.kind == Kind::R) {
			std::vector<int> sources{-1};
			for (auto w : x.mo[ev.loc])
				sources.push_back(static_cast<int>(w));
			std::vector<int> ok;
			for (auto src : sources) {
				x.rf[e] = src;
				if (acceptable())
					ok.push_back(src);
			}
			if (ok.empty())
				return {};
			x.rf[e] = ok[pick(rng, ok.size())];
		} else if (ev.kind == Kind::W) {
			auto &order = x.mo[ev.loc];
			auto before = order;
			std::vector<unsigned> ok;
			for (auto at = 0U; at <= before.size(); at++) {
				order = before;
				order.insert(order.begin() + at, e);
				if (isAtomic(restrictTo(x, present)) && acceptable())
					ok.push_back(at);
			}
			if (ok.empty())
				return {};
			order = before;
			order.insert(order.begin() + ok[pick(rng, ok.size())], e);
		}
	}
	if (!isHeapWellFormed(x))
		return {};
	canonicalizeLocations(x);
	return x;
}

} // namespace

auto randomExecution(const Alphabet &alphabet, const Bounds &bounds, bool cycles, std::mt19937 &rng)
	-> Execution
{
	for (;;) {
		auto x = randomAttempt(alphabet, bounds, cycles, rng);
		if (x.size() > 0)
			return x;
	}
}

auto randomBuiltExecution(const Alphabet &alphabet, const Bounds &bounds, std::mt19937 &rng,
			  const std::function<bool(const Execution &)> &accept) -> Execution
{
	for (;;) {
		auto x = builtAttempt(alphabet, bounds, rng, accept);
		if (x.size() > 0)
			return x;
	}
}

} // namespace oracle
