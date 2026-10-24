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

#include "Execution.hpp"

#include <algorithm>
#include <array>
#include <istream>
#include <ostream>
#include <sstream>

namespace oracle {

namespace {

constexpr std::array<const char *, numKinds> kindNames = {
	"R",	 "W",	 "F",	  "TC",	       "TB",	       "TJ",	     "TE",   "TK",
	"ALLOC", "FREE", "HPRET", "HPPROTECT", "METHOD-BEGIN", "METHOD-END", "OTHER"};

constexpr std::array<const char *, numOrders> orderNames = {"na",  "rlx",     "acq",
							    "rel", "acq_rel", "sc"};

constexpr std::array<const char *, numFlavors> flavorNames = {
	"plain",     "noret",	    "mb",	  "lock",      "unlock",
	"srcu-lock", "srcu-unlock", "failed-cas", "lkmm-fence"};

/* GenMC's names (std::formatter<LkmmFenceKind>) */
constexpr std::array<const char *, numLkmmFences> lkmmFenceNames = {
	"mb",  "rmb",	   "wmb",	 "ba",	     "aa",   "as",
	"aul", "rcu-lock", "rcu-unlock", "sync-rcu", "asru", "sync-srcu"};

auto eventName(unsigned e) -> std::string { return "e" + std::to_string(e); }

template <typename Names> auto indexOf(const Names &names, const std::string &s) -> int
{
	auto it = std::ranges::find(names, s);
	return it == names.end() ? -1 : static_cast<int>(it - names.begin());
}

auto parseLocation(const std::string &s) -> int
{
	if (s.empty() || s[0] < 'x' || s[0] > 'z')
		return -1;
	auto base = s[0] - 'x';
	if (s.size() == 1)
		return base;
	try {
		return base + (3 * std::stoi(s.substr(1)));
	} catch (...) {
		return -1;
	}
}

auto parseEvent(const std::string &s) -> int
{
	if (s.size() < 2 || s[0] != 'e')
		return -1;
	try {
		return std::stoi(s.substr(1));
	} catch (...) {
		return -1;
	}
}

} // namespace

auto kindName(Kind k) -> const char * { return kindNames[static_cast<unsigned>(k)]; }
auto orderName(Order o) -> const char * { return orderNames[static_cast<unsigned>(o)]; }
auto flavorName(Flavor f) -> const char * { return flavorNames[static_cast<unsigned>(f)]; }
auto lkmmFenceName(unsigned kind) -> const char * { return lkmmFenceNames.at(kind); }

auto locationName(int l) -> std::string
{
	return std::string(1, static_cast<char>('x' + (l % 3))) +
	       (l >= 3 ? std::to_string(l / 3) : "");
}

auto Execution::moBefore(unsigned a, unsigned b) const -> bool
{
	const auto &ev = events[a];
	if (ev.kind != Kind::W || events[b].kind != Kind::W || ev.loc != events[b].loc)
		return false;
	const auto &order = mo[ev.loc];
	auto ia = std::ranges::find(order, a);
	auto ib = std::ranges::find(order, b);
	return ia < ib && ib != order.end();
}

auto Execution::has(const Edges &edges, unsigned a, unsigned b) -> bool
{
	return std::ranges::find(edges, std::make_pair(a, b)) != edges.end();
}

auto Execution::additionOrder(std::optional<unsigned> last) const -> Addition
{
	auto n = size();
	std::vector<std::vector<unsigned>> succs(n);
	std::vector<unsigned> preds(n, 0);
	auto edge = [&](unsigned a, unsigned b) {
		succs[a].push_back(b);
		preds[b]++;
	};
	for (auto e = 1U; e < n; e++)
		if (events[e].thread == events[e - 1].thread)
			edge(e - 1, e);
	for (auto r = 0U; r < n; r++)
		if (rf[r] >= 0)
			edge(static_cast<unsigned>(rf[r]), r);
	for (const auto *edges : {&tc, &tj, &lin})
		for (const auto &[a, b] : *edges)
			edge(a, b);

	Addition order{.events = {}, .causal = true};
	std::vector<bool> done(n, false);
	while (order.events.size() < n) {
		auto next = std::optional<unsigned>();
		for (auto e = 0U; e < n && !next; e++)
			if (!done[e] && preds[e] == 0 &&
			    (e != last || order.events.size() + 1 == n))
				next = e;
		if (!next) {
			order.events.clear();
			for (auto e = 0U; e < n; e++)
				if (e != last)
					order.events.push_back(e);
			if (last)
				order.events.push_back(*last);
			order.causal = false;
			return order;
		}
		done[*next] = true;
		order.events.push_back(*next);
		for (auto s : succs[*next])
			preds[s]--;
	}
	return order;
}

void Execution::print(std::ostream &os, const std::string &indent) const
{
	for (auto e = 0U; e < size(); e++) {
		const auto &ev = events[e];
		os << indent << eventName(e) << ": T" << ev.thread << " " << kindName(ev.kind);
		if (ev.isAccess())
			os << "(" << locationName(ev.loc) << ")";
		os << " " << orderName(ev.order);
		if (ev.excl)
			os << " excl";
		if (ev.flavor != Flavor::Plain)
			os << " " << flavorName(ev.flavor);
		if (ev.flavor == Flavor::LkmmFence)
			os << ":" << lkmmFenceName(ev.fence);
		os << "\n";
	}

	std::string rfs;
	for (auto r = 0U; r < size(); r++)
		if (rf[r] >= 0)
			rfs += " " + eventName(rf[r]) + "->" + eventName(r);
	if (!rfs.empty())
		os << indent << "rf:" << rfs << "\n";
	for (auto l = 0U; l < numLocations(); l++) {
		if (mo[l].empty())
			continue;
		os << indent << "mo(" << locationName(static_cast<int>(l)) << "):";
		for (auto w : mo[l])
			os << " " << eventName(w);
		os << "\n";
	}
	auto printEdges = [&](const char *name, const Edges &edges) {
		if (edges.empty())
			return;
		os << indent << name << ":";
		for (const auto &[a, b] : edges)
			os << " " << eventName(a) << "->" << eventName(b);
		os << "\n";
	};
	printEdges("ctrl", ctrl);
	printEdges("addr", addr);
	printEdges("data", data);
	printEdges("pctrl", pctrl);
	printEdges("tc", tc);
	printEdges("tj", tj);
	printEdges("lin", lin);
}

auto operator<<(std::ostream &os, const Execution &x) -> std::ostream &
{
	x.print(os);
	return os;
}

// NOLINTNEXTLINE(readability-function-cognitive-complexity): one case per line form
auto Execution::parse(std::istream &is, std::string &error) -> std::optional<Execution>
{
	Execution x;
	std::string line;
	auto lineNo = 0U;
	auto fail = [&](const std::string &why) -> std::optional<Execution> {
		error = "line " + std::to_string(lineNo) + ": " + why;
		return std::nullopt;
	};

	std::vector<std::pair<unsigned, unsigned>> rfs;
	std::vector<std::pair<int, std::vector<unsigned>>> mos;
	while (std::getline(is, line)) {
		lineNo++;
		std::istringstream ls(line);
		std::string head;
		if (!(ls >> head) || head[0] == '#')
			continue;

		/* An event: eN: Tt KIND[(loc)] order [excl] [flavor[:fence]] */
		if (head.back() == ':' && parseEvent(head.substr(0, head.size() - 1)) >= 0) {
			if (parseEvent(head.substr(0, head.size() - 1)) !=
			    static_cast<int>(x.size()))
				return fail("events must be numbered in order");
			Event ev;
			std::string thread;
			std::string kind;
			std::string order;
			if (!(ls >> thread >> kind >> order) || thread.size() < 2 ||
			    thread[0] != 'T')
				return fail("expected: eN: Tt KIND order");
			ev.thread = static_cast<unsigned>(std::stoul(thread.substr(1)));
			if (auto paren = kind.find('('); paren != std::string::npos) {
				if (kind.back() != ')')
					return fail("bad location in " + kind);
				ev.loc = parseLocation(
					kind.substr(paren + 1, kind.size() - paren - 2));
				kind = kind.substr(0, paren);
				if (ev.loc < 0)
					return fail("bad location in " + kind);
			}
			auto k = indexOf(kindNames, kind);
			auto o = indexOf(orderNames, order);
			if (k < 0 || o < 0)
				return fail("unknown kind or ordering");
			ev.kind = static_cast<Kind>(k);
			ev.order = static_cast<Order>(o);
			if (ev.isAccess() != (ev.loc >= 0))
				return fail("reads and writes, and only they, have a location");
			std::string word;
			while (ls >> word) {
				if (word == "excl") {
					ev.excl = true;
					continue;
				}
				auto colon = word.find(':');
				auto f = indexOf(flavorNames, word.substr(0, colon));
				if (f < 0)
					return fail("unknown flavor " + word);
				ev.flavor = static_cast<Flavor>(f);
				if (ev.flavor == Flavor::LkmmFence) {
					if (colon == std::string::npos)
						return fail("an lkmm-fence needs a kind");
					auto fk = indexOf(lkmmFenceNames, word.substr(colon + 1));
					if (fk < 0)
						return fail("unknown LKMM fence " + word);
					ev.fence = static_cast<unsigned>(fk);
				}
			}
			if (!x.events.empty() && ev.thread != x.events.back().thread &&
			    ev.thread != x.events.back().thread + 1)
				return fail("threads must be numbered in order");
			x.events.push_back(ev);
			continue;
		}

		/* mo(loc): eA eB ... */
		if (head.starts_with("mo(") && head.ends_with("):")) {
			auto l = parseLocation(head.substr(3, head.size() - 5));
			if (l < 0)
				return fail("bad location in " + head);
			std::vector<unsigned> order;
			std::string w;
			while (ls >> w) {
				auto e = parseEvent(w);
				if (e < 0)
					return fail("bad event " + w);
				order.push_back(static_cast<unsigned>(e));
			}
			mos.emplace_back(l, std::move(order));
			continue;
		}

		/* name: eA->eB ... */
		auto *edges = head == "ctrl:"	 ? &x.ctrl
			      : head == "addr:"	 ? &x.addr
			      : head == "data:"	 ? &x.data
			      : head == "pctrl:" ? &x.pctrl
			      : head == "tc:"	 ? &x.tc
			      : head == "tj:"	 ? &x.tj
			      : head == "lin:"	 ? &x.lin
			      : head == "rf:"	 ? &rfs
						 : nullptr;
		if (edges == nullptr)
			return fail("unknown line " + head);
		std::string edge;
		while (ls >> edge) {
			auto arrow = edge.find("->");
			auto a = arrow == std::string::npos ? -1
							    : parseEvent(edge.substr(0, arrow));
			auto b = arrow == std::string::npos ? -1
							    : parseEvent(edge.substr(arrow + 2));
			if (a < 0 || b < 0)
				return fail("bad edge " + edge);
			edges->emplace_back(a, b);
		}
	}

	auto n = x.size();
	auto locs = 0;
	for (const auto &ev : x.events)
		locs = std::max(locs, ev.loc + 1);
	x.rf.assign(n, -1);
	x.mo.assign(locs, {});
	for (const auto &[w, r] : rfs) {
		if (w >= n || r >= n)
			return fail("rf out of range");
		x.rf[r] = static_cast<int>(w);
	}
	for (auto &[l, order] : mos) {
		if (l >= locs || std::ranges::any_of(order, [&](auto w) { return w >= n; }))
			return fail("mo out of range");
		x.mo[l] = std::move(order);
	}
	for (const auto *edges : {&x.ctrl, &x.addr, &x.data, &x.pctrl, &x.tc, &x.tj, &x.lin})
		if (std::ranges::any_of(*edges,
					[&](auto &e) { return e.first >= n || e.second >= n; }))
			return fail("edge out of range");
	return x;
}

} // namespace oracle
