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

#ifndef KATER_ORACLE_EXECUTION_HPP
#define KATER_ORACLE_EXECUTION_HPP

#include <cstdint>
#include <iosfwd>
#include <optional>
#include <string>
#include <utility>
#include <vector>

namespace oracle {

/* The kinds of GenMC event labels the model tells apart */
enum class Kind : std::uint8_t {
	R,
	W,
	F,
	TC, /* ThreadCreate */
	TB, /* ThreadStart */
	TJ, /* ThreadJoin */
	TE, /* ThreadFinish */
	TK, /* ThreadKill */
	Alloc,
	Free,
	HpRetire,
	HpProtect,
	MethodBegin,
	MethodEnd,
	Other, /* every other label: optionals, loop and spin markers, outputs, ... */
};
inline constexpr unsigned numKinds = 15;

/* GenMC's memory orderings (consume is never generated) */
enum class Order : std::uint8_t { NA, RLX, ACQ, REL, ACQ_REL, SC };
inline constexpr unsigned numOrders = 6;

auto kindName(Kind k) -> const char *;
auto orderName(Order o) -> const char *;

/*
 * The class of an event's GenMC label beyond its kind and ordering, for the
 * models whose predicates tell the classes apart (LKMM's)
 */
enum class Flavor : std::uint8_t {
	Plain,	    /* ReadLabel, WriteLabel, FenceLabel; FaiRead and FaiWrite in an RMW */
	NoRet,	    /* an RMW that returns no value: NoRetFaiRead, NoRetFaiWrite */
	Mb,	    /* a fully ordered RMW: FaiRead, FaiWrite with the LkmmMb attribute */
	Lock,	    /* spin_lock(): LockCasRead, LockCasWrite */
	Unlock,	    /* spin_unlock(): UnlockWrite */
	SrcuLock,   /* srcu_read_lock(): SrcuLockRead */
	SrcuUnlock, /* srcu_read_unlock(): SrcuUnlockWrite */
	FailedCas,  /* a compare-and-swap that failed: a CasRead with no write */
	LkmmFence,  /* an LkmmFenceLabel, of the kind in `fence` */
};
inline constexpr unsigned numFlavors = 9;

/* The kinds of LkmmFenceLabel, in GenMC's order (LkmmFenceKind) */
inline constexpr unsigned numLkmmFences = 12;

auto flavorName(Flavor f) -> const char *;
auto lkmmFenceName(unsigned kind) -> const char *;

/*
 * A concrete execution graph: what Graph leaves to the solver, fixed.
 * Events are numbered thread by thread, in program order, and initial
 * writes are implicit, as in Graph.
 *
 * A location an allocation is of is a heap block (one location wide), the
 * others are static. Frees, retires and hazard-pointer protections are of a
 * block, which its allocation precedes in porf.
 */
struct Execution {
	struct Event {
		unsigned thread = 0;
		Kind kind = Kind::Other;
		Order order = Order::NA;
		/* The location of an access, or the block an allocation, free,
		 * retire or protection is of; numbered by first use */
		int loc = -1;
		bool excl = false;
		Flavor flavor = Flavor::Plain;
		unsigned fence = 0; /* the kind of an LkmmFence */
		unsigned hp = 0;    /* the hazard pointer an HpProtect protects through */

		[[nodiscard]] auto isAccess() const -> bool
		{
			return kind == Kind::R || kind == Kind::W;
		}
		/* Whether the event has a location: GenMC's LOC */
		[[nodiscard]] auto hasLocation() const -> bool
		{
			return isAccess() || kind == Kind::Alloc || kind == Kind::Free ||
			       kind == Kind::HpRetire || kind == Kind::HpProtect;
		}
		/* Whether the error checks look at the event (GenMCDriver::checkForRaces) */
		[[nodiscard]] auto isChecked() const -> bool
		{
			return isAccess() || kind == Kind::Free || kind == Kind::HpRetire;
		}
	};
	using Edges = std::vector<std::pair<unsigned, unsigned>>;

	std::vector<Event> events;

	/* The write each read reads from; -1 for the initial value (and non-reads) */
	std::vector<int> rf;

	/* The writes to each location, in coherence order */
	std::vector<std::vector<unsigned>> mo;

	Edges ctrl, addr, data, pctrl, tc, tj, lin;

	[[nodiscard]] auto size() const -> unsigned { return static_cast<unsigned>(events.size()); }
	[[nodiscard]] auto numThreads() const -> unsigned
	{
		return events.empty() ? 0 : events.back().thread + 1;
	}
	[[nodiscard]] auto numLocations() const -> unsigned
	{
		return static_cast<unsigned>(mo.size());
	}

	/* Whether write A is before write B in coherence */
	[[nodiscard]] auto moBefore(unsigned a, unsigned b) const -> bool;

	/* Whether (A, B) is an edge of EDGES */
	[[nodiscard]] static auto has(const Edges &edges, unsigned a, unsigned b) -> bool;

	/* The allocation of location L, if L is a heap block */
	[[nodiscard]] auto allocationOf(int l) const -> std::optional<unsigned>;

	/*
	 * The order kater-oracle-runner adds the events to a GenMC graph in,
	 * with LAST, if given, last: each event after its po, rf, tc, tj and
	 * lin predecessors, the lowest-numbered first, if there is such an
	 * order (CAUSAL); otherwise (a porf cycle) by number
	 */
	struct Addition {
		std::vector<unsigned> events;
		bool causal;
	};
	[[nodiscard]] auto additionOrder(std::optional<unsigned> last) const -> Addition;

	/* Renders the graph in the form parse() reads */
	void print(std::ostream &os, const std::string &indent = "") const;

	/* Reads a graph that print() rendered; on a malformed one, explains in ERROR */
	static auto parse(std::istream &is, std::string &error) -> std::optional<Execution>;
};

auto operator<<(std::ostream &os, const Execution &x) -> std::ostream &;

/* The name of location L: x, y, z, x1, ... */
auto locationName(int l) -> std::string;

} // namespace oracle

#endif /* KATER_ORACLE_EXECUTION_HPP */
