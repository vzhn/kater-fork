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

#ifndef KATER_ORACLE_ENUMERATE_HPP
#define KATER_ORACLE_ENUMERATE_HPP

#include "Execution.hpp"

#include <functional>
#include <random>
#include <vector>

namespace oracle {

/*
 * The events a graph is made of: the instructions of a thread, each one or
 * two events (an RMW is a read and a write), with the orderings a model
 * tells apart. Every thread but the first starts with a thread start, as in
 * GenMC, where the first thread starts with the initial writes.
 */
struct Alphabet {
	struct Instruction {
		/* R, W or F, an RMW being an R with `rmw`; Alloc, Free,
		 * HpRetire, HpProtect; or another kind, of no location */
		Kind kind;
		Order order;
		bool rmw = false;
		Flavor flavor = Flavor::Plain;
		unsigned fence = 0;
		unsigned hp = 0;
	};
	/* Random graphs give a location an allocation (of an Alloc
	 * instruction) before its first event, rather than placing one */
	std::vector<Instruction> instructions;

	/* The dependency relations an event may have on an earlier read of its thread */
	std::vector<Execution::Edges Execution::*> deps;

	/* Random graphs may create and join threads, and have method calls
	 * with lin between them (Relinche's) */
	bool threadEvents = false;
	bool methods = false;
};

struct Bounds {
	unsigned events = 4; /* the events of instructions (thread starts aside) */
	unsigned threads = 3;
	unsigned locations = 2;
};

/*
 * Calls VISIT on every graph over ALPHABET within BOUNDS whose rf, co and
 * fr respect po, whose RMWs are atomic and that has no porf cycle (with
 * CYCLES, also those with one), each once up to renaming locations. Deps
 * come from the read right before an event. Stops early if VISIT returns
 * false; returns whether it ran to the end.
 */
auto enumerate(const Alphabet &alphabet, const Bounds &bounds, bool cycles,
	       const std::function<bool(const Execution &)> &visit) -> bool;

/* A random graph of the same kind, with up to BOUNDS.events events */
auto randomExecution(const Alphabet &alphabet, const Bounds &bounds, bool cycles, std::mt19937 &rng)
	-> Execution;

/*
 * A random graph built as GenMC builds one, without revisits: its events
 * added in a random order that respects po and thread events, each read
 * reading from a write already there, and each write going in co, where
 * ACCEPT (coherence, say) allows it on the events added so far
 */
auto randomBuiltExecution(const Alphabet &alphabet, const Bounds &bounds, std::mt19937 &rng,
			  const std::function<bool(const Execution &)> &accept) -> Execution;

/* Whether X's RMWs are atomic: each RMW's write is right after its read's write in co */
auto isAtomic(const Execution &x) -> bool;

/* Whether X's heap is as GenMC's: a block has one allocation, which precedes
 * the events of the block in po | rf | tc | tj, and frees, retires and
 * protections are of blocks */
auto isHeapWellFormed(const Execution &x) -> bool;

/* Whether GRAPH's rf, co and fr respect po and its RMWs are atomic, as those
 * of the graphs enumerate() makes do */
auto respectsPo(const Execution &graph) -> bool;

/* Whether po | rf | tc | tj | lin has a cycle in X */
auto hasPorfCycle(const Execution &x) -> bool;

/* X with only the events KEEP says (whose rf sources it keeps), threads as they are */
auto restrictTo(const Execution &x, const std::vector<bool> &keep) -> Execution;

/* X without event E, which nothing reads from and no thread event depends on */
auto withoutEvent(const Execution &x, unsigned e) -> Execution;

/* Numbers X's locations by first use */
void canonicalizeLocations(Execution &x);

} // namespace oracle

#endif /* KATER_ORACLE_ENUMERATE_HPP */
