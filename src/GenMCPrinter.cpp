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

#include "GenMCPrinter.hpp"

#include <iostream>
#include <algorithm>

#include "Config.hpp"
#include "KatModule.hpp"
#include "Logger.hpp"
#include "NFAUtils.hpp"
#include "RegExp.hpp"
#include "RegExpUtils.hpp"
#include "Utils.hpp"

#include <fstream>
#include <functional>
#include <sstream>

using namespace std::literals;

namespace {

const char *genmcCopyright =
	R"(/*
 * GenMC -- Generic Model Checking.
 *
 * This project is dual-licensed under the Apache License 2.0 and the MIT License.
 * You may choose to use, distribute, or modify this software under either license.
 *
 * Apache License 2.0:
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * MIT License:
 *     https://opensource.org/licenses/MIT
 */
)";

const char *katerNotice =
	R"(/*******************************************************************************
 * CAUTION: This file is generated automatically by Kater -- DO NOT EDIT.
 *******************************************************************************/
)";

const char *coherenceFuns =
	R"(
static auto isWriteRfBefore(const WriteLabel *wLab, const EventLabel *lab) -> bool
{
	auto &before = lab->view(#HB#);
	return before.contains(wLab->getPos()) ||
	       std::ranges::any_of(wLab->readers(),
				   [&](auto &rLab) { return before.contains(rLab.getPos()); });
}

static auto isHbOptRfBefore(const EventLabel *lab, const WriteLabel *wLab) -> bool
{
	return wLab->view(#HB#).contains(lab->getPos()) ||
	       std::ranges::any_of(wLab->readers(), [&](auto &rLab) {
		       return rLab.view(#HB#).contains(lab->getPos());
	       });
}

static auto splitLocMOBefore(SAddr addr, EventLabel *lab) -> ExecutionGraph::co_iterator
{
	auto &g = *lab->getParent();
	auto rit = std::ranges::find_if(g.rco(addr), [&](auto &oLab)
					{ return isWriteRfBefore(&oLab, lab); });
	/* Convert to forward iterator, but be _really_ careful */
	return (rit == std::ranges::end(g.rco(addr))) ? std::ranges::begin(g.co(addr)) : ++ExecutionGraph::co_iterator(*rit);
}

static auto splitLocMOAfterHb(ReadLabel *rLab) -> ExecutionGraph::co_iterator
{
	auto &g = *rLab->getParent();
	if (std::ranges::any_of(g.getInitLabel()->rfs(rLab->getAddr()),
			[rLab](auto &rfLab) { return rfLab.view(#HB#).contains(rLab->getPos()); }))
		return std::ranges::begin(g.co(rLab->getAddr()));

	auto it = std::ranges::find_if(g.co(rLab->getAddr()),
			       [&](auto &wLab) { return isHbOptRfBefore(rLab, &wLab); });
	if (it == std::ranges::end(g.co(rLab->getAddr())) || it->view(#HB#).contains(rLab->getPos()))
		return it;
	return ++it;
}

static auto splitLocMOAfter(WriteLabel *wLab) -> ExecutionGraph::co_iterator
{
	auto &g = *wLab->getParent();
	return std::ranges::find_if(g.co(wLab->getAddr()),
			    [&](auto &sLab) { return isHbOptRfBefore(wLab, &sLab); });
}

/* Whether END is reachable from BEGIN in ADDR's coherence order. It is not
 * when coherence contradicts hb, which a consistent graph never does, but an
 * event added before events kept further on in its thread can see before
 * the graph is checked again, typically because of a kept event the new path
 * skips (it goes once the thread passes its place): then every position is a
 * candidate, and GenMC's later checks drop the inconsistent ones */
static auto isCoRange(ExecutionGraph &g, SAddr addr, ExecutionGraph::co_iterator begin,
		      ExecutionGraph::co_iterator end) -> bool
{
	for (auto it = begin; it != end; ++it)
		if (it == std::ranges::end(g.co(addr)))
			return false;
	return true;
}

auto #CLASS#::getCoherentStores(ReadLabel *rLab) -> std::vector<EventLabel *>
{
	auto &g = *rLab->getParent();
	std::vector<EventLabel *> stores;

	/* Fastpath: co_max(G) is po-before R */
	auto *comaxLab = g.co_max(rLab->getAddr());
	if (comaxLab->getThread() == rLab->getThread() && comaxLab->getIndex() < rLab->getIndex())
		return {comaxLab};

	/*
	 * If there are no stores (rf?;hb)-before the current event
	 * then we can read read from all concurrent stores and the
	 * initializer store. Otherwise, we can read from all concurrent
	 * stores and the mo-latest of the (rf?;hb)-before stores.
	 */
	auto begIt = splitLocMOBefore(rLab->getAddr(), rLab);
	if (begIt == std::ranges::begin(g.co(rLab->getAddr())))
		stores.push_back(g.getInitLabel());
	else {
		stores.push_back(&*(--begIt));
		++begIt;
	}

	/*
	 * If the model supports out-of-order execution we have to also
	 * account for the possibility the read is hb-before some other
	 * store, or some read that reads from a store.
	 */
	auto endIt = (isDepTracking()) ? splitLocMOAfterHb(rLab) : std::ranges::end(g.co(rLab->getAddr()));
	if (!isCoRange(g, rLab->getAddr(), begIt, endIt)) {
		stores.clear();
		stores.push_back(g.getInitLabel());
		begIt = std::ranges::begin(g.co(rLab->getAddr()));
		endIt = std::ranges::end(g.co(rLab->getAddr()));
	}
	std::transform(begIt, endIt, std::back_inserter(stores), [&](auto &lab){
		return &lab;
	});
	return stores;
}

static auto getMOOptRfAfter(WriteLabel *sLab) -> std::vector<EventLabel *>
{
	auto &g = *sLab->getParent();
	std::vector<EventLabel *> after;
	std::vector<ReadLabel *> rfAfter;

	for (auto &wLab : g.co_succs(sLab)) {
		after.push_back(&wLab);
		std::ranges::transform(wLab.readers(), std::back_inserter(rfAfter),
			[&](auto &rLab) { return &rLab; });
	}
	std::transform(rfAfter.begin(), rfAfter.end(), std::back_inserter(after),
		       [](auto *rLab) { return rLab; });
	return after;
}

static auto getMOInvOptRfAfter(WriteLabel *sLab) -> std::vector<EventLabel *>
{
	auto &g = *sLab->getParent();
	std::vector<EventLabel *> after;
	std::vector<ReadLabel *> rfAfter;

	/* First, add (mo;rf?)-before */
	for (auto &wLab : g.co_preds(sLab)) {
		after.push_back(&wLab);
		std::ranges::transform(wLab.readers(), std::back_inserter(rfAfter),
			[&](auto &rLab) { return &rLab; });
	}
	std::transform(rfAfter.begin(), rfAfter.end(), std::back_inserter(after),
		       [](auto *rLab) { return rLab; });

	/* Then, we add the reader list for the initializer */
	for (auto &rLab : g.getInitLabel()->rfs(sLab->getAddr()))
		after.insert(after.end(), &rLab);
	return after;
}

[[maybe_unused]] static auto getRevisitableFrom(WriteLabel *sLab, const VectorClock &pporf,
						WriteLabel *coPred) -> std::vector<ReadLabel *>
{
	const auto *confLab = findPendingRMW(sLab);
	std::vector<ReadLabel *> loads;

	for (auto &rLab : coPred->readers()) {
		if (!pporf.contains(rLab.getPos()) && rLab.getAddr() == sLab->getAddr() &&
		    rLab.isRevisitable() && rLab.wasAddedMax())
			loads.push_back(&rLab);
	}
	if (confLab)
		loads.erase(std::remove_if(loads.begin(), loads.end(),
					   [&](auto &eLab) {
						   return eLab->getStamp() > confLab->getStamp();
					   }),
			    loads.end());
	return loads;
}

void #CLASS#::filterCoherentRevisits(WriteLabel *sLab, std::vector<ReadLabel *> &ls)
{
	/* If this store is po- and mo-maximal then we are done */
	auto &g = *sLab->getParent();
	if (!isDepTracking() && sLab == g.co_max(sLab->getAddr()))
		return;

	/* First, we have to exclude (mo;rf?;hb?;sb)-after reads */
	auto optRfs = getMOOptRfAfter(sLab);
	ls.erase(std::remove_if(ls.begin(), ls.end(),
				[&](auto &eLab) {
					auto &before = g.po_imm_pred(eLab)->view(#HB#); // hb;sb
					return std::any_of(
						optRfs.begin(), optRfs.end(), [&](auto &evLab) {
							return before.contains(evLab->getPos());
						});
				}),
		 ls.end());

	/* If out-of-order event addition is not supported, then we are done
	 * due to po-maximality */
	if (!isDepTracking())
		return;

	/* Otherwise, we also have to exclude hb-before loads */
	ls.erase(std::remove_if(ls.begin(), ls.end(),
				[&](auto &eLab) { return sLab->view(#HB#).contains(eLab->getPos()); }),
		 ls.end());

	/* ...and also exclude (mo^-1; rf?; (hb^-1)?; sb^-1)-after reads in the *resulting* graph.
	 * An RMW read's own write part, and the reads of it, are no such events:
	 * revisited, the read reads SLAB, and its write moves right after SLAB
	 * in coherence (a write part kept while its read was deleted and
	 * executed anew, see updateKeptRMWWrite()) */
	auto &before = sLab->getPrefixView();
	auto moInvOptRfs = getMOInvOptRfAfter(sLab);
	ls.erase(std::remove_if(
			 ls.begin(), ls.end(),
			 [&](auto &eLab) {
				 auto v = g.getViewFromStamp(eLab->getStamp());
				 v->update(before);
				 const auto *own = eLab->isRMW() ? g.po_imm_succ(eLab) : nullptr;
				 auto isOwn = [&](const EventLabel *evLab) {
					 const auto *rLab = genmc::dyn_cast<ReadLabel>(evLab);
					 return own && (evLab == own || (rLab && rLab->getRf() == own));
				 };
				 return std::any_of(
					 moInvOptRfs.begin(), moInvOptRfs.end(), [&](auto &evLab) {
						 return !isOwn(evLab) &&
							v->contains(evLab->getPos()) && // stays in graph?
							g.po_imm_pred(evLab)->view(#HB#).contains(eLab->getPos()); // po-pred to check evLab != rLab
					 });
			 }),
		 ls.end());
}

auto #CLASS#::getCoherentPlacings(WriteLabel *wLab)
	-> std::vector<EventLabel *>
{
	auto &g = *wLab->getParent();
	std::vector<EventLabel *> result;

	/* If it is an RMW store, there is only one possible position in MO */
	if (wLab->isRMW()) {
		auto *rLab = genmc::dyn_cast<ReadLabel>(g.po_imm_pred(wLab));
		VERIFY(rLab);
		auto *rfLab = rLab->getRf();
		VERIFY(rfLab);
		result.push_back(rfLab);
		return result;
	}

	/* Otherwise, we calculate the full range and add the store */
	auto rangeBegin = splitLocMOBefore(wLab->getAddr(), wLab);
	auto rangeEnd = (isDepTracking()) ? splitLocMOAfter(wLab) : std::ranges::end(g.co(wLab->getAddr()));
	if (!isCoRange(g, wLab->getAddr(), rangeBegin, rangeEnd)) {
		rangeBegin = std::ranges::begin(g.co(wLab->getAddr()));
		rangeEnd = std::ranges::end(g.co(wLab->getAddr()));
	}
	auto cos = std::ranges::subrange(rangeBegin, rangeEnd) |
		   std::views::filter([&](auto &sLab) { return !sLab.isRMW(); }) |
		   std::views::transform([&](auto &sLab) {
			   auto *pLab = g.co_imm_pred(&sLab);
			   return pLab ? (EventLabel *)pLab : (EventLabel *)g.getInitLabel();
		   });
	std::ranges::copy(cos, std::back_inserter(result));
	/* The range's end bounds it from above (dependency-tracking models: the
	 * first write a later access of the thread wrote or read). If it is an
	 * RMW's write, the placing right before it comes between that write and
	 * the write its read reads, as the ones the filter drops do */
	if (rangeEnd == std::ranges::end(g.co(wLab->getAddr())))
		result.push_back(g.co_max(wLab->getAddr()));
	else if (!rangeEnd->isRMW())
		result.push_back(!g.co_imm_pred(&*rangeEnd)
					 ? (EventLabel *)g.getInitLabel()
					 : (EventLabel *)g.co_imm_pred(&*rangeEnd));
	return result;
})";

const char *commonHeaderDeclarations =
	R"(#ifndef #GUARDNAME#
#define #GUARDNAME#

#include "genmc/Models/ConsistencyChecker.hpp"
#include "genmc/Execution/EventLabel.hpp"
#include <algorithm>
#include <cstdint>
#include <vector>
#include <concepts>

// NOLINTBEGIN
class #CLASS# : public ConsistencyChecker {

private:
	enum class NodeStatus : uint32_t { unseen = 0, entered = 1, left = 2 };

	struct DFSWorklistEntry {
		DFSWorklistEntry() = default;
		DFSWorklistEntry(uint32_t state, const EventLabel *lab, bool finishing = false)
			: nfaState(state), lab(lab), isFinishing(finishing)
		{}
		uint32_t nfaState;
		const EventLabel *lab;
		bool isFinishing;
	};

	template <std::unsigned_integral T>
	class NodeStatusVector {
	public:
		NodeStatusVector() = default;
		NodeStatusVector(size_t size)
			: visited(size), baseStatus(0)
		{}

		[[nodiscard]] auto getStatus(size_t i) const -> NodeStatus
		{
			auto status = visited[i];
			if (status < baseStatus)
				return NodeStatus::unseen;
			return static_cast<NodeStatus>(status - baseStatus);
		}

		void setStatus(size_t i, NodeStatus s) { visited[i] = baseStatus + static_cast<T>(s); }

		void maybeClearResize(size_t newSize)
		{
			if (baseStatus >= std::numeric_limits<T>::max() - 6) {
				visited.clear();
				baseStatus = 0;
			} else {
				baseStatus += 3;
			}
			visited.resize(newSize);
		}

	private:
		mutable std::vector<T> visited;
		T baseStatus{};
	};

	/* Tarjan's algorithm, for the acyclicity checks: each node keeps its
	 * index, the least index it reaches (its lowlink), the number of
	 * starting nodes on the stack up to it, and the node it was reached
	 * from. A node is `entered` while it is on the stack, and `left` once
	 * its component is complete */
	class NodeSCCVector {
	public:
		struct Node {
			uint32_t status{};
			uint32_t index{};
			uint32_t lowlink{};
			uint32_t starting{};
			Node *parent{};

			/* left is entered + 1 */
			void leave() { ++status; }
		};

		[[nodiscard]] auto getStatus(size_t i) const -> NodeStatus
		{
			auto status = nodes[i].status;
			if (status < baseStatus)
				return NodeStatus::unseen;
			return static_cast<NodeStatus>(status - baseStatus);
		}

		[[nodiscard]] auto get(size_t i) const -> const Node & { return nodes[i]; }

		auto enter(size_t i, uint32_t index, uint32_t starting, Node *parent) -> Node *
		{
			nodes[i] = {baseStatus + static_cast<uint32_t>(NodeStatus::entered), index, index,
				    starting, parent};
			return &nodes[i];
		}

		void maybeClearResize(size_t newSize)
		{
			if (baseStatus >= UINT32_MAX - 6) {
				nodes.clear();
				baseStatus = 0;
			} else {
				baseStatus += 3;
			}
			nodes.resize(newSize);
		}

	private:
		std::vector<Node> nodes;
		uint32_t baseStatus{};
	};

	/* The search for a cycle through a starting node. The nodes on the stack
	 * from any node an edge leads back to are all in the edge's component, so
	 * the edge closes such a cycle iff a starting node is among them. The
	 * stack is kept as the nodes being explored, innermost first through
	 * their parents, and apart, the explored ones that are not the root of
	 * their component */
	class SCCSearch {
	public:
		void reset()
		{
			explored = nullptr;
			pending.clear();
			index = 0;
			starting = 0;
		}

		/* Puts node I of NODES on the stack, to explore it */
		[[gnu::always_inline]] void enter(NodeSCCVector &nodes, size_t i, bool isStarting)
		{
			starting += static_cast<uint32_t>(isStarting);
			explored = nodes.enter(i, index++, starting, explored);
		}

		/* The node explored has an edge to node I of NODES, which is on the
		 * stack: returns whether the edge closes a cycle through a starting node */
		[[gnu::always_inline]] auto reach(const NodeSCCVector &nodes, size_t i, bool isStarting) -> bool
		{
			const auto &n = nodes.get(i);
			if (starting > n.starting || isStarting)
				return true;
			explored->lowlink = std::min(explored->lowlink, n.index);
			return false;
		}

		/* Done exploring the innermost node explored: if it reaches nothing
		 * below it on the stack, its component, it and the nodes above it,
		 * is complete. Its only starting node can be itself, alone: the
		 * search stops at any cycle through one */
		[[gnu::always_inline]] void finish(bool isStarting)
		{
			auto *n = explored;
			explored = n->parent;
			if (n->lowlink < n->index) {
				explored->lowlink = std::min(explored->lowlink, n->lowlink);
				pending.push_back(n);
				return;
			}
			starting -= static_cast<uint32_t>(isStarting);
			n->leave();
			while (!pending.empty() && pending.back()->index > n->index) {
				pending.back()->leave();
				pending.pop_back();
			}
		}

	private:
		NodeSCCVector::Node *explored{};	    /* the innermost node being explored */
		std::vector<NodeSCCVector::Node *> pending; /* explored, in a component not complete */
		uint32_t index{};
		uint32_t starting{}; /* the starting nodes on the stack */
	};


public:
	#CLASS#(const Config *conf) : ConsistencyChecker(conf) {};

protected: // subclasses may refine the generated checks (e.g., hand-written axioms)
	bool isConsistent(const EventLabel *lab) const override;
	bool isConsistent(const ExecutionGraph &g) const override;
	bool isCoherentRelinche(const ExecutionGraph &g) const override;
	std::optional<VerificationError> checkErrors(const EventLabel *lab, const EventLabel *&race) const override;
	std::vector<VerificationError> checkWarnings(const EventLabel *lab, const VSet<VerificationError> &reported, std::vector<const EventLabel *> &races) const override;
	std::vector<EventLabel *> getCoherentStores(ReadLabel *rLab) override;
	void filterCoherentRevisits(WriteLabel *sLab, std::vector<ReadLabel *> &ls) override;
	std::vector<EventLabel *> getCoherentPlacings(WriteLabel *sLab) override;
	void updateMMViews(EventLabel *lab) override;
	std::unique_ptr<VectorClock> calculatePrefixView(const EventLabel *lab) const override;
	std::unique_ptr<VectorClock> calculateRevisitPrefixView(const EventLabel *lab) const override;
	bool isDepTracking() const override;
	void calculateSaved(EventLabel *lab);
	void calculateViews(EventLabel *lab);
	mutable const EventLabel *cexLab{};
	void recomputeCacheCounters(const ExecutionGraph &g) const override;
	void resetCacheCounters() const override;
	void maybeDecreaseCacheCounters(const EventLabel *lab) const override;
	void maybeIncreaseCacheCounters(const EventLabel *lab) const override;
)";

} // namespace

enum class TraversalKind : std::uint8_t { DFS, SCC };

struct DFSParameters {
	using State = NFA::State;
	using Hook = std::function<void(CodeBuilder &)>;

	std::string name;	 // name of printed routine
	std::string status;	 // name of status arrays
	std::string extraParams; // Additional parameters to the routine besides worklist
	std::string savedParam;	 // saved param of label printing
	std::optional<unsigned> initViewIdx; // view calculations: init label's per-location view

	Hook atBegin; // at node discovery
	Hook atTreeE; // at tree-edge discovery
	Hook atCyclE; // at cyclic-edge discovery
	Hook atForwE; // at forward-edge discovery
	Hook atEnd;   // at node exit
	Hook atFinal; // at final-state discovery
	/* at final-state discovery through a positional relation (alloc, free, ...):
	 * the event is given as a position, as its label may be gone from the graph */
	std::function<void(CodeBuilder &, const std::string &)> atFinalPos;

	std::vector<char> visit{}; // indexed by state ID: "has visit array"
};

GenMCPrinter::GenMCPrinter(const KatModule &module, const Config &config) : Printer(module, config)
{
	className = getPrefix() + "Checker";
	guardName = std::string("GENMC_") + getPrefix() + "_CHECKER_HPP";

	/* Open required streams, if the user requested file printing */
	if (!getPrefix().empty()) {
		foutHpp = openFileForWriting(getConf().dir + "/" + className + ".hpp");
		outHpp = &foutHpp;
		foutCpp = openFileForWriting(getConf().dir + "/" + className + ".cpp");
		outCpp = &foutCpp;
	}

	/* CodeBuilders bind to the (now-wired) stream pointers. */
	hppB_.emplace(*outHpp);
	cppB_.emplace(*outCpp);
}

auto GenMCPrinter::shouldPrintSuccAcycChecks() const -> bool
{
	return !getModule().isDepTracking();
}

/* Emit "return true && a && b ... && z;" - one clause per indented line.
 * Emits "return true;" if `clauses` is empty. Caller owns the surrounding
 * block; this only emits at body-level + 1 below the current level. */
static void emitConjunction(CodeBuilder &c, const std::vector<std::string> &clauses)
{
	c.line("return true");
	for (auto &clause : clauses) {
		auto _ = c.bump();
		c.line("&& {}", clause);
	}
	c.line(";");
}

/* Emit "std::vector<DFSWorklistEntry> <var> = {{ {id, lab}, ... }};" populated
 * from `accepting` (reversed, to match the recursion's discovery order). */
template <std::ranges::range R>
static void emitStartStates(CodeBuilder &c, std::string_view var, R &&accepting,
			    std::string_view labVar)
{
	c.line("std::vector<DFSWorklistEntry> {} = {{", var);
	for (auto &s : accepting | std::views::reverse) {
		auto _ = c.bump();
		c.line("{{ {}, {} }},", s->getId(), labVar);
	}
	c.line("}};").blank();
}

auto GenMCPrinter::usesRfInvInAcycChecks() const -> bool
{
	auto result = false;
	for (auto &stmt : getModule().exports()) {
		auto *acyc = dynamic_cast<AcyclicConstraint *>(stmt->getConstraint());
		if (!acyc)
			continue;

		auto rfInv = Relation::createBuiltin(Relation::BuiltinID::rf).invert();
		visitRE(acyc->getRERef(), [&](auto &r) {
			auto *charRE = dynamic_cast<const CharRE *>(&*r);
			if (charRE && charRE->getLabel().getRelation().has_value() &&
			    *charRE->getLabel().getRelation() == rfInv)
				result = true;
		});
	}
	return result;
}

/*
 * Emits a worklist-based DFS. Entry form: {stateId, lab, isFinishing}.
 * A node is pushed twice: once for discovery, and once more with
 * isFinishing=true so that its post-order actions execute (e.g., mark it as "left").
 *
 * SCC runs Tarjan's algorithm (SCCSearch, in the checker's header): a node
 * stays on its stack until its component is complete, and the search stops
 * at the first edge that closes a cycle through a starting state.
 */
void GenMCPrinter::outputTraversal(const NFA &nfa, const DFSParameters &params, TraversalKind kind)
{
	/* The automaton may have no states, as the 0 of `r = 0` has none: its
	 * traversal then has no cases, and nothing starts it */
	assert(!params.name.empty() && params.visit.size() == nfa.getNumStates());

	const bool isSCC = (kind == TraversalKind::SCC);
	assert(!isSCC || params.atCyclE);
	const auto stateArr = [&](auto *s) {
		return std::format("{}_{}", params.status, s->getId());
	};
	const auto search = std::format("{}Search", params.status);

	/*
	 * SCC cycle-detection guard: an edge to a node on the stack ("entered")
	 * closes a cycle through a starting state iff one is on the stack at or
	 * above that node. Otherwise the edge lowers the explored node's lowlink.
	 */
	const auto sccEnteredGuard = [&](auto *s, std::string_view labVar) {
		return std::format("status == NodeStatus::entered && "
				   "{}.reach({}, {}->getStamp().get(), {})",
				   search, stateArr(s), labVar, s->isStarting());
	};

	/* SCC keeps Tarjan's index and lowlink along with the status; DFS only a status. */
	const auto vecElem = isSCC ? "NodeSCCVector" : "NodeStatusVector<uint32_t>";

	auto &h = hppB();
	auto &c = cppB();

	/* Declarations in the .hpp */
	for (auto &sUP : nfa.states())
		h.line("mutable {} {};", vecElem, stateArr(&*sUP));
	if (isSCC)
		h.line("mutable SCCSearch {};", search);
	h.blank();
	h.line("bool {}Iterative(std::vector<DFSWorklistEntry> &worklist{}) const;", params.name,
	       params.extraParams)
		.blank();

	/* Second (finishing) pop of a node: mark it `left` (SCC: complete its
	 * component, if it is the root) and run its exit actions. */
	auto emitFinishingBranch = [&](NFA::State *s) {
		{
			auto ifFinScope = c.ifStmt("isFinishing");
			if (params.visit[s->getId()]) {
				if (isSCC) {
					c.line("{}.finish({});", search, s->isStarting());
				} else {
					c.line("{}.setStatus(lab->getStamp().get(), "
					       "NodeStatus::left);",
					       stateArr(s));
				}
			}
			if (params.atEnd)
				params.atEnd(c);
			c.line("break;");
		}
		c.blank().blank();
	};

	/* First (discovery) pop: enter the node, schedule its finishing pop, and
	 * recurse along incoming edges. States without a visit array keep no status. */
	auto emitDiscovery = [&](NFA::State *s) {
		auto emitEntryAction = [&](CodeBuilder &c) {
			if (params.atBegin)
				params.atBegin(c);
			if (s->isStarting() && params.atFinal)
				params.atFinal(c);
		};

		if (!params.visit[s->getId()]) {
			emitEntryAction(c);
			return;
		}

		c.line("auto status = {}.getStatus(lab->getStamp().get());", stateArr(s));
		if (isSCC) {
			{
				auto ifUnseenScope = c.ifStmt("status == NodeStatus::unseen");
				c.line("{}.enter({}, lab->getStamp().get(), {});", search,
				       stateArr(s), s->isStarting());
				c.line("worklist.emplace_back({}, lab, true /* "
				       "isFinishing */);",
				       s->getId());
				emitEntryAction(c);
			}
			{
				auto elifEnteredScope = c.elifStmt("{}", sccEnteredGuard(s, "lab"));
				params.atCyclE(c);
			}
			{
				auto elseScope = c.elseStmt();
				c.line("break; /* already explored */");
			}
		} else {
			c.line("if (status != NodeStatus::unseen)")
				.indented("break; /* already explored */")
				.blank();
			c.line("worklist.emplace_back({}, lab, true);", s->getId());
			c.line("{}.setStatus(lab->getStamp().get(), "
			       "NodeStatus::entered);",
			       stateArr(s));
			emitEntryAction(c);
		}
		c.blank();
	};

	/* For each incoming edge, classify the neighbour by status (tree/cyclic/
	 * forward edge) and fire the matching hook. */
	using RB = Relation::BuiltinID;
	const auto positionalAccessor = [&](const NFA::Transition &t) -> std::optional<std::string> {
		auto r = t.label.getRelation();
		if (!r.has_value() || !r->isBuiltin())
			return std::nullopt;
		switch (r->toBuiltin()) {
		case RB::alloc:
		case RB::free:
		case RB::retire:
		case RB::unprotected:
		case RB::last_na_reads:
		case RB::last_na_writes:
		case RB::last_at_reads:
		case RB::last_at_writes: {
			const auto &outs = getModule().getTheory().getInfo(*r).genmc;
			return (r->isInverse() ? outs.pred : outs.succ) + "_pos";
		}
		default:
			return std::nullopt;
		}
	};
	const auto isSingleEventAccessor = [&](const NFA::Transition &t) {
		auto id = t.label.getRelation()->toBuiltin();
		return id == RB::alloc || id == RB::free || id == RB::retire;
	};
	const auto rfInv = Relation::createBuiltin(Relation::BuiltinID::rf).invert();
	const auto isRfPred = [&](const NFA::Transition &t) {
		auto r = t.label.getRelation();
		return r.has_value() && *r == rfInv;
	};

	auto emitTransitions = [&](NFA::State *s) {
		c.line("[[maybe_unused]] auto &g = *lab->getParent();");

		/* Print the transitions in a standard order */
		std::vector<NFA::Transition> ts(s->ins().begin(), s->ins().end());
		std::ranges::sort(ts, {}, [&](const auto &t) {
			return std::pair{t.dest->getId(),
					 printTransLabel(t, "pLab", "lab", params.savedParam)};
		});
		for (auto &t : ts) {
			/* Positional relations end the traversal: GenMC gives the event's
			 * position (alloc_pos() etc.), and its label may no longer exist */
			if (auto pos = positionalAccessor(t); pos.has_value()) {
				if (!params.atFinalPos || !t.dest->isStarting() ||
				    !std::ranges::empty(t.dest->ins()) ||
				    !t.label.getPostChecks().empty()) {
					std::cerr << "unsupported use of a positional relation (" << *pos
						  << ") in " << params.name << "\n";
					std::exit(EXIT_FAILURE); // NOLINT(concurrency-mt-unsafe)
				}
				auto pre = printPredSet("lab", t.label.getPreChecks());
				if (isSingleEventAccessor(t)) {
					auto posScope =
						c.kr("{}if (auto tmpE = g.{}(lab); tmpE)", pre, *pos);
					params.atFinalPos(c, "*tmpE");
				} else {
					auto posScope = c.kr("{}for (auto tmpE : g.{}(lab))", pre, *pos);
					params.atFinalPos(c, "tmpE");
				}
				continue;
			}
			/* GenMC keeps the init label out of view calculations: a read
			 * from init takes the view init holds for the read's location */
			const bool fromInit = params.initViewIdx.has_value() && isRfPred(t);
			if (fromInit && !t.dest->isStarting()) {
				auto initScope = c.kr("{}if (auto *iLab = "
						      "genmc::dyn_cast_if_present<InitLabel>(g.rf_pred(lab)); "
						      "iLab)",
						      printPredSet("lab", t.label.getPreChecks()));
				c.line("calcRes.update(iLab->locView("
				       "genmc::cast<ReadLabel>(lab)->getAddr(), {}));",
				       *params.initViewIdx);
			}
			auto transScope =
				c.kr("{}", printTransLabel(t, "pLab", "lab", params.savedParam));
			std::optional<CodeBuilder::Scope> notInitScope;
			if (fromInit)
				notInitScope.emplace(c.ifStmt("!genmc::isa<InitLabel>(pLab)"));
			if (!params.visit[t.dest->getId()]) {
				c.line("worklist.emplace_back({}, pLab);", t.dest->getId());
				if (params.atTreeE)
					params.atTreeE(c);
				continue;
			}
			c.line("auto status = {}.getStatus(pLab->getStamp().get());",
			       stateArr(t.dest));
			{
				auto ifUnseenScope = c.ifStmt("status == NodeStatus::unseen");
				c.line("worklist.emplace_back({}, pLab);", t.dest->getId());
				if (params.atTreeE)
					params.atTreeE(c);
			}
			if (params.atCyclE) {
				auto elifEnteredScope =
					isSCC ? c.elifStmt("{}", sccEnteredGuard(t.dest, "pLab"))
					      : c.elifStmt("status == NodeStatus::entered");
				params.atCyclE(c);
			}
			if (params.atForwE) {
				auto elifLeftScope = c.elifStmt("status == NodeStatus::left");
				params.atForwE(c);
			}
			c.blank();
		}
	};

	/* iterative DFS traversal */
	auto functionScope =
		c.function("bool {}::{}Iterative(std::vector<DFSWorklistEntry> &worklist{}) const ",
			   className, params.name, params.extraParams);
	{
		auto loopScope = c.whileLoop("!worklist.empty()");
		c.line("auto [stateId, lab, isFinishing] = worklist.back();");
		c.line("worklist.pop_back();");

		/* Per-state definition in the .cpp */
		auto switchScope = c.kr("switch(stateId)");
		for (auto &sUP : nfa.states()) {
			auto *s = &*sUP;
			/* Cases are emitted dense 0..n by construction: IDs are state indices. */
			auto caseScope = c.kr("case {}:", s->getId());
			emitFinishingBranch(s);
			emitDiscovery(s);
			emitTransitions(s);
			c.blank();
			c.line("break;");
		}
		c.line("default:");
		c.indented("UNREACHABLE();");
	}

	/* Finished the worklist, nothing found */
	c.line("return true;");
}

namespace {
/* Returns P if CST is `[P];any;[P] <= id`, and nullptr otherwise */
auto getCountedPredicate(const SubsetConstraint *cst) -> const CharRE *
{
	const auto *seqRE = dynamic_cast<const SeqRE *>(cst->getLHS());
	if (seqRE == nullptr || seqRE->getNumKids() != 3 || !cst->getRHS()->isId())
		return nullptr;

	const auto *predRE = dynamic_cast<const CharRE *>(seqRE->getKid(0));
	if (predRE == nullptr || !predRE->getLabel().isPredicate() ||
	    predRE->getLabel().isTruePredicate())
		return nullptr;

	if (!seqRE->getKid(1)->isAnyRelation() || *seqRE->getKid(2) != *predRE)
		return nullptr;

	return predRE;
}

auto replaceAll(std::string &inout, const std::string &what, const std::string &with) -> std::size_t
{
	std::size_t count{};
	for (std::string::size_type pos{};
	     std::string::npos != (pos = inout.find(what.data(), pos, what.length()));
	     pos += with.length(), ++count) {
		inout.replace(pos, what.length(), with.data(), with.length());
	}
	return count;
}
} // namespace

auto GenMCPrinter::printPredSet(const std::string &arg, const PredicateSet &preds) -> std::string
{
	if (preds.empty())
		return "";

	std::string out = "if (true";
	for (const auto &p : preds.preds()) {
		out += " && ";
		auto s = getModule().getTheory().getInfo(p).genmc;
		replaceAll(s, "#", arg);
		out += s;
	}
	out += ")";
	return out;
}

auto GenMCPrinter::printRelation(const std::string &res, const std::string &arg,
				 const std::optional<Relation> &r) -> std::string
{
	if (!r.has_value())
		return std::format("if (auto {} = {}; true)", res, arg);

	if (r->isBuiltin()) {
		const auto &rInfo = getModule().getTheory().getInfo(*r);
		const auto &outs = getModule().getTheory().getInfo(*r).genmc;
		const auto &s = r->isInverse() ? outs.pred : outs.succ;
		if (rInfo.arity == RelArity::OneOne ||
		    (rInfo.arity == RelArity::OneMany && r->isInverse()) ||
		    (rInfo.arity == RelArity::ManyOne && !r->isInverse())) {
			return std::format("if (auto {} = g.{}({}); {})", res, s, arg, res);
		}
		return std::format("for (auto &tmp : g.{}({})) if (auto *{} = &tmp; true)", s, arg,
				   res);
	}

	// No view indexes should appear when printing nfas.
	// if they do appear, it's from rec views => these are left rec
	// => just yield the same event (next state is guaranteed to be starting)
	if (isMutRecRelation(r->getID()))
		return std::format("if (auto {} = {}; true)", res, arg);

	// A user relation (relation r (genmc_pred: ..., genmc_succ: ...)): GenMC's
	// hook returns the related labels as a range of pointers
	assert(getModule().getTheory().hasInfo(*r));
	const auto &outs = getModule().getTheory().getInfo(*r).genmc;
	const auto &s = r->isInverse() ? outs.pred : outs.succ;
	return std::format("for (auto *{} : g.{}({}))", res, s, arg);
}

auto GenMCPrinter::printTransLabel(const NFA::Transition &t, const std::string &res,
				   const std::string &arg, const std::string &saveRes)
	-> std::string
{
	std::string out;
	out += printPredSet(arg, t.label.getPreChecks());
	out += printRelation(res, arg, t.label.getRelation());
	out += printPredSet(res, t.label.getPostChecks());

	/* If the destination is starting, update the saved result */
	if (!t.dest->isStarting() || saveRes.empty())
		return out;

	if (isMutRecRelation(t.label.getRelation()->getID())) {
		out += std::format("if ({}.update({}->view({})); true)", saveRes, res,
				   getPrintedIdx(getMutRecRelationDeclaration(
					   t.label.getRelation()->getID())));
	} else {
		out += std::format("if ({}.updateIdx({}->getPos()); true)", saveRes, res);
	}
	return out;
}

void GenMCPrinter::printHeader()
{
	auto &h = hppB();
	auto &c = cppB();

	/* Copyright notice in both HPP and CPP */
	h.raw(genmcCopyright).blank().raw(katerNotice).blank();
	c.raw(genmcCopyright).blank().raw(katerNotice).blank();

	/* HPP declarations */
	auto cHeaderDeclarations = std::string(commonHeaderDeclarations);
	replaceAll(cHeaderDeclarations, "#CLASS#", className);
	replaceAll(cHeaderDeclarations, "#GUARDNAME#", guardName);
	h.raw(cHeaderDeclarations).blank();

	/* CPP includes */
	const auto *viewHdr = getModule().isDepTracking() ? R"("genmc/ADT/DepView.hpp")"
							  : R"("genmc/ADT/View.hpp")";
	c.line("// NOLINTBEGIN")
		.line(R"(#include "{}.hpp")", className)
		.line(R"(#include "genmc/ADT/VSet.hpp")")
		.line("#include {}", viewHdr)
		.line(R"(#include "genmc/Execution/ExecutionGraph.hpp")")
		.line(R"(#include "genmc/Execution/GraphUtils.hpp")")
		.line(R"(#include "genmc/Support/VerificationError.hpp")")
		.blank()
		.line("#include <algorithm>")
		.blank();
}

void GenMCPrinter::printConsistency(
	const std::unordered_map<Statement *, std::string> &exportedNames)
{
	auto &module = getModule();
	auto &theory = module.getTheory();
	auto &hpp = hppB();
	auto &cpp = cppB();

	auto collectAcycSubset = [&](std::string_view callArg) {
		std::vector<std::string> clauses;
		for (auto &stmt : module.exports()) {
			auto *acycCst =
				dynamic_cast<const AcyclicConstraint *>(stmt->getConstraint());
			if (acycCst && !stmt->isExtra())
				clauses.push_back(
					std::format("{}({})", exportedNames.at(&*stmt), callArg));
		}
		/* Inclusions and equalities */
		for (auto &stmt : module.exports()) {
			auto *subCst =
				dynamic_cast<const SubsetConstraint *>(stmt->getConstraint());
			if (subCst && !stmt->isExtra())
				clauses.push_back(
					std::format("{}({})", exportedNames.at(&*stmt), callArg));
		}
		return clauses;
	};

	/* incremental version */
	{
		auto fun = cpp.function(
			"bool {}::isConsistent([[maybe_unused]] const EventLabel *lab) const",
			className);
		cpp.blank();
		emitConjunction(cpp, collectAcycSubset("lab"));
	}

	/* full version */
	{
		auto fun = cpp.function(
			"bool {}::isConsistent([[maybe_unused]] const ExecutionGraph &g) const",
			className);
		cpp.blank();
		emitConjunction(cpp, collectAcycSubset("g"));
	}

	/* coherence (special treatment) */
	{
		auto fun = cpp.function(
			"bool {}::isCoherentRelinche(const ExecutionGraph &g) const", className);
		cpp.blank();
		std::vector<std::string> clauses;
		for (auto &stmt : module.exports()) {
			auto *cohCst =
				dynamic_cast<const CoherenceConstraint *>(stmt->getConstraint());
			if (!cohCst)
				continue;
			assert(!stmt->isExtra());
			clauses.emplace_back("visitCoherenceRelinche(g)");
		}
		emitConjunction(cpp, clauses);
	}

	/* print the extras */
	for (auto &stmt : module.exports()) {
		if (stmt->isExtra()) {
			hpp.line("bool {}(const EventLabel *lab) {{ return {}(lab); }}",
				 *stmt->getNameOfExtra(), exportedNames.at(&*stmt));
		}
	}
	hpp.blank();

	/* pporf-before getter */
	auto pporfNFA = module.createPPORF()->toNFA();
	simplify(pporfNFA, theory);
	printPPoRfHpp(pporfNFA, module.isDepTracking());
	printPPoRfCpp(pporfNFA, module.isDepTracking());
	{
		auto fun = cpp.function(
			"std::unique_ptr<VectorClock> {}::calculatePrefixView(const EventLabel "
			"*lab) const",
			className);
		cpp.line("return std::make_unique<{}>(calcPPoRfBefore(lab));",
			 module.isDepTracking() ? "DepView" : "View");
	}

	/* The prefix a write's revisits take (rppo, if declared): reads in the
	 * prefix but not in this one stay revisitable */
	if (module.getRPPODeclaration() && module.isDepTracking()) {
		auto rpporfNFA = module.createRPPORF()->toNFA();
		simplify(rpporfNFA, theory);
		printPPoRfHpp(rpporfNFA, true, "RPPoRf");
		printPPoRfCpp(rpporfNFA, true, "RPPoRf");
	}
	{
		auto fun = cpp.function(
			"std::unique_ptr<VectorClock> {}::calculateRevisitPrefixView(const EventLabel "
			"*lab) const",
			className);
		if (module.getRPPODeclaration() && module.isDepTracking())
			cpp.line("return std::make_unique<DepView>(calcRPPoRfBefore(lab));");
		else
			cpp.line("return calculatePrefixView(lab);");
	}
}

void GenMCPrinter::printCacheCounters()
{
	auto &cpp = cppB();

	auto counterName = [](const CacheCounter &cacheC) -> std::string {
		return "cacheCounter" + cacheC.prefix;
	};

	/* Recomputing all cache counters */
	{
		auto fun = cpp.function("void {}::recomputeCacheCounters([[maybe_unused]] const "
					"ExecutionGraph &g) const",
					className);
		for (const auto &cacheC : cacheCounters)
			cpp.line("recompute{}(g);", cacheC.prefix);
	}

	/* Resetting all cache counters */
	{
		auto fun = cpp.function("void {}::resetCacheCounters() const", className);
		for (const auto &cacheC : cacheCounters)
			cpp.line("{} = -1;", counterName(cacheC));
	}

	/* Decreasing matching cache counters */
	{
		auto fun =
			cpp.function("void {}::maybeDecreaseCacheCounters([[maybe_unused]] const "
				     "EventLabel *lab) const",
				     className);
		for (const auto &cacheC : cacheCounters) {
			auto ifPred = cpp.kr("{}", cacheC.predCheck);
			cpp.line("VERIFY({} > 0);", counterName(cacheC));
			cpp.line("{} -= 1;", counterName(cacheC));
		}
	}

	/* Increasing matching cache counters */
	{
		auto fun =
			cpp.function("void {}::maybeIncreaseCacheCounters([[maybe_unused]] const "
				     "EventLabel *lab) const",
				     className);
		for (const auto &cacheC : cacheCounters) {
			auto ifPred = cpp.kr("{}", cacheC.predCheck);
			cpp.line("VERIFY({} >= 0);", counterName(cacheC));
			cpp.line("{} += 1;", counterName(cacheC));
		}
	}
}

void GenMCPrinter::printFooter()
{
	hppB().blank()
		.line("}};")
		.blank()
		.line("// NOLINTEND")
		.blank()
		.line("#endif /* {} */", guardName);
	cppB().line("// NOLINTEND");
}

// NOLINTNEXTLINE(readability-function-cognitive-complexity): pre-existing size
auto GenMCPrinter::output() -> bool
{
	printHeader();

	auto exported = true;
	auto &module = getModule();
	auto &theory = module.getTheory();
	auto &h = hppB();
	auto &c = cppB();

	/*
	 * The class body straddles printHeader() / printFooter(). We hold an
	 * outer bump for the duration of output()'s body so that every
	 * member-declaration emission via h.line("...") gets the implicit
	 * one-tab class-body indent. The scope ends before printFooter so the
	 * closing `};` and `#endif` sit at column 0.
	 */
	std::optional<CodeBuilder::Scope> hppClassBody;
	hppClassBody.emplace(h, ""); // bump-style scope (no close emit)

	{
		auto fn = c.function("bool {}::isDepTracking() const", className);
		c.line("return {:d};", module.isDepTracking());
	}

	/************************************************************
	** calculators, views, etc
	************************************************************/

	// We keep the names of the printed routines saved in the exportedNames map
	auto vc = 0U;
	auto sc = 0U;
	std::unordered_map<Statement *, std::string> exportedNames;

	/* First, keep mappings from recursive relations (these are used in regexps) */
	for (auto &let : module.lets()) {
		if (dynamic_cast<NoSavedExp *>(let->getSaved()))
			continue;

		/* Store the array index printed for the let statement
		 * (NOTE: the index corresponds to either the view or the set array) */
		auto letIdx = dynamic_cast<ViewExp *>(let->getSaved()) ? vc++ : sc++;
		letToIdxMap.insert({&*let, letIdx});

		/* Also keep mappings from recursive relations (these are used in regexps) */
		if (auto *mutRecRE = dynamic_cast<const MutRecRE *>(let->getRE())) {
			mutRecRelToLetMap.emplace(mutRecRE->getRelation().getID(), &*let);
		}
	}
	/* Then, export calculators */
	for (auto &let : module.lets()) {
		if (dynamic_cast<NoSavedExp *>(let->getSaved()))
			continue;

		// Print the calculation routines
		auto exportedNameSuffix = "Calc" + std::to_string(let->getID());
		auto name =
			toCamelCase(let->getName().substr(let->getName().find_last_of(":") + 1));
		printCalculator(&*let, exportedNameSuffix, name);

		// Also print a wrapper around the main entry point (in case we ever want
		// GenMC-specific code to run)
		auto exportedName = "check" + exportedNameSuffix;
		exportedNames[&*let] = exportedName;
		h.line("auto {}(const EventLabel *lab) const;", exportedName);
		{
			auto fn = c.function("auto {}::{}(const EventLabel *lab) const", className,
					     exportedName);
			c.line("[[maybe_unused]] auto &g = *lab->getParent();").blank();
			c.line("return visit{}(lab);", exportedNameSuffix);
		}
	}
	{
		auto fn = c.function("void {}::calculateSaved([[maybe_unused]] EventLabel *lab)",
				     className);
		for (auto &let : module.lets()) {
			if (!dynamic_cast<SetExp *>(let->getSaved()))
				continue;
			c.line("lab->addSaved({}(lab));", exportedNames[&*let]);
		}
	}
	{
		auto fn = c.function("void {}::calculateViews(EventLabel *lab)", className);
		c.line("lab->setViews({{}});");
		for (auto &let : module.lets()) {
			if (!dynamic_cast<ViewExp *>(let->getSaved()))
				continue;
			if (let->hasCodeToPrint())
				c.raw(*let->getCodeToPrint()).raw("\n");
			/* The slot exists while the view is computed */
			auto viewScope = c.kr("");
			c.line("lab->addView({{}});");
			c.line("lab->setView(std::move({}(lab)), {});", exportedNames[&*let],
			       getPrintedIdx(&*let));
		}
	}
	{
		auto fn = c.function("void {}::updateMMViews(EventLabel *lab)", className);
		c.line("calculateViews(lab);").line("calculateSaved(lab);");
		if (!module.isDepTracking()) { /* we can optimize the calculation */
			c.line("lab->setPrefixView(calculatePrefixView(lab));");
		}
	}

	// FIXME: Somewhere sanitize exports (unless has to be <= )

	// First, print the main consistency check dictated by the constraint.
	for (auto &stmt : module.exports()) {
		std::string exportedNameSuffix;
		bool counterexample = false;
		auto visitor = make_visitor(
			type_list<AcyclicConstraint, SubsetConstraint, EqualityConstraint,
				  WarningConstraint, ErrorConstraint, CoherenceConstraint,
				  TotalityConstraint>{},
			[&](const AcyclicConstraint &acst) {
				exportedNameSuffix = "ConsAcyclic" + std::to_string(stmt->getID());
				printAcyclic(&acst, exportedNameSuffix);
			},
			[&](const SubsetConstraint &scst) {
				exportedNameSuffix =
					"ConsInclusion" + std::to_string(stmt->getID());
				printSubset(&scst, exportedNameSuffix, false, false);
			},
			[&](const EqualityConstraint &ecst) {
				exportedNameSuffix = "ConsEquality" + std::to_string(stmt->getID());
				printSubset(&ecst, exportedNameSuffix + "Direct", false, false);
				auto convC = SubsetConstraint::create(
					ecst.getRHS()->clone(), ecst.getLHS()->clone(),
					ecst.sameEnds(), ecst.rotated());
				printSubset(&*convC, exportedNameSuffix + "Converse", false, false);
				h.line("bool visit{}(const EventLabel *lab) const;",
				       exportedNameSuffix);
				auto fn =
					c.function("bool {}::visit{}(const EventLabel *lab) const",
						   className, exportedNameSuffix);
				c.line("return visit{}Direct(lab) && visit{}Converse(lab);",
				       exportedNameSuffix, exportedNameSuffix);
			},
			[&](const WarningConstraint &wcst) {
				counterexample = true;
				exportedNameSuffix = "Warning" + std::to_string(stmt->getID());
				printWarning(&wcst, exportedNameSuffix);
			},
			[&](const ErrorConstraint &wcst) {
				counterexample = true;
				exportedNameSuffix = "Error" + std::to_string(stmt->getID());
				printWarning(&wcst, exportedNameSuffix);
			},
			[&](const CoherenceConstraint &ccst) { printCoherence(&ccst); },
			/* Unreachable today: the grammar admits totality only in "assume" */
			[&](const TotalityConstraint &tcst) {
				LOG(VerbosityLevel::Error) << "cannot export totality constraint";
				exported = false;
			});
		visitor(*stmt->getConstraint());

		// Skip if there was nothing to export
		if (exportedNameSuffix.empty())
			continue;

		auto exportedName = "check" + exportedNameSuffix;
		exportedNames[&*stmt] = exportedName;

		// Then, print the "unless" routine with the respective name
		printUnless(stmt->getUnless(), "Unless" + exportedNameSuffix, counterexample);

		// Finally, print a checker that combines the main routine and the unless
		// clause, as well as GenMC-specific code

		//  Incremental version:
		h.line("bool {}(const EventLabel *lab) const;", exportedName);
		{
			auto fn = c.function("bool {}::{}(const EventLabel *lab) const", className,
					     exportedName);
			c.line("[[maybe_unused]] auto &g = *lab->getParent();").blank();
			if (stmt->hasCodeToPrint())
				c.raw(*stmt->getCodeToPrint()).raw("\n");
			if (stmt->getUnless()) {
				c.line("if (visitUnless{}(lab))", exportedNameSuffix)
					.indented("return true;")
					.blank();
			}
			c.line("return visit{}(lab);", exportedNameSuffix);
		}

		//  Full version, of the constraints isConsistent(g) checks: the
		//  acyclicity ones have their own, the inclusions and equalities are
		//  checked at every label
		if (dynamic_cast<const AcyclicConstraint *>(stmt->getConstraint())) {
			h.line("bool {}(const ExecutionGraph &g) const;", exportedName);
			auto fn = c.function("bool {}::{}(const ExecutionGraph &g) const",
					     className, exportedName);
			c.line("return visit{}Full(g);", exportedNameSuffix);
		} else if (dynamic_cast<const SubsetConstraint *>(stmt->getConstraint())) {
			h.line("bool {}(const ExecutionGraph &g) const;", exportedName);
			auto fn = c.function("bool {}::{}(const ExecutionGraph &g) const",
					     className, exportedName);
			c.line("return std::ranges::all_of(g.labels(), [&](auto &lab) {{ return "
			       "{}(&lab); }});",
			       exportedName);
		}
	}

	{
		auto fn = c.function(
			"std::optional<VerificationError> {}::checkErrors([[maybe_unused]] const "
			"EventLabel *lab, [[maybe_unused]] const EventLabel *&race) const",
			className);
		for (auto &stmt : module.exports()) {
			auto *errorCst =
				dynamic_cast<const ErrorConstraint *>(stmt->getConstraint());
			if (!errorCst)
				continue;
			{
				auto ifScope = c.ifStmt("!{}(lab)", exportedNames[&*stmt]);
				c.line("race = cexLab;")
					.line("return {{VerificationError::{}}};",
					      errorCst->getWarningName());
			}
			c.blank().blank();
		}
		c.line("return {{}};");
	}

	{
		auto fn = c.function(
			"std::vector<VerificationError> {}::checkWarnings(const EventLabel *lab, "
			"const VSet<VerificationError> &seenWarnings, std::vector<const EventLabel "
			"*> &racyLabs) const",
			className);
		c.line("std::vector<VerificationError> result;").blank();
		for (auto &stmt : module.exports()) {
			auto *warnCst =
				dynamic_cast<const WarningConstraint *>(stmt->getConstraint());
			if (!warnCst || dynamic_cast<const ErrorConstraint *>(warnCst))
				continue;
			{
				auto ifScope = c.ifStmt("seenWarnings.count(VerificationError::{})"
							" == 0 && !{}(lab)",
							warnCst->getWarningName(),
							exportedNames[&*stmt]);
				c.line("racyLabs.push_back(cexLab);")
					.line("result.push_back(VerificationError::{});",
					      warnCst->getWarningName());
			}
			c.blank().blank();
		}
		c.line("return result;");
	}

	printConsistency(exportedNames);
	printCacheCounters();

	hppClassBody.reset();
	printFooter();
	return exported;
}

auto GenMCPrinter::getStateVisitAssignment(const NFA &nfa) const -> std::vector<char>
{
	std::vector<char> result(nfa.getNumStates(), 0);

	/* Helper that determines whether a state has any "outpoints" (i.e.,
	 * whether the edges leaving a state lead anywhere) */
	auto hasOutpoints = [&](NFA::State *s) {
		return std::ranges::any_of(s->ins(),
					   [&](auto &t) { return t.dest->hasIncoming(); });
	};
	/* A state should have a visit array if it has many entrypoints,
	 * and these are meaningful (i.e., if they lead nowhere, having a visit
	 * array doesn't really save anything) */
	auto shouldHaveVisitArray = [&](NFA::State *s) {
		return s->getNumOutgoing() > 1 &&
		       std::ranges::any_of(s->ins(), [&](auto &t) { return hasOutpoints(t.dest); });
	};

	for (auto &sUP : nfa.states()) {
		result[sUP->getId()] =
			static_cast<char>(getConf().emitVisitArrays || shouldHaveVisitArray(&*sUP));
	}
	return result;
}

void GenMCPrinter::printSubset(const SubsetConstraint *subCst, std::string prefix,
			       bool counterexample, bool viewOfRHS)
{
	auto nfaLHS = subCst->getLHS()->toNFA();
	simplify(nfaLHS, getModule().getTheory());
	auto nfaRHS = subCst->getRHS()->toNFA();
	simplify(nfaRHS, getModule().getTheory());

	auto &hpp = hppB();
	auto &cpp = cppB();

	/* Constraints counting predicate instances get ad-hoc counting code */
	if (const auto *countedRE = getCountedPredicate(subCst); countedRE != nullptr) {
		std::string counterName = "cacheCounter" + prefix;
		const auto &predSet = countedRE->getLabel().getPreChecks();
		std::string predCheck = printPredSet("lab", predSet);

		hpp.line("mutable int {} = 0;", counterName);
		hpp.line("void recompute{}(const ExecutionGraph &g) const;", prefix);
		{
			auto fun =
				cpp.function("void {}::recompute{}(const ExecutionGraph &g) const",
					     className, prefix);
			{
				auto lam = cpp.lambda("auto isMatchingLabel = [](const auto &l)");
				cpp.line("auto *lab = &l;");
				cpp.line("{}", predCheck);
				cpp.indented("return true;");
				cpp.line("return false;");
			}
			cpp.line("{} = std::count_if(g.label_begin(), g.label_end(), "
				 "isMatchingLabel);",
				 counterName);
		}

		hpp.line("bool visit{}(const EventLabel *lab) const;", prefix);
		{
			auto fun = cpp.function("bool {}::visit{}(const EventLabel *lab) const",
						className, prefix);
			cpp.line("auto &g = *lab->getParent();");
			cpp.line("if ({} == -1) /* Cache is empty */", counterName);
			cpp.indented("recompute{}(g);", prefix);

			cpp.line("return {} < 2;", counterName);
		}

		cacheCounters.push_back({prefix, predCheck});
		return;
	}

	auto markAccepting = [](std::string statusName) -> DFSParameters::Hook {
		return [s = std::move(statusName)](CodeBuilder &c) {
			c.line("{}Accepting[lab->getStamp().get()] = true;", s);
		};
	};
	DFSParameters paramsLHS = {
		.name = "visitLHS" + prefix,
		.status = "visitedLHS" + prefix,
		.savedParam = "",
		.atFinal = markAccepting("visitedLHS" + prefix),
		.visit = getStateVisitAssignment(nfaLHS),
	};
	DFSParameters paramsRHS = {
		.name = "visitRHS" + prefix,
		.status = "visitedRHS" + prefix,
		.savedParam = "",
		.atFinal = markAccepting("visitedRHS" + prefix),
		.visit = getStateVisitAssignment(nfaRHS),
	};

	/* Can we skip visiting the RHS? If so, change the LHS config*/
	std::optional<int> rhsViewIdx;
	auto shouldVisitRHS = true;
	/* Whether the DFS routines record the accepting states they reach (only
	 * when they compare the two sides; otherwise they return at the first one
	 * or compare against a view, and the arrays would cost O(graph) per call
	 * for nothing) */
	auto marksAccepting = true;
	auto lets = getModule().lets();
	auto viewLet = std::ranges::find_if(lets, [&](auto &let) {
		return viewOfRHS && dynamic_cast<const ViewExp *>(let->getSaved()) &&
		       *let->getRE() == *subCst->getRHS();
	});
	if (subCst->isEmpty()) {
		/* Case e <= 0 : we can optimize and return false if any accepting is
		 * reachable, the event it is reached at being the counterexample */
		marksAccepting = false;
		paramsLHS.atFinal = [counterexample](CodeBuilder &c) {
			if (counterexample)
				c.line("cexLab = lab;");
			c.line("return false;");
		};
		paramsLHS.atFinalPos = [counterexample](CodeBuilder &c, const std::string &e) {
			if (counterexample)
				c.line("cexLab = g.getEventLabelIfPresent({});", e);
			c.line("return false;");
		};
	} else if (viewLet != std::ranges::end(lets)) {
		shouldVisitRHS = false;
		marksAccepting = false;
		rhsViewIdx = getPrintedIdx(&**viewLet);
		/* Case e <= VIEW: return false if any accepting is not in view */
		paramsLHS.extraParams = ", const View &v";
		paramsLHS.atFinal = [counterexample](CodeBuilder &c) {
			{
				auto ifContainsScope = c.ifStmt("!v.contains(lab->getPos())");
				if (counterexample)
					c.line("cexLab = lab;");
				c.line("return false;");
			}
			c.blank().blank();
		};
		paramsLHS.atFinalPos = [counterexample](CodeBuilder &c, const std::string &e) {
			auto ifContainsScope = c.ifStmt("!v.contains({})", e);
			if (counterexample)
				c.line("cexLab = g.getEventLabelIfPresent({});", e);
			c.line("return false;");
		};
	}

	/* Print the DFS routines */
	outputTraversal(nfaLHS, paramsLHS, TraversalKind::DFS);
	if (shouldVisitRHS) {
		outputTraversal(nfaRHS, paramsRHS, TraversalKind::DFS);
	}

	auto emitArrayInit = [&](const NFA &nfa, const DFSParameters &params) {
		for (auto &s : nfa.states() | std::views::filter([&](auto &sUP) {
				       return params.visit[sUP->getId()];
			       })) {
			cpp.line("{}_{}.maybeClearResize(g.getMaxStamp().get() + 1);",
				 params.status, s->getId());
		}
	};

	/* Extra arrays used by the DFS routines */
	if (marksAccepting) {
		hpp.line("mutable std::vector<bool> {}Accepting;", paramsLHS.status);
		if (shouldVisitRHS)
			hpp.line("mutable std::vector<bool> {}Accepting;", paramsRHS.status);
	}

	/* "visit" function for the automaton (again based on the RHS) */
	hpp.line("bool visit{}(const EventLabel *lab) const;", prefix);
	{
		auto fun = cpp.function("bool {}::visit{}(const EventLabel *lab) const", className,
					prefix);
		cpp.line("[[maybe_unused]] auto &g = *lab->getParent();").blank();
		emitArrayInit(nfaLHS, paramsLHS);
		if (shouldVisitRHS) {
			emitArrayInit(nfaRHS, paramsRHS);
		}
		if (marksAccepting) {
			cpp.line("{}Accepting.clear();", paramsLHS.status)
				.line("{}Accepting.resize(g.getMaxStamp().get() + 1, false);",
				      paramsLHS.status);
			if (shouldVisitRHS) {
				cpp.line("{}Accepting.clear();", paramsRHS.status)
					.line("{}Accepting.resize(g.getMaxStamp().get() + 1, "
					      "false);",
					      paramsRHS.status);
			}
			cpp.blank();
		}

		if (!shouldVisitRHS) {
			/* An LHS that accepts nothing is within the view */
			if (std::ranges::empty(nfaLHS.accepting())) {
				cpp.line("return true;");
				return;
			}

			cpp.line("auto &v = lab->view({});", *rhsViewIdx).blank();

			cpp.line("/* Explore from all accepting states in LHS using DFS */");
			emitStartStates(cpp, "startStatesLHS", nfaLHS.accepting(), "lab");
			cpp.line("return {}Iterative(startStatesLHS, v);", paramsLHS.name);
		} else {
			if (!std::ranges::empty(nfaLHS.accepting())) {
				cpp.line(
					"/* Explore from all accepting states in LHS using DFS */");
				emitStartStates(cpp, "startStatesLHS", nfaLHS.accepting(), "lab");
				cpp.line("if (!{}Iterative(startStatesLHS))", paramsLHS.name);
				cpp.indented("return false;").blank();
			}

			if (!std::ranges::empty(nfaRHS.accepting())) {
				cpp.line(
					"/* Explore from all accepting states in RHS using DFS */");
				emitStartStates(cpp, "startStatesRHS", nfaRHS.accepting(), "lab");
				cpp.line("if (!{}Iterative(startStatesRHS))", paramsRHS.name);
				cpp.indented("return false;").blank();
			}

			if (marksAccepting) {
				auto loopScope =
					cpp.forLoop("auto i = 0u; i < {}Accepting.size(); i++",
						    paramsLHS.status);
				{
					auto ifAcceptingScope =
						cpp.ifStmt("{}Accepting[i] && !{}Accepting[i]",
							   paramsLHS.status, paramsRHS.status);
					if (counterexample) {
						cpp.line("cexLab = &*std::find_if(g.label_begin(), "
							 "g.label_end(), [&](auto &lab){{ return "
							 "lab.getStamp() == i; }});");
					}
					cpp.line("return false;");
				}
				cpp.blank();
			}
			cpp.line("return true;");
		}
	}
}

void GenMCPrinter::printUnless(const Constraint *cst, std::string prefix, bool counterexample)
{
	if (!cst) {
		hppB().line(
			"bool check{}([[maybe_unused]] const EventLabel *lab) {{ return false; }}",
			prefix);
		return;
	}

	auto *subCst = dynamic_cast<const SubsetConstraint *>(cst);
	assert(subCst);
	/* The clauses of errors and warnings are checked after the views are
	 * updated, those of consistency constraints by isConsistent(lab) */
	printSubset(subCst, prefix, counterexample, counterexample);
}

void GenMCPrinter::printWarning(const WarningConstraint *stmt, std::string prefix)
{
	/* Print a "visit" function for the automaton */
	hppB().line("bool visit{}(const EventLabel *lab) const;", prefix);
	{
		auto fn = cppB().function(
			"bool {}::visit{}([[maybe_unused]] const EventLabel *lab) const", className,
			prefix);
		cppB().line("return false;");
	}
}

void GenMCPrinter::printAcyclic(const AcyclicConstraint *acycCst, std::string prefix)
{
	// Take the reflexive-transitive closure, which typically helps minizing the
	// NFA. Doing so is alright because the generated DFS code discounts empty
	// paths anyway.
	auto nfa = acycCst->getRE()->toNFA();
	nfa.star();
	simplify(nfa, getModule().getTheory());
	removeSimilarTransitions(nfa);

	if (getConf().verbose >= 3)
		std::cerr << "Acyclic size " << nfa.size() << "\n";

	// For non-dep-tracking models, we can iterate the NFA based on
	// outgoing transitions. This is more efficient, as maximal graph
	// events typically have more incoming than outgoing edges
	if (shouldPrintSuccAcycChecks())
		nfa.flip();

	/* star() leaves one state, starting and accepting, that every iteration
	 * of the relation passes through, and simplify() keeps it (it merges
	 * steps only past states that do not accept): the cycles of the relation
	 * are the cycles of the product through that state */
	assert(nfa.getNumStarting() == 1 && nfa.getNumAccepting() == 1 &&
	       (*nfa.start_begin())->isAccepting());

	DFSParameters params = {
		.name = "visit" + prefix,
		.status = "visited" + prefix,
		.savedParam = "",
		.atCyclE = [](CodeBuilder &c) { c.line("return false; /* cycle detected */"); },
		.visit = getStateVisitAssignment(nfa),
	};
	/* The search counts the nodes of that state on its stack */
	for (auto *s : nfa.starting())
		params.visit[s->getId()] = 1;
	outputTraversal(nfa, params, TraversalKind::SCC);

	auto &hpp = hppB();
	auto &cpp = cppB();

	auto emitInits = [&]() {
		cpp.line("{}Search.reset();", params.status);
		for (auto &sUP : nfa.states() | std::views::filter([&](auto &sUP) {
					 return params.visit[sUP->getId()];
				 })) {
			cpp.line("{}_{}.maybeClearResize(g.getMaxStamp().get() + 1);",
				 params.status, sUP->getId());
		}
		cpp.blank();
	};

	/* "visit<Prefix>(lab)" -- incremental version. */
	hpp.line("bool visit{}(const EventLabel *lab) const;", prefix).blank();
	{
		auto fnScope = cpp.function("bool {}::visit{}(const EventLabel *lab) const",
					    className, prefix);
		cpp.line("[[maybe_unused]] auto &g = *lab->getParent();").blank();
		emitInits();

		/* Don't visit all states: for incremental checks, visit the ones you can
		 * enter with po/rf. NOTE: We use po and not po_imm below (even though the
		 * NFAs use po_imm) because the user is now allowed to use po_imm (so all
		 * po_imms are po_imm+), and we assume that only po_imm is included in
		 * itself. */
		cpp.line("/* States we need to explore from using DFS */");
		cpp.line("std::vector<DFSWorklistEntry> startStates = {{");
		for (auto &sUP : nfa.states() | std::views::reverse) {
			auto startStatesDefScope = cpp.bump();
			auto ts = shouldPrintSuccAcycChecks() ? sUP->ins() : sUP->outs();
			if (std::ranges::all_of(ts, [&](auto &t) {
				    auto rOpt = t.label.getRelation();
				    return rOpt.has_value() && !rOpt->isInverse() &&
					   (getModule().getTheory().isIncludedIn(
						    *rOpt, Relation::createBuiltin(
								   Relation::BuiltinID::po)) ||
					    getModule().getTheory().isIncludedIn(
						    *rOpt, Relation::createBuiltin(
								   Relation::BuiltinID::rf)) ||
					    !rOpt->isBuiltin());
			    })) {
				continue;
			}
			cpp.line("{{ {}, lab }},", sUP->getId());
		}
		cpp.line("}};").blank();
		cpp.line("return {}Iterative(startStates);", params.name);
	}

	/* "visit<Prefix>Full(g)" -- full-graph version. */
	hpp.line("bool visit{}Full(const ExecutionGraph &g) const;", prefix).blank();
	{
		auto fnFullScope = cpp.function(
			"bool {}::visit{}Full(const ExecutionGraph &g) const", className, prefix);
		emitInits();

		{
			auto initStartStatesScope = cpp.lambda("auto exploreLab = [&](auto &lab)");
			cpp.line("/* Explore from all accepting states using DFS */");
			emitStartStates(cpp, "startStates", nfa.accepting(), "&lab");
			cpp.line("return {}Iterative(startStates);", params.name);
		}

		cpp.line("return std::ranges::all_of(g.labels(), exploreLab);");
	}
}

void GenMCPrinter::printCoherence(const CoherenceConstraint *cohCst)
{
	auto s = std::string(coherenceFuns);
	replaceAll(s, "#CLASS#", className);
	replaceAll(s, "#HB#", std::to_string(getPrintedIdx(getModule().getCOHDeclaration())));
	cppB().line("{}", s);

	// For coherence, we detect violations by performing multiple DFSs (for each memory access).
	// In contrast to acyclicity, we don't take the reflexive-transitive closure here.
	// This is much slower, but can be optimized for Relinche.
	// (This can potentially be optimized by taking the rotational closure of COH instead.)
	//
	// NOTE: As this is currently only used in Relinche, we instead print an optimized
	//       version that checks for hbpo;eco;hbpo;lin irreflexivity.
	const auto &module = getModule();
	auto ecoREUP = PlusRE::createOpt(AltRE::createOpt(module.getRegisteredRE("rf")->clone(),
							  module.getRegisteredRE("mo")->clone(),
							  module.getRegisteredRE("fr")->clone()));
	const auto *hbpoRE = module.getRegisteredRE(cohCst->getID());
	auto nfa = SeqRE::createOpt(hbpoRE->clone(), ecoREUP->clone(), hbpoRE->clone(),
				    module.getRegisteredRE("lin")->clone())
			   ->toNFA();

	simplify(nfa, getModule().getTheory());
	// Opt: We can just get away with predecessor checks

	auto prefix = "Coherence"s;
	DFSParameters params = {
		.name = "visit" + prefix,
		.status = "visited" + prefix,
		.extraParams = ", const EventLabel *initLab",
		.savedParam = "",
		.atFinal = [](CodeBuilder &c) { c.line("if (lab == initLab) return false;"); },
		.visit = getStateVisitAssignment(nfa),
	};
	outputTraversal(nfa, params, TraversalKind::DFS);

	auto &c = cppB();
	auto &h = hppB();

	// Helper that emits the per-state init lines at the current level.
	auto printInitializations = [&]() {
		for (auto &iSUP : nfa.states() | std::views::filter([&](auto &s) {
					  return params.visit[s->getId()];
				  })) {
			c.line("{}_{}.maybeClearResize(g.getMaxStamp().get() + 1);", params.status,
			       iSUP->getId());
		}
		c.blank();
	};

	/* Print only a "visitCoherenceRelinche(G)" for the constraint */
	h.line("bool visit{}Relinche(const ExecutionGraph &g) const;", prefix).blank();
	{
		auto fn = c.function("bool {}::visit{}Relinche(const ExecutionGraph &g) const",
				     className, prefix);
		for (auto &sUP : nfa.accepting()) {
			auto loop = c.forLoop("auto &lab : g.labels()");
			c.line("if (!genmc::isa<MethodBeginLabel>(&lab))");
			c.indented("continue;").blank();
			printInitializations();

			/* Explore from single accepting state only, we need to reset vectors before
			 * every DFS run. */
			c.line("/* Explore from this accepting state using DFS */");
			c.line("std::vector<DFSWorklistEntry> startState = {{ {{ {}, &lab }} }};",
			       sUP->getId());

			c.line("if (!{}Iterative(startState, &lab /* initLab */))", params.name);
			c.indented("return false;");
		}
		c.line("return true;");
	}
}

void GenMCPrinter::printCalculator(const LetStatement *let, std::string prefix, std::string name)
{
	auto *viewExp = dynamic_cast<const ViewExp *>(let->getSaved());
	auto *setExp = dynamic_cast<const SetExp *>(let->getSaved());
	assert(viewExp || setExp);
	auto nfa = viewExp ? viewExp->getRE()->toNFA() : setExp->getRE()->toNFA();
	simplify(nfa, getModule().getTheory());

	bool isView = dynamic_cast<const ViewExp *>(let->getSaved());
	auto paramType = isView ? "View"s : "VSet<Event>"s;
	DFSParameters params = {
		.name = "visit" + prefix,
		.status = "visited" + prefix,
		.extraParams = ", " + paramType + " &calcRes",
		.savedParam = "calcRes",
		.initViewIdx = isView ? std::optional<unsigned>(getPrintedIdx(let)) : std::nullopt,
		.visit = getStateVisitAssignment(nfa),
	};
	outputTraversal(nfa, params, TraversalKind::DFS);

	auto &h = hppB();
	auto &c = cppB();

	/* "visitCalc(lab)" -- compute the saved value. */
	h.line("{} visit{}(const EventLabel *lab) const;", paramType, prefix);
	{
		auto fn = c.function("{} {}::visit{}(const EventLabel *lab) const", paramType,
				     className, prefix);
		c.line("[[maybe_unused]] auto &g = *lab->getParent();")
			.line("{} calcRes;", paramType)
			.blank();
		c.line("{}", isView ? "calcRes.updateIdx(lab->getPos());" : "FIXME");
		for (auto &sUP : nfa.states() | std::views::filter([&](auto &sUP) {
					 return params.visit[sUP->getId()];
				 })) {
			c.line("{}_{}.maybeClearResize(g.getMaxStamp().get() + 1);", params.status,
			       sUP->getId());
		}
		c.blank();

		c.line("/* Explore from all accepting states using DFS */");
		emitStartStates(c, "startStates", nfa.accepting(), "lab");

		c.line("{}Iterative(startStates, calcRes);", params.name);
		c.line("return calcRes;");
	}

	/* Getter for the saved result; views are also addressed by index, and the
	 * base class provides getHbView() on top of getHbViewIndex() */
	if (!isView || name != "Hb")
		h.line("auto get{}{}(const EventLabel *lab) const -> const {} & {{ return "
		       "lab->{}({}); }}",
		       name, isView ? "View" : "Set", paramType, isView ? "view" : "calculated",
		       getPrintedIdx(let));
	if (isView)
		h.line("auto get{}ViewIndex() const -> unsigned {{ return {}; }}", name,
		       getPrintedIdx(let));
	h.blank();
}

void GenMCPrinter::printPPoRfHpp(const NFA &nfa, bool deps, const std::string &name)
{
	const auto vt = deps ? "DepView" : "View";

	/* visitPPoRfXX for each state */
	std::for_each(nfa.states_begin(), nfa.states_end(), [&](auto &s) {
		hppB().line("void visit{}{}(const EventLabel *lab, {} &pporf) const;",
			    name, s->getId(), vt);
	});
	hppB().blank();

	/* calc<name>Before for the automaton */
	hppB().line("{} calc{}Before(const EventLabel *lab) const;", vt, name).blank();

	/* status arrays */
	std::for_each(nfa.states_begin(), nfa.states_end(), [&](auto &s) {
		hppB().line("mutable std::vector<NodeStatus> visited{}{};", name, s->getId());
	});
	hppB().blank();
}

void GenMCPrinter::printPPoRfCpp(const NFA &nfa, bool deps, const std::string &name)
{
	auto &c = cppB();
	const auto vt = deps ? "DepView" : "View";

	/* Optimization for non-dep-tracking models */
	if (!deps) {
		auto fn = c.function("{} {}::calc{}Before(const EventLabel *lab) const", vt,
				     className, name);
		c.line("[[maybe_unused]] auto &g = *lab->getParent();")
			.line("View pporf;")
			.line("pporf.updateIdx(lab->getPos());")
			.blank()
			.line("if (auto *pLab = g.po_imm_pred(lab); pLab)")
			.indented("pporf.update(pLab->getPrefixView());");
		c.line("if (auto *rLab = genmc::dyn_cast<ReadLabel>(lab); rLab && rLab->getRf())")
			.indented("pporf.update(rLab->getRf()->getPrefixView());");
		c.line("auto *tsLab = genmc::dyn_cast<ThreadStartLabel>(lab);")
			.line("if (tsLab && tsLab->getCreate())")
			.indented("pporf.update(tsLab->getCreate()->getPrefixView());");
		c.line("if (auto *tjLab = genmc::dyn_cast<ThreadJoinLabel>(lab))")
			.indented("pporf.update(g.getLastThreadLabel(tjLab->getChildId())"
				  "->getPrefixView());");
		c.line("return pporf;");
		return;
	}

	std::for_each(nfa.states_begin(), nfa.states_end(), [&](auto &s) {
		{
			auto fn = c.function(
				"void {}::visit{}{}(const EventLabel *lab, {} &pporf) const",
				className, name, s->getId(), vt);
			c.line("[[maybe_unused]] auto &g = *lab->getParent();")
				.blank()
				.line("visited{}{}[lab->getStamp().get()] = "
				      "NodeStatus::entered;",
				      name, s->getId());
			if (s->isStarting()) {
				c.line("pporf.updateIdx(lab->getPos());");
			}
			std::for_each(s->in_begin(), s->in_end(), [&](auto &t) {
				/* printTransLabel returns an "if (...)" predicate
				 * fragment; pair it with kr() to open the brace and
				 * indent the body. */
				auto trans = c.kr("{}", printTransLabel(t, "pLab", "lab", "pporf"));
				c.line("auto status = "
				       "visited{}{}[pLab->getStamp().get()];",
				       name, t.dest->getId())
					.line("if (status == NodeStatus::unseen)")
					.indented("visit{}{}(pLab, pporf);", name, t.dest->getId());
			});
			c.line("visited{}{}[lab->getStamp().get()] = NodeStatus::left;",
			       name, s->getId());
		}
	});

	{
		auto fn = c.function("{} {}::calc{}Before(const EventLabel *lab) const", vt,
				     className, name);
		c.line("[[maybe_unused]] auto &g = *lab->getParent();")
			.line("{} pporf;", vt)
			.line("pporf.updateIdx(lab->getPos());");
		std::for_each(nfa.states_begin(), nfa.states_end(), [&](auto &s) {
			c.line("visited{}{}.clear();", name, s->getId())
				.line("visited{}{}.resize(g.getMaxStamp().get() + 1, "
				      "NodeStatus::unseen);",
				      name, s->getId());
		});
		c.blank();
		std::for_each(nfa.accept_begin(), nfa.accept_end(), [&](auto &acc) -> void {
			c.line("visit{}{}(lab, pporf);", name, acc->getId());
		});
		c.line("return pporf;");
	}
}
