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

#include "NFAAssertions.hpp"
#include "NFATestUtils.hpp"

#include "NFA.hpp"
#include "Relation.hpp"
#include "Saturation.hpp"
#include "TransLabel.hpp"

#include <gtest/gtest.h>

static auto po() -> TransLabel { return makeLabel({}, Relation::po); }
static auto rf() -> TransLabel { return makeLabel({}, Relation::rf); }
static auto mo() -> TransLabel { return makeLabel({}, Relation::mo); }

/* po;rf | mo, both words leaving the same starting state */
static auto makeSharedStart() -> NFA
{
	NFA nfa;
	auto *s0 = nfa.createStarting();
	auto *s1 = nfa.createState();
	auto *s2 = nfa.createAccepting();
	NFA::addTransition(s0, NFA::Transition(po(), s1));
	NFA::addTransition(s1, NFA::Transition(rf(), s2));
	NFA::addTransition(s0, NFA::Transition(mo(), s2));
	return nfa;
}

/*
 * The saturation of `po;po <= po`, and of `total po`, which says that po is
 * a strict total order: where the right-hand side reads po, it may read po+,
 * and nothing else
 */
TEST(SaturateTransitive, RepeatsTheRelation)
{
	auto nfa = makeSharedStart();
	saturateTransitive(nfa, Relation::createBuiltin(Relation::po));
	ASSERT_TRUE(wellFormed(nfa));
	EXPECT_TRUE(acceptsWord(nfa, Word{po(), rf()}));
	EXPECT_TRUE(acceptsWord(nfa, Word{po(), po(), rf()}));
	EXPECT_TRUE(acceptsWord(nfa, Word{po(), po(), po(), rf()}));
	EXPECT_TRUE(acceptsWord(nfa, Word{mo()}));
}

TEST(SaturateTransitive, DoesNotSkipTheRelation)
{
	/* A strict order relates no event to itself. The saturation of `total`
	 * used to make po optional */
	auto nfa = makeSharedStart();
	saturateTransitive(nfa, Relation::createBuiltin(Relation::po));
	EXPECT_FALSE(acceptsWord(nfa, Word{rf()}));
}

TEST(SaturateTransitive, DoesNotPutTheRelationBeforeOtherSteps)
{
	/* Transitivity gives po;po;rf <= po;rf, but po;mo is in neither po;rf
	 * nor mo. The saturation of `total` used to repeat po through an ε step
	 * back to the starting state, from which mo follows too */
	auto nfa = makeSharedStart();
	saturateTransitive(nfa, Relation::createBuiltin(Relation::po));
	EXPECT_FALSE(acceptsWord(nfa, Word{po(), mo()}));
	EXPECT_FALSE(acceptsWord(nfa, Word{po(), po(), mo()}));
}

using RoleKind = SaturationEvidence::Role::Kind;

TEST(SaturateTransitive, RecordsWhatEachStateStandsFor)
{
	/* po | mo: the accepting state is entered by both */
	NFA nfa;
	auto *s0 = nfa.createStarting();
	auto *s1 = nfa.createAccepting();
	NFA::addTransition(s0, NFA::Transition(po(), s1));
	NFA::addTransition(s0, NFA::Transition(mo(), s1));

	SaturationEvidence ev;
	saturateTransitive(nfa, Relation::createBuiltin(Relation::po), &ev);
	EXPECT_EQ(ev.hypothesis, SaturationEvidence::Hypothesis::Transitive);
	EXPECT_EQ(ev.letter, po());
	ASSERT_EQ(nfa.getNumStates(), 3U);
	ASSERT_EQ(ev.roles.size(), nfa.getNumStates());
	EXPECT_EQ(ev.roles[0].kind, RoleKind::State);
	/* The state the loop is added to is entered by po alone... */
	EXPECT_EQ(ev.roles[1].kind, RoleKind::After);
	EXPECT_EQ(ev.roles[1].state, 1U);
	/* ... and the state split off it takes the mo step, standing for it */
	EXPECT_EQ(ev.roles[2].kind, RoleKind::State);
	EXPECT_EQ(ev.roles[2].state, 1U);
}

TEST(SaturateID, RecordsACopyAtEachState)
{
	auto nfa = makeSharedStart();
	const auto states = nfa.getNumStates();
	SaturationEvidence ev;
	saturateID(nfa, NFA(rf()), &ev);

	/* rf <= id: the word is empty, and each copy goes from a state back to it */
	EXPECT_EQ(ev.hypothesis, SaturationEvidence::Hypothesis::Within);
	EXPECT_TRUE(ev.word.empty());
	EXPECT_EQ(ev.automaton.getNumStates(), 2U);
	ASSERT_EQ(ev.copies.size(), states);
	for (auto g = 0U; g < states; g++) {
		EXPECT_EQ(ev.copies[g].from, g);
		EXPECT_EQ(ev.copies[g].to, g);
		EXPECT_TRUE(ev.copies[g].path.empty());
	}
	/* The copies' states follow the old ones, copy by copy */
	ASSERT_EQ(ev.roles.size(), nfa.getNumStates());
	for (auto m = 0U; m < states; m++)
		EXPECT_EQ(ev.roles[m].kind, RoleKind::State);
	const auto &r = ev.roles[states + (2 * 1) + 1];
	EXPECT_EQ(r.kind, RoleKind::Copy);
	EXPECT_EQ(r.state, 1U);
	EXPECT_EQ(r.copy, 1U);
}
