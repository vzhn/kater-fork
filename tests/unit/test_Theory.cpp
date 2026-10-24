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

#include "Predicate.hpp"
#include "Relation.hpp"
#include "Theory.hpp"
#include "VSet.hpp"

#include <gtest/gtest.h>

using PB = Predicate::BuiltinID;

static auto inverse(Relation r) -> Relation { return r.invert(); }
static auto complement(Predicate p) -> Predicate { return p.complement(); }

/* The domain of r^-1 is the codomain of r: `assume r^-1 <= [R];r^-1;[W]`
 * says that r goes from writes to reads (#45) */
TEST(Theory, DomainsOfAnInverseAreTheRelationsTheOtherWay)
{
	Theory theory;
	auto r = Relation::createUser();
	theory.registerRelation(r, RelationInfo{.name = "r"});
	auto reads = Predicate::createBuiltin(PB::R);
	auto writes = Predicate::createBuiltin(PB::W);

	theory.registerDomain(inverse(r), PredicateSet{reads});
	theory.registerCodomain(inverse(r), PredicateSet{writes});
	EXPECT_EQ(theory.getDomain(r), PredicateSet{writes});
	EXPECT_EQ(theory.getCodomain(r), PredicateSet{reads});
	EXPECT_EQ(theory.getDomain(inverse(r)), PredicateSet{reads});
	EXPECT_EQ(theory.getCodomain(inverse(r)), PredicateSet{writes});

	/* Those of a relation itself are its own */
	auto s = Relation::createUser();
	theory.registerRelation(s, RelationInfo{.name = "s"});
	theory.registerDomain(s, PredicateSet{reads});
	theory.registerCodomain(s, PredicateSet{writes});
	EXPECT_EQ(theory.getDomain(s), PredicateSet{reads});
	EXPECT_EQ(theory.getCodomain(s), PredicateSet{writes});
}

/* A sub-predicate of a member of a disjoint set is disjoint from the other
 * members, whichever of the two the theory learns first (#46) */
TEST(Theory, SubPredicatesOfDisjointOnesAreDisjoint)
{
	/* A <= B <= C, and C # D */
	auto predA = Predicate::createUser();
	auto predB = Predicate::createUser();
	auto predC = Predicate::createUser();
	auto predD = Predicate::createUser();
	auto registerSubsets = [&](Theory &theory) -> void {
		theory.registerSubsetPair(predA.getID(), predB.getID());
		theory.registerSubsetPair(predB.getID(), predC.getID());
	};

	Theory subsetsFirst;
	registerSubsets(subsetsFirst);
	subsetsFirst.registerDisjointPreds({predC.getID(), predD.getID()});

	Theory disjointFirst;
	disjointFirst.registerDisjointPreds({predC.getID(), predD.getID()});
	registerSubsets(disjointFirst);

	for (const auto *theory : {&subsetsFirst, &disjointFirst}) {
		for (const auto &p : {predA, predB, predC})
			EXPECT_FALSE(theory->composes(PredicateSet{p}, PredicateSet{predD}));
		EXPECT_TRUE(theory->composes(PredicateSet{predA}, PredicateSet{predB}));
	}
	EXPECT_EQ(subsetsFirst.disjointPredicateSets(), disjointFirst.disjointPredicateSets());
}

/* A super-predicate of a member of a disjoint set need not be disjoint from
 * the other members: registerSubsetPair used to make it so (#46) */
TEST(Theory, SuperPredicatesOfDisjointOnesNeedNotBe)
{
	/* A <= B, and A # C */
	Theory theory;
	auto predA = Predicate::createUser();
	auto predB = Predicate::createUser();
	auto predC = Predicate::createUser();
	theory.registerDisjointPreds({predA.getID(), predC.getID()});
	theory.registerSubsetPair(predA.getID(), predB.getID());

	EXPECT_FALSE(theory.composes(PredicateSet{predA}, PredicateSet{predC}));
	EXPECT_TRUE(theory.composes(PredicateSet{predB}, PredicateSet{predC}));
	auto onlyAC = VSet<VSet<Predicate::ID>>{VSet<Predicate::ID>{predA.getID(), predC.getID()}};
	EXPECT_EQ(theory.disjointPredicateSets(), onlyAC);
}

/* [A;B;C] = 0 makes A, B and C invalid together, and says nothing of ~A, B
 * and C: composes used to compare the predicates by id alone (#46) */
TEST(Theory, InvalidCombinationsAreOfPlainPredicates)
{
	Theory theory;
	auto predA = Predicate::createUser();
	auto predB = Predicate::createUser();
	auto predC = Predicate::createUser();
	auto predD = Predicate::createUser();
	theory.registerInvalidPreds({predA.getID(), predB.getID(), predC.getID()});

	EXPECT_FALSE(theory.composes(PredicateSet{predA}, PredicateSet{predB, predC}));
	EXPECT_FALSE(theory.composes(PredicateSet{predB, predC}, PredicateSet{predA}));
	EXPECT_TRUE(theory.composes(PredicateSet{complement(predA)}, PredicateSet{predB, predC}));
	EXPECT_TRUE(theory.composes(PredicateSet{predB, predC}, PredicateSet{complement(predA)}));
	EXPECT_TRUE(theory.composes(PredicateSet{complement(predA), predB},
				    PredicateSet{complement(predC)}));

	/* A negated predicate more only narrows an invalid combination down */
	EXPECT_FALSE(theory.composes(PredicateSet{predA, complement(predD)},
				     PredicateSet{predB, predC}));
}
