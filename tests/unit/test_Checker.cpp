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
#include "TransLabel.hpp"
#include "VSet.hpp"

#include <gtest/gtest.h>

#include <algorithm>
#include <vector>

/* The case split of the inclusion check, from Checker.cpp */
auto maybeSplitToComplements(const TransLabel &label, const VSet<Predicate> &negated,
			     const Theory &theory) -> std::vector<TransLabel>;

using PB = Predicate::BuiltinID;
using RB = Relation::BuiltinID;

/* Splitting a letter on a negated predicate gives both cases, so that
 * together they cover the letter */
TEST(MaybeSplitToComplements, GivesBothCases)
{
	Theory theory;
	auto notF = Predicate::createBuiltin(PB::F).complement();
	auto f = Predicate::createBuiltin(PB::F);

	for (const auto &label :
	     {TransLabel(std::nullopt), TransLabel(Relation::createBuiltin(RB::po))}) {
		auto cases = maybeSplitToComplements(label, VSet<Predicate>{notF}, theory);
		auto withNotF = label;
		withNotF.merge(TransLabel(std::nullopt, {notF}));
		auto withF = label;
		withF.merge(TransLabel(std::nullopt, {f}));

		EXPECT_EQ(cases.size(), 2U);
		EXPECT_TRUE(std::ranges::find(cases, withNotF) != cases.end());
		EXPECT_TRUE(std::ranges::find(cases, withF) != cases.end());
	}
}

/* Without negated predicates there is nothing to split */
TEST(MaybeSplitToComplements, KeepsTheLetterOtherwise)
{
	Theory theory;
	auto label = TransLabel(Relation::createBuiltin(RB::rf));
	auto cases = maybeSplitToComplements(label, {}, theory);
	ASSERT_EQ(cases.size(), 1U);
	EXPECT_EQ(cases[0], label);
}
