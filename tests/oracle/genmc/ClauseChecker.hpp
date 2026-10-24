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

#ifndef KATER_ORACLE_CLAUSE_CHECKER_HPP
#define KATER_ORACLE_CLAUSE_CHECKER_HPP

#include <vector>

class EventLabel;

/*
 * The verdicts of a checker's error and warning clauses on an event, in the
 * order of the exports: what checkErrors() and checkWarnings() combine. The
 * build derives a class of each exported checker that gives them
 * (Clauses.cmake), as they are protected members of their own names.
 */
class ClauseChecker {

public:
	ClauseChecker() = default;
	ClauseChecker(const ClauseChecker &) = delete;
	ClauseChecker(ClauseChecker &&) = delete;
	auto operator=(const ClauseChecker &) -> ClauseChecker & = delete;
	auto operator=(ClauseChecker &&) -> ClauseChecker & = delete;
	virtual ~ClauseChecker() = default;

	[[nodiscard]] virtual auto clauses(const EventLabel *lab) const -> std::vector<bool> = 0;
};

#endif /* KATER_ORACLE_CLAUSE_CHECKER_HPP */
