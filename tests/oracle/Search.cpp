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

#include "Search.hpp"

#include <cassert>
#include <sstream>

namespace oracle {

/* Turns off the incidental unknowns the counterexample does not need. Leaves
 * SOLVER satisfiable, with the scopes it pushed */
static void minimize(z3::solver &solver, const Graph &g)
{
	for (const auto &v : g.incidentals()) {
		solver.push();
		solver.add(!v);
		if (solver.check() != z3::sat)
			solver.pop();
	}
	[[maybe_unused]] auto res = solver.check();
	assert(res == z3::sat);
}

auto search(const KatModule &module, const Query &hypotheses, const Query &violation,
	    const SearchOptions &opts) -> Search
{
	for (auto n = opts.minEvents; n <= opts.maxEvents; n++) {
		z3::context ctx;
		Graph g(ctx, n);
		Semantics sem(g, module);

		z3::solver solver(ctx);
		z3::params params(ctx);
		params.set("timeout", opts.timeoutMs);
		solver.set(params);

		try {
			auto h = hypotheses(g, sem);
			auto v = violation(g, sem);
			solver.add(g.axioms());
			solver.add(h.expr());
			solver.add(v.expr());
		} catch (const Unsupported &u) {
			return {.outcome = Search::Outcome::Unsupported,
				.events = n,
				.detail = u.what()};
		}

		switch (solver.check()) {
		case z3::unsat:
			continue;
		case z3::sat: {
			minimize(solver, g);
			std::ostringstream os;
			g.print(os, solver.get_model(), module.getTheory());
			return {.outcome = Search::Outcome::Counterexample,
				.events = n,
				.detail = os.str()};
		}
		case z3::unknown:
			return {.outcome = Search::Outcome::Unknown,
				.events = n,
				.detail = solver.reason_unknown()};
		}
	}
	return {.outcome = Search::Outcome::NoCounterexample,
		.events = opts.maxEvents,
		.detail = {}};
}

} // namespace oracle
