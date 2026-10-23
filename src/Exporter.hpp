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

#ifndef KATER_EXPORTER_HPP
#define KATER_EXPORTER_HPP

#include "Checker.hpp"
#include "Config.hpp"
#include "KatModule.hpp"

/*
 * Code export: turns a module's export statements into a consistency
 * checker for a model checker.
 *
 * Export first proves, through the Checker, the side conditions that the
 * generated code relies on (the module's relations are closed the way the
 * incremental calculations assume), then rewrites the module for faster
 * generated code, and finally prints it.
 *
 * The exporter is downstream of the decision procedure: it may ask the
 * Checker questions, but the Checker never depends on it.
 */
class Exporter {

public:
	Exporter() = delete;
	Exporter(KatModule &mod, Checker &checker, const Config &conf)
		: module(&mod), checker(&checker), config(&conf)
	{
	}

	auto exportCode() -> bool;

private:
	[[nodiscard]] auto getModule() const -> const KatModule & { return *module; }
	auto getModule() -> KatModule & { return *module; }
	[[nodiscard]] auto getChecker() const -> Checker & { return *checker; }
	[[nodiscard]] auto getConf() const -> const Config & { return *config; }
	[[nodiscard]] auto getTheory() const -> const Theory & { return getModule().getTheory(); }

	void optimizeModuleForExport();
	void makeViewsIncremental();
	auto checkSavedRelsExportRequirements(const RegExp &pporf) -> bool;
	auto checkExportRequirements() -> bool;

	KatModule *module;
	Checker *checker;
	const Config *config;
};

#endif /* KATER_EXPORTER_HPP */
