"""Drive `leantools specform` + `leantools gate` and apply the gate rule (IMPLEMENTATION.md §1, §3.4).

Gate passes iff spec_ok_on_original ∧ precond_density ≥ δ ∧ every distinguishable mutant is killed.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from orchestrator.config import Config
from orchestrator.leantools import LeanTools
from orchestrator.units import Unit


@dataclass
class GateOutcome:
    passed: bool
    reason: str                      # "pass" | "spec_false" | "density" | "survivors" | "error" | "no_generator"
    specform: dict[str, Any]
    gate: dict[str, Any] | None = None
    survivors: list[dict[str, Any]] = field(default_factory=list)

    @property
    def summary(self) -> dict[str, Any]:
        g = self.gate or {}
        ms = g.get("mutants", [])
        dist = [m for m in ms if m.get("distinguishable")]
        return {
            "passed": self.passed, "reason": self.reason,
            "spec_ok_on_original": g.get("spec_ok_on_original"), "precond_density": g.get("precond_density"),
            "effective_runs": g.get("effective_runs"), "mutants_total": len(ms), "mutants_distinguishable": len(dist),
            "mutants_killed": sum(1 for m in dist if m.get("killed")), "mutants_timeout": sum(1 for m in ms if m.get("timeout")),
            "output_comparable": g.get("output_comparable"), "elapsed_s": g.get("elapsed_s"),
            "specform_elapsed_s": self.specform.get("elapsed_s"),
        }


def specform_ok(sf: dict[str, Any]) -> bool:
    return bool(sf.get("shape_ok") and sf.get("attr_ok") and sf.get("vocab_ok") and sf.get("decidable_ok")) and not sf.get("error")


def run_gate(config: Config, tools: LeanTools, unit: Unit, members: list[str], spec_file: Path, seed: int = 0) -> GateOutcome:
    sf = tools.specform(unit.id, members, spec_file)
    if not specform_ok(sf):
        return GateOutcome(False, "specform", sf)
    b = config.budgets
    g = tools.gate(unit.id, members, spec_file, runs=int(b["pbt_runs"]), max_mutants=int(b["max_mutants"]),
                   timeout_s=int(b["eval_timeout_s"]), seed=seed)
    if "error" in g:
        reason = "no_generator" if str(g["error"]).startswith("no generator") else "error"
        return GateOutcome(False, reason, sf, g)
    if not g.get("spec_ok_on_original"):
        return GateOutcome(False, "spec_false", sf, g)
    floor = float(config.gate["precond_density_floor"])
    if float(g.get("precond_density", 0.0)) < floor:
        return GateOutcome(False, "density", sf, g)
    survivors = [m for m in g.get("mutants", []) if m.get("distinguishable") and not m.get("killed")]
    if survivors:
        return GateOutcome(False, "survivors", sf, g, survivors)
    return GateOutcome(True, "pass", sf, g)
