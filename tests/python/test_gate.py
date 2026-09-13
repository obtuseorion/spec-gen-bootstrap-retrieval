"""Task 5 — `leantools gate` on hand-written specs (tests/lean/gate)."""

from __future__ import annotations

import json
import time
from pathlib import Path

import pytest

from conftest import REPO, run_leantools

CASES = json.loads((REPO / "tests/lean/gate/cases.json").read_text())


def gate(config: dict, name: str) -> dict:
    case = CASES[name]
    kwargs = {"unit": case["unit"], "spec": REPO / "tests/lean/gate" / f"{name}.lean",
              "runs": case["runs"], "timeout": case["timeout"], "max_mutants": 60, "seed": 1}
    if "members" in case:
        kwargs["members"] = case["members"]
    out = run_leantools(config, "gate", **kwargs)
    assert "error" not in out, json.dumps(out, indent=1)[:3000]
    return out


def kill_rate(out: dict) -> float:
    dist = [m for m in out["mutants"] if m["distinguishable"]]
    return sum(m["killed"] for m in dist) / len(dist) if dist else float("nan")


def test_a_true_postcondition_kills_nothing(config: dict, project_root: Path) -> None:
    out = gate(config, "a_true_post")
    assert out["spec_ok_on_original"], out
    dist = [m for m in out["mutants"] if m["distinguishable"]]
    assert dist, out["mutants"]
    assert kill_rate(out) == 0.0, [(m["op"], m["before"], m["after"], m["killed"]) for m in dist]


def test_b_exact_spec_kills_everything(config: dict, project_root: Path) -> None:
    out = gate(config, "b_exact")
    assert out["spec_ok_on_original"], out
    dist = [m for m in out["mutants"] if m["distinguishable"]]
    assert dist, out["mutants"]
    assert kill_rate(out) == 1.0, [(m["op"], m["before"], m["after"], m["killed"], m["witness"]) for m in dist]
    assert out["precond_density"] == 1.0


def test_c_precondition_density(config: dict, project_root: Path) -> None:
    out = gate(config, "c_density")
    assert out["spec_ok_on_original"], out
    assert out["precond_density"] < 0.2, out["precond_density"]
    assert out["effective_runs"] >= 1


def test_de_out_of_precondition_mutant_and_timeout(config: dict, project_root: Path) -> None:
    t0 = time.monotonic()
    out = gate(config, "de_loop")
    elapsed = time.monotonic() - t0
    timeout = CASES["de_loop"]["timeout"]
    assert out["spec_ok_on_original"], out
    # (d) `32 → 33` only changes behaviour at dst_coeff = 33, outside `h : dst_coeff ≤ 32`
    outside = [m for m in out["mutants"] if m["op"] == "bound_shift" and m["before"] == "32" and m["after"] == "33"]
    assert outside, [(m["op"], m["before"], m["after"]) for m in out["mutants"]]
    assert all(not m["distinguishable"] for m in outside), outside
    # (e) removing the loop exit makes the mutant diverge on in-precondition inputs
    timeouts = [m for m in out["mutants"] if m["timeout"]]
    assert timeouts, [(m["op"], m["before"], m["after"], m["distinguishable"]) for m in out["mutants"]]
    assert all(m["distinguishable"] and not m["killed"] for m in timeouts), timeouts
    # the whole run (environment load + elaboration + evaluation) stays within 2 × timeout plus fixed overhead
    assert elapsed < 2 * timeout + 30, elapsed
