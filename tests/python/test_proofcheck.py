"""Task 6 — `leantools proofcheck` on hand-written proofs (tests/lean/proofcheck)."""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from conftest import REPO, run_leantools

DIR = REPO / "tests/lean/proofcheck"
CASES = json.loads((DIR / "cases.json").read_text())


@pytest.mark.parametrize("name", sorted(CASES))
def test_proofcheck_case(config: dict, project_root: Path, name: str) -> None:
    case = CASES[name]
    out = run_leantools(config, "proofcheck", unit=case["unit"], spec=DIR / f"{name}.spec.lean",
                        proof=DIR / f"{name}.proof.lean", callee_specs=DIR / case["callee_specs"])
    for key, expected in case["expect"].items():
        assert out.get(key) == expected, f"{name}: {key}: expected {expected!r}, got {out.get(key)!r}\nfull: {json.dumps(out, indent=1)[:3000]}"
    if "static_violation_prefix" in case:
        assert any(v.startswith(case["static_violation_prefix"]) for v in out["static_violations"]), out["static_violations"]
    if out.get("kernel_ok"):
        assert out["theorems"], out
