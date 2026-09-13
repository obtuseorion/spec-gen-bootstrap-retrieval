"""Task 2 — `leantools specform` on hand-written specs (tests/lean/specform)."""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from conftest import REPO, run_leantools

CASES = json.loads((REPO / "tests/lean/specform/cases.json").read_text())


@pytest.mark.parametrize("name", sorted(CASES))
def test_specform_case(config: dict, project_root: Path, name: str) -> None:
    case = CASES[name]
    spec = REPO / "tests/lean/specform" / f"{name}.lean"
    out = run_leantools(config, "specform", unit=case["unit"], spec=spec)
    for key, expected in case["expect"].items():
        assert out.get(key) == expected, f"{name}: {key}: expected {expected!r}, got {out.get(key)!r}\nfull: {json.dumps(out, indent=1)}"
    if out.get("shape_ok"):
        assert out["spec_prop_reelab_ok"], f"{name}: spec_prop does not re-elaborate:\n{out['spec_prop']}"
