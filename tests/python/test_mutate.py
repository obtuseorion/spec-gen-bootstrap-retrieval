"""Task 4 — `leantools mutate`: every emitted mutant elaborates and builds in a scratch module."""

from __future__ import annotations

import subprocess
from pathlib import Path

import pytest

from conftest import REPO, run_leantools

# Five hand-picked units: arithmetic, loop with if, slice loops, match inside a loop, bool compare.
UNITS = [
    "Corpus.demo.mul2_add1",
    "Corpus.loops_adts.array_shared_borrow_loop1",
    "Corpus.arrays.sum",
    "Corpus.issue_789_loop_ctx_match.the_loop",
    "Corpus.arrays.zero_slice",
]


@pytest.mark.parametrize("unit", UNITS)
def test_mutants_elaborate_and_build(config: dict, project_root: Path, unit: str, tmp_path: Path) -> None:
    out = run_leantools(config, "mutate", unit=unit, max_mutants=40, seed=1)
    assert "error" not in out, out
    mutants = out["mutants"]
    assert mutants, f"{unit}: no mutants (candidates={out['candidates']}, dropped={out['dropped'][:5]})"
    ops = {m["op"] for m in mutants}
    assert len(ops) >= 3, f"{unit}: only ops {ops}"
    ids = [m["id"] for m in mutants]
    assert len(ids) == len(set(ids))
    # Assemble a scratch module with every mutant and build it with lake's environment.
    scratch = tmp_path / "MutantsScratch.lean"
    text = "import Corpus\nimport LeanTools.Instances\nimport LeanTools.Mut\n" + out["header"]
    for m in mutants:
        text += f"\n-- {m['id']} {m['op']} @ {m['site']}: {m['before']!r} -> {m['after']!r}\n" + m["source"] + "\n"
    scratch.write_text(text)
    lean_tools = REPO / config["paths"]["lean_tools"]
    proc = subprocess.run(["lake", "env", "lean", str(scratch)], cwd=lean_tools, capture_output=True,
                          text=True, timeout=config["budgets"]["leantools_timeout_s"])
    errors = [l for l in proc.stdout.splitlines() if "MutantsScratch" in l and "error" in l]
    assert proc.returncode == 0 and not errors, f"{unit}: scratch module failed:\n" + "\n".join(errors[:10]) + proc.stderr[-1500:]
    # Every mutant renames every member consistently and differs from the original.
    for m in mutants:
        assert m["source"] != out["original"]
        for orig, new in m["names"]:
            assert new.endswith("_mut" + m["id"][1:])
