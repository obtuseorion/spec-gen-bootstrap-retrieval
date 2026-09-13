"""Task 3 — PBT generators: tests/lean/sample/SampleTest.lean samples 1000 values per type."""

from __future__ import annotations

import subprocess
from pathlib import Path

from conftest import REPO


def test_sample_distributions(config: dict, project_root: Path) -> None:
    lean_tools = REPO / config["paths"]["lean_tools"]
    test_file = REPO / "tests/lean/sample/SampleTest.lean"
    proc = subprocess.run(["lake", "env", "lean", str(test_file)], cwd=lean_tools,
                          capture_output=True, text=True, timeout=config["budgets"]["leantools_timeout_s"])
    errors = [l for l in proc.stdout.splitlines() if "error" in l and "SampleTest" in l]
    assert proc.returncode == 0 and not errors, f"stdout:\n{proc.stdout[-4000:]}\nstderr:\n{proc.stderr[-2000:]}"
    assert "SAMPLE_TEST_OK" in proc.stdout, proc.stdout[-4000:]
