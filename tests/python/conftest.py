"""Shared fixtures: repo root, config, and a `leantools` subprocess helper."""

from __future__ import annotations

import json
import subprocess
import tomllib
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[2]


@pytest.fixture(scope="session")
def repo_root() -> Path:
    return REPO


@pytest.fixture(scope="session")
def config() -> dict:
    with open(REPO / "pipeline/config.toml", "rb") as f:
        return tomllib.load(f)


@pytest.fixture(scope="session")
def project_root(config: dict) -> Path:
    root = REPO / config["paths"]["project"]
    if not (root / "lakefile.toml").is_file():
        pytest.skip(f"emitted project not found at {root}; run scripts/check.sh corpus")
    return root


def run_leantools(config: dict, command: str, **kwargs: str) -> dict:
    """Invoke `lake exe leantools <command> --project … [--k v …]` and parse its JSON."""
    lean_tools = REPO / config["paths"]["lean_tools"]
    project = REPO / config["paths"]["project"]
    argv = ["lake", "exe", "leantools", command, "--project", str(project),
            "--namespace", config["paths"]["project_namespace"]]
    for k, v in kwargs.items():
        argv += [f"--{k.replace('_', '-')}", str(v)]
    proc = subprocess.run(argv, cwd=lean_tools, capture_output=True, text=True,
                          timeout=config["budgets"]["leantools_timeout_s"])
    try:
        return json.loads(proc.stdout)
    except json.JSONDecodeError as e:  # pragma: no cover - diagnostic path
        raise AssertionError(f"leantools {command} produced no JSON (exit {proc.returncode}):\n"
                             f"stdout: {proc.stdout[:2000]}\nstderr: {proc.stderr[:2000]}") from e
