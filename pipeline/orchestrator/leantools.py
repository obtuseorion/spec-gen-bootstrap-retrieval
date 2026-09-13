"""Thin subprocess wrapper around `lake exe leantools`.

Every command returns exactly one JSON object on stdout; a failure is a JSON
object with an `error` key (non-zero exit). Nothing else on stdout is ever
parsed, and human-readable Lean output is never interpreted here.
"""

from __future__ import annotations

import json
import subprocess
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from orchestrator.config import Config


class LeanToolsError(RuntimeError):
    pass


@dataclass
class LeanTools:
    config: Config

    def _argv(self, command: str, kwargs: dict[str, Any]) -> list[str]:
        argv = ["lake", "exe", "leantools", command,
                "--project", str(self.config.project), "--namespace", self.config.namespace]
        for k, v in kwargs.items():
            if v is None:
                continue
            argv += [f"--{k.replace('_', '-')}", str(v)]
        return argv

    def run(self, command: str, limit: float | None = None, **kwargs: Any) -> dict[str, Any]:
        """Run a command; returns the parsed JSON (which may carry `error`). `limit` is the subprocess timeout."""
        timeout = limit or self.config.budgets.get("leantools_timeout_s", 600)
        argv = self._argv(command, kwargs)
        t0 = time.monotonic()
        try:
            proc = subprocess.run(argv, cwd=self.config.lean_tools, capture_output=True, text=True, timeout=timeout)
        except subprocess.TimeoutExpired:
            return {"error": f"leantools {command} timed out after {timeout}s", "elapsed_s": time.monotonic() - t0}
        stdout = proc.stdout.strip()
        # the last line is the JSON object (lake may print build noise before it)
        line = stdout.splitlines()[-1] if stdout else ""
        try:
            out = json.loads(line)
        except json.JSONDecodeError:
            out = {"error": f"leantools {command} produced no JSON (exit {proc.returncode}): {proc.stderr[-2000:]}"}
        if not isinstance(out, dict):
            out = {"error": f"leantools {command} produced a non-object JSON value"}
        out["elapsed_s"] = round(time.monotonic() - t0, 3)
        return out

    # convenience wrappers -------------------------------------------------
    def graph(self) -> dict[str, Any]:
        return self.run("graph", limit=1800)

    def specform(self, unit: str, members: list[str], spec: Path) -> dict[str, Any]:
        return self.run("specform", unit=unit, members=",".join(members), spec=spec)

    def gate(self, unit: str, members: list[str], spec: Path, runs: int, max_mutants: int, timeout_s: int, seed: int = 0) -> dict[str, Any]:
        budget = timeout_s * 4 + 600
        return self.run("gate", limit=budget, unit=unit, members=",".join(members), spec=spec, runs=runs,
                        max_mutants=max_mutants, timeout=timeout_s, seed=seed)

    def proofcheck(self, unit: str, members: list[str], spec: Path, proof: Path, callee_specs: Path) -> dict[str, Any]:
        return self.run("proofcheck", unit=unit, members=",".join(members), spec=spec, proof=proof, callee_specs=callee_specs)

    def embedtext(self, unit: str, members: list[str]) -> dict[str, Any]:
        return self.run("embedtext", unit=unit, members=",".join(members))
