"""Drive `leantools proofcheck` and classify the result (IMPLEMENTATION.md §3.5, Task 9)."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Any

from orchestrator.leantools import LeanTools
from orchestrator.units import Unit


@dataclass
class ProofOutcome:
    accepted: bool               # kernel ∧ axioms ∧ static
    modular: bool                # accepted ∧ opaque_ok
    result: dict[str, Any]
    blame_unit: str | None       # callee unit id when the failure is attributed to a callee spec
    intra_unit_member: str | None  # member of this unit the failure mentions (loop / SCC obligation)

    @property
    def summary(self) -> dict[str, Any]:
        r = self.result
        return {"accepted": self.accepted, "modular": self.modular, "kernel_ok": r.get("kernel_ok"),
                "axioms_ok": r.get("axioms_ok"), "static_ok": r.get("static_ok"), "opaque_ok": r.get("opaque_ok"),
                "static_violations": r.get("static_violations", []), "blame": self.blame_unit,
                "intra_unit_member": self.intra_unit_member, "error": (r.get("error") or "")[:2000],
                "elapsed_s": r.get("elapsed_s")}


def _mentions(text: str, name: str) -> bool:
    short = name.split(".")[-1]
    return name in text or f" {short} " in text or f" {short}\n" in text or f"{short} " in text


def run_proofcheck(tools: LeanTools, unit: Unit, members: list[str], specs_dir: Path, proofs_dir: Path,
                   callee_specs_dir: Path, member_to_unit: dict[str, str], target: str) -> ProofOutcome:
    r = tools.proofcheck(unit.id, members, specs_dir, proofs_dir, callee_specs_dir)
    if "error" in r and "kernel_ok" not in r:
        return ProofOutcome(False, False, r, None, None)
    accepted = bool(r.get("kernel_ok") and r.get("axioms_ok") and r.get("static_ok"))
    modular = accepted and r.get("opaque_ok") is True
    blame_unit = None
    intra = None
    if not r.get("kernel_ok"):
        err = r.get("error") or ""
        # a helper of this unit (other than the target) mentioned in the failure ⇒ intra-unit obligation
        for m in unit.all_members:
            if m != target and _mentions(err, m):
                intra = m
                break
        b = r.get("blame")
        if b and intra is None:
            bu = member_to_unit.get(b, b)
            if bu != unit.id:
                blame_unit = bu
    return ProofOutcome(accepted, modular, r, blame_unit, intra)
