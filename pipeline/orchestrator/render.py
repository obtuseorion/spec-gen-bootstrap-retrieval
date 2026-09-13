"""Prompt rendering (IMPLEMENTATION.md Task 8).

Templates live in `pipeline/prompts/spec.md` and `proof.md` with `{{name}}`
placeholders and `{{#name}} … {{/name}}` sections that are dropped entirely
when `name` is empty — so a zero-example prompt has no examples header at all.

Examples are never truncated: an example over the token cap is dropped and the
next candidate is tried. Callee specs precede examples and are never dropped.
"""

from __future__ import annotations

import difflib
import math
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from orchestrator.corpus import Record
from orchestrator.units import Unit

_SECTION = re.compile(r"\{\{#(\w+)\}\}(.*?)\{\{/\1\}\}", re.DOTALL)
_VAR = re.compile(r"\{\{(\w+)\}\}")


def approx_tokens(text: str, chars_per_token: float = 3.5) -> int:
    return math.ceil(len(text) / chars_per_token)


def render_template(template: str, ctx: dict[str, Any]) -> str:
    def section(m: re.Match[str]) -> str:
        name, body = m.group(1), m.group(2)
        return body if ctx.get(name) else ""

    text = _SECTION.sub(section, template)
    text = _VAR.sub(lambda m: str(ctx.get(m.group(1), "")), text)
    # collapse runs of blank lines left by dropped sections
    return re.sub(r"\n{3,}", "\n\n", text).strip() + "\n"


@dataclass
class Renderer:
    prompts_dir: Path
    example_token_cap: int = 1500
    chars_per_token: float = 3.5
    namespace: str = "Corpus"

    def _template(self, name: str) -> str:
        return (self.prompts_dir / f"{name}.md").read_text()

    # ---- pieces -------------------------------------------------------------
    @staticmethod
    def _lean(text: str) -> str:
        return "```lean\n" + text.strip() + "\n```"

    def _example(self, rec: Record, stage: str) -> str:
        parts = [self._lean(rec.unit["source"])]
        specs = "\n\n".join(rec.member_specs.values()) if rec.member_specs else rec.spec_stmt
        parts.append(self._lean(specs))
        if stage == "proof":
            proofs = rec.member_proofs or {rec.id: rec.proof}
            proof_text = "\n\n".join(f"-- proof of {m}\n{p.strip()}" for m, p in proofs.items())
            parts.append(self._lean(proof_text))
        return "\n\n".join(parts)

    def select_examples(self, candidates: list[Record], stage: str, k: int = 2) -> tuple[list[Record], list[str]]:
        """Render up to k examples under the token cap; oversize ones are dropped, never truncated."""
        chosen: list[Record] = []
        rendered: list[str] = []
        for rec in candidates:
            if len(chosen) >= k:
                break
            text = self._example(rec, stage)
            if approx_tokens(text, self.chars_per_token) > self.example_token_cap:
                continue
            chosen.append(rec)
            rendered.append(text)
        return chosen, rendered

    @staticmethod
    def _examples_block(rendered: list[str]) -> str:
        return "\n\n".join(f"### Example {i + 1}\n\n{t}" for i, t in enumerate(rendered))

    @staticmethod
    def _callee_block(callee_specs: dict[str, str]) -> str:
        if not callee_specs:
            return "(this definition calls no other function of the crate)"
        return "\n\n".join(f"```lean\n{s.strip()}\n```" for _, s in sorted(callee_specs.items()))

    @staticmethod
    def _other_specs_block(other_specs: dict[str, str]) -> str:
        return "\n\n".join(f"```lean\n{s.strip()}\n```" for _, s in other_specs.items())

    # ---- prompts ------------------------------------------------------------
    def render_spec_prompt(self, unit: Unit, target: str, callee_specs: dict[str, str], examples: list[Record],
                           other_specs: dict[str, str] | None = None, feedback: str = "") -> tuple[str, list[Record]]:
        chosen, rendered = self.select_examples(examples, "spec")
        ctx = {
            "namespace": self.namespace, "unit_id": unit.id, "target": target, "source": unit.source.strip(),
            "callee_specs": self._callee_block(callee_specs),
            "examples": self._examples_block(rendered) if rendered else "",
            "other_specs": self._other_specs_block(other_specs) if other_specs else "",
            "feedback": feedback.strip(),
        }
        return render_template(self._template("spec"), ctx), chosen

    def render_proof_prompt(self, unit: Unit, target: str, spec_stmt: str, callee_specs: dict[str, str],
                            examples: list[Record], other_specs: dict[str, str] | None = None,
                            feedback: str = "") -> tuple[str, list[Record]]:
        chosen, rendered = self.select_examples(examples, "proof")
        ctx = {
            "namespace": self.namespace, "unit_id": unit.id, "target": target, "source": unit.source.strip(),
            "spec_stmt": spec_stmt.strip(),
            "callee_specs": self._callee_block(callee_specs),
            "examples": self._examples_block(rendered) if rendered else "",
            "other_specs": self._other_specs_block(other_specs) if other_specs else "",
            "feedback": feedback.strip(),
        }
        return render_template(self._template("proof"), ctx), chosen

    # ---- feedback -----------------------------------------------------------
    @staticmethod
    def specform_feedback(sf: dict[str, Any]) -> str:
        lines = ["The previous specification was rejected before testing:"]
        if sf.get("error"):
            lines.append("Lean error:\n```\n" + sf["error"].strip() + "\n```")
        if sf.get("shape_ok") is False:
            lines.append(f"- wrong shape: {sf.get('shape_error', '')}")
        if sf.get("attr_ok") is False:
            lines.append("- the theorem must carry the `@[step]` attribute")
        if sf.get("vocab_ok") is False:
            lines.append("- vocabulary violations: " + ", ".join(sf.get("vocab_violations", [])) +
                         " (only Aeneas.Std, Lean core and Mathlib constants may appear; no other crate function; no extra declarations)")
        if sf.get("decidable_ok") is False:
            lines.append("- not decidable (cannot be tested): " + "; ".join(sf.get("undecidable", [])))
        return "\n".join(lines)

    @staticmethod
    def gate_feedback(gate: dict[str, Any], unit_source: str, density_floor: float, max_mutants: int = 5) -> str:
        lines = []
        if not gate.get("spec_ok_on_original", False):
            lines.append("The specification is FALSE for the original definition on this input:")
            lines.append(f"- input: `{gate.get('original_witness')}`")
            if gate.get("original_timeout"):
                lines.append("- the definition did not terminate within the time limit on this input; strengthen the precondition")
            else:
                lines.append(f"- observed result: `{gate.get('original_observed')}`")
        dens = gate.get("precond_density", 0.0)
        if dens < density_floor:
            lines.append(f"The precondition is too restrictive: only {dens:.0%} of sampled inputs satisfy it "
                         f"(at least {density_floor:.0%} required). Weaken the hypotheses.")
        survivors = [m for m in gate.get("mutants", []) if m.get("distinguishable") and not m.get("killed")]
        if survivors:
            lines.append(f"The specification is too weak: {len(survivors)} mutant(s) of the definition behave differently "
                         "from the original yet still satisfy it. Strengthen the postcondition so that each is rejected:")
            for m in survivors[:max_mutants]:
                lines.append(f"\n### Surviving mutant ({m['op']}) at {m.get('site', '?')}: `{m['before']}` → `{m['after']}`")
                lines.append("```diff\n" + Renderer.unified_diff(unit_source, m) + "```")
                lines.append(f"- distinguishing input: `{m.get('witness')}`")
                lines.append(f"- mutant output: `{m.get('observed')}`  (original: `{m.get('expected')}`)")
                if m.get("timeout"):
                    lines.append("- the mutant did not terminate on this input")
        return "\n".join(lines) if lines else "The gate failed for an unrecorded reason; produce a stronger specification."

    @staticmethod
    def unified_diff(unit_source: str, mutant: dict[str, Any]) -> str:
        """Unified diff of the unit source against the mutant (renamed `_mutN` names undone)."""
        src = mutant.get("source", "")
        for orig, new in mutant.get("names", []):
            src = src.replace(new.split(".")[-1], orig.split(".")[-1])
        a = unit_source.strip().splitlines()
        b = src.strip().splitlines()
        # source lines carry doc comments identically; keep the diff focused
        diff = list(difflib.unified_diff(a, b, "original", "mutant", n=2, lineterm=""))
        if len(diff) > 60:
            diff = diff[:60] + ["... (diff truncated)"]
        return "\n".join(diff) + "\n" if diff else f"- {mutant['before']}\n+ {mutant['after']}\n"

    @staticmethod
    def proof_feedback(pc: dict[str, Any]) -> str:
        lines = []
        if pc.get("error"):
            lines.append("The proof failed. Lean reported:\n```\n" + pc["error"].strip() + "\n```")
        if pc.get("kernel_ok") and not pc.get("axioms_ok", True):
            lines.append("The proof uses forbidden axioms: " + ", ".join(pc.get("axioms", [])) +
                         ". Only propext, Classical.choice and Quot.sound are allowed (no native_decide, no sorry).")
        if pc.get("kernel_ok") and not pc.get("static_ok", True):
            lines.append("The proof unfolds these callees: " + ", ".join(pc.get("static_violations", [])) +
                         ". Do not unfold these; use their `step` lemmas.")
        if pc.get("kernel_ok") and pc.get("static_ok") and pc.get("opaque_ok") is False:
            lines.append("The proof depends on the definition of a callee (it fails when callees are opaque). "
                         "Use only the callees' `step` lemmas:\n```\n" + pc.get("opaque_error", "").strip() + "\n```")
        return "\n".join(lines) if lines else "The proof was rejected; try a different approach using `step`."
