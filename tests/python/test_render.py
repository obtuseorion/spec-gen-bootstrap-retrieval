"""Task 8 — prompt rendering golden files (0 and 2 examples) and the LLM block extractor."""

from __future__ import annotations

import os
from pathlib import Path

import pytest

from orchestrator.corpus import Record
from orchestrator.llm import extract_lean_block
from orchestrator.render import Renderer, approx_tokens
from orchestrator.units import Unit
from conftest import REPO

GOLDEN = REPO / "tests/python/golden"


def unit() -> Unit:
    return Unit.from_json({
        "id": "Corpus.demo.use_mul2_add1", "kind": "def", "members": ["Corpus.demo.use_mul2_add1"], "loops": [],
        "callees": ["Corpus.demo.mul2_add1"], "is_divergent": False, "is_generic": False,
        "signature": {"arg_type_heads": ["U32", "U32"], "ret_type_head": "Result U32", "called_consts": ["Aeneas.Std.UScalar.add"], "has_loop": False},
        "source": "def demo.use_mul2_add1 (x : Std.U32) (y : Std.U32) : Result Std.U32 := do\n  let i ← demo.mul2_add1 x\n  i + y",
        "module": "Corpus.Funs"})


def example(i: int, big: bool = False) -> Record:
    src = f"def demo.ex{i} (x : Std.U32) : Result Std.U32 := do\n  x + {i}#u32" + ("\n-- filler" * 2000 if big else "")
    spec = f"@[step]\ntheorem demo.ex{i}_spec (x : U32) (h : x.val + {i} ≤ U32.max) :\n    demo.ex{i} x ⦃ r => r.val = x.val + {i} ⦄ := by sorry"
    return Record(id=f"Corpus.demo.ex{i}", crate="corpus", unit={"source": src, "signature": {}}, spec_stmt=spec, spec_prop="",
                  proof=f"unfold demo.ex{i}\nstep* <;> scalar_tac", status="proved_modular", member_specs={f"Corpus.demo.ex{i}": spec},
                  member_proofs={f"Corpus.demo.ex{i}": f"unfold demo.ex{i}\nstep* <;> scalar_tac"})


CALLEES = {"Corpus.demo.mul2_add1": "@[step]\ntheorem demo.mul2_add1_spec (x : U32) (h : 2 * x.val + 1 ≤ U32.max) :\n    demo.mul2_add1 x ⦃ r => r.val = 2 * x.val + 1 ⦄ := by sorry"}
SPEC = "@[step]\ntheorem demo.use_mul2_add1_spec (x y : U32) (h : 2 * x.val + 1 + y.val ≤ U32.max) :\n    demo.use_mul2_add1 x y ⦃ r => r.val = 2 * x.val + 1 + y.val ⦄ := by sorry"


def check_golden(name: str, text: str) -> None:
    path = GOLDEN / name
    if os.environ.get("UPDATE_GOLDEN") or not path.is_file():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
    assert text == path.read_text(), f"{name} differs from golden file (set UPDATE_GOLDEN=1 to refresh)"


@pytest.fixture
def renderer() -> Renderer:
    return Renderer(prompts_dir=REPO / "pipeline/prompts", example_token_cap=1500)


def test_spec_prompt_zero_examples(renderer: Renderer) -> None:
    text, chosen = renderer.render_spec_prompt(unit(), "Corpus.demo.use_mul2_add1", CALLEES, [])
    assert chosen == []
    assert "example" not in text.lower()
    assert "{{" not in text
    check_golden("spec_prompt_0.md", text)


def test_spec_prompt_two_examples(renderer: Renderer) -> None:
    text, chosen = renderer.render_spec_prompt(unit(), "Corpus.demo.use_mul2_add1", CALLEES, [example(1), example(2)])
    assert [r.id for r in chosen] == ["Corpus.demo.ex1", "Corpus.demo.ex2"]
    assert "### Example 1" in text and "### Example 2" in text
    # callee specs precede examples
    assert text.index("mul2_add1_spec") < text.index("### Example 1")
    check_golden("spec_prompt_2.md", text)


def test_proof_prompt_zero_and_two(renderer: Renderer) -> None:
    text0, _ = renderer.render_proof_prompt(unit(), "Corpus.demo.use_mul2_add1", SPEC, CALLEES, [])
    assert "example" not in text0.lower() and "{{" not in text0
    check_golden("proof_prompt_0.md", text0)
    text2, chosen = renderer.render_proof_prompt(unit(), "Corpus.demo.use_mul2_add1", SPEC, CALLEES, [example(1), example(2)])
    assert len(chosen) == 2 and "step* <;> scalar_tac" in text2
    check_golden("proof_prompt_2.md", text2)


def test_oversize_example_is_dropped_not_truncated(renderer: Renderer) -> None:
    big = example(9, big=True)
    assert approx_tokens(big.unit["source"]) > 1500
    text, chosen = renderer.render_spec_prompt(unit(), "Corpus.demo.use_mul2_add1", CALLEES, [big, example(1), example(2)])
    assert [r.id for r in chosen] == ["Corpus.demo.ex1", "Corpus.demo.ex2"]
    assert "filler" not in text


def test_feedback_sections(renderer: Renderer) -> None:
    text, _ = renderer.render_spec_prompt(unit(), "Corpus.demo.use_mul2_add1", CALLEES, [], feedback="The previous attempt failed.")
    assert "## Feedback on the previous attempt" in text
    gate = {"spec_ok_on_original": True, "precond_density": 0.9, "mutants": [
        {"id": "m1", "op": "arith_swap", "site": "3:6", "before": "+", "after": "-", "killed": False, "distinguishable": True,
         "witness": "x := 3#u32", "observed": "(ok 6#u32)", "expected": "(ok 7#u32)", "timeout": False,
         "source": "def demo.use_mul2_add1_mut1 (x : Std.U32) (y : Std.U32) : Result Std.U32 := do\n  let i ← demo.mul2_add1_mut1 x\n  i - y",
         "names": [["Corpus.demo.use_mul2_add1", "Corpus.demo.use_mul2_add1_mut1"]]}]}
    fb = renderer.gate_feedback(gate, unit().source, 0.2)
    assert "arith_swap" in fb and "x := 3#u32" in fb and "-  i + y" in fb and "+  i - y" in fb
    pc = {"kernel_ok": True, "axioms_ok": True, "static_ok": False, "static_violations": ["Corpus.demo.mul2_add1"]}
    assert "Do not unfold these; use their `step` lemmas." in renderer.proof_feedback(pc)


def test_extract_lean_block() -> None:
    assert extract_lean_block("text\n```lean\nfoo\n```\nmore") == "foo"
    assert extract_lean_block("no block") is None
    assert extract_lean_block("```lean\na\n```\n```lean\nb\n```") is None
