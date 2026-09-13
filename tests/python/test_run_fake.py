"""Task 9 — end-to-end dry run with the fake LLM, and `--resume` making no LLM calls.

Uses a temporary corpus store and run directory; the emitted project and leantools are real.
"""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from orchestrator.arms import Arm
from orchestrator.config import Config, load_config
from orchestrator.embedding import Embedder
from orchestrator.llm import FakeLLM
from orchestrator.run import Pipeline
from conftest import REPO

UNITS = ["Corpus.demo.mul2_add1", "Corpus.demo.use_mul2_add1", "Corpus.demo.incr", "Corpus.demo.list_nth"]


def tmp_config(tmp_path: Path) -> Config:
    base = load_config()
    raw = json.loads(json.dumps(base.raw))
    raw["paths"]["corpus_store"] = str(tmp_path / "store")
    raw["paths"]["runs"] = str(tmp_path / "runs")
    raw["budgets"]["pbt_runs"] = 50
    raw["budgets"]["max_mutants"] = 30
    raw["budgets"]["eval_timeout_s"] = 5
    return Config(raw=raw, root=base.root)


@pytest.mark.slow
def test_dry_run_and_resume(tmp_path: Path, project_root: Path) -> None:
    config = tmp_config(tmp_path)
    # reuse the cached graph so the test does not spend 10 s on `leantools graph`
    cached = REPO / "corpus_store/corpus/graph.json"
    if cached.is_file():
        (config.corpus_store / "corpus").mkdir(parents=True, exist_ok=True)
        (config.corpus_store / "corpus/graph.json").write_text(cached.read_text())
    llm = FakeLLM(fixtures=REPO / "tests/fixtures/fake_llm")
    run_dir = tmp_path / "run"
    pipe = Pipeline(config, "corpus", Arm("A"), llm, run_dir, units_filter=UNITS, embedder=Embedder(model_name="test"))
    counts = pipe.run()
    assert counts.get("proved_modular") == 2, counts           # mul2_add1 and its caller
    assert counts.get("spec_rejected") == 1 and counts.get("skipped_generic") == 1, counts
    store = pipe.store
    rec = store.get("Corpus.demo.use_mul2_add1")
    assert rec is not None and rec.status == "proved_modular"
    assert store.spec_path("Corpus.demo.mul2_add1").is_file()
    assert store.get_failure("Corpus.demo.incr").status == "spec_rejected"
    events = [json.loads(l) for l in (run_dir / "events.jsonl").read_text().splitlines()]
    assert {e["event"] for e in events} >= {"run_start", "llm_call", "gate", "proofcheck", "unit_done", "retrieval", "run_end"}
    first_calls = llm.calls
    assert first_calls > 0
    # resume: same run dir, nothing left to do, no LLM calls
    llm2 = FakeLLM(fixtures=REPO / "tests/fixtures/fake_llm")
    pipe2 = Pipeline(config, "corpus", Arm("A"), llm2, run_dir, units_filter=UNITS, resume=True, embedder=Embedder(model_name="test"))
    counts2 = pipe2.run()
    assert counts2 == {"resumed": len(UNITS)}, counts2
    assert llm2.calls == 0
