# Bootstrapped few-shot spec/proof generation for Aeneas-translated Rust

Implementation of `IMPLEMENTATION.md`: for every Lean definition Aeneas emits
from the `corpus/` crate, generate a `@[step]` specification, validate it by
mutation testing + property-based testing, prove it against the kernel with
modularity checks, and admit the (definition, spec, proof) triple to a corpus
from which later units retrieve their few-shot examples.

Deviations forced by the toolchain that is actually installed (Aeneas
`5d08da45`, `step`/`WP.spec` instead of `progress`/`∃ r, … = ok r ∧ …`,
`partial_fixpoint` as the divergent marker) are recorded in `docs/phase0.md`.

## Layout

```
corpus/                  the crate (corpus-pinned), graph.json (ground truth), lean/ (emitted project)
scripts/check.sh         cargo → charon → aeneas → lake  (regenerates corpus/lean)
scripts/compare_graph.py leantools graph vs graph.json, every difference categorised
pipeline/lean_tools/     Lean 4 package: `lake exe leantools <graph|specform|mutate|gate|proofcheck|embedtext>`
pipeline/orchestrator/   Python: run.py (loop), gate.py, proofcheck.py, corpus.py, retrieval.py,
                         render.py, llm.py, log.py, arms.py, units.py, metrics.py
pipeline/prompts/        spec.md, proof.md templates ({{ }} placeholders, conditional sections)
pipeline/config.toml     budgets, δ, τ, K, model, paths
pipeline/ablate.sh       arms A, C, D, F, (B, E), C --order-seed 1
tests/lean/              hand-written inputs for Tasks 2–6;  tests/python/  pytest suites
corpus_store/<crate>/<arm>/   records/, specs/, failures/, corpus.sqlite, embeddings  (runtime)
runs/<crate>/<arm>/<ts>/      events.jsonl, run.json, work/, summary.{json,md}       (runtime)
```

## Setup

```sh
scripts/check.sh corpus                      # once: emit and build corpus/lean (uses the cached Aeneas release)
(cd pipeline/lean_tools && lake build)       # build the Lean tools (shares the Mathlib checkout)
uv sync --group dev                          # Python environment
.venv/bin/python -m pytest tests/python -q   # all task checks (≈5 min; needs the built project)
```

## Running

```sh
export PYTHONPATH=pipeline
.venv/bin/python -m orchestrator.run --crate corpus --arm A --llm fake --units Corpus.demo.mul2_add1   # dry run
.venv/bin/python -m orchestrator.run --crate corpus --arm A                                             # real, arm A first (§7)
.venv/bin/python -m orchestrator.run --crate corpus --arm C --resume
.venv/bin/python -m orchestrator.metrics runs/corpus/C/<ts>                                             # summary.md
pipeline/ablate.sh corpus                                                                                # A, C, D, F, (B, E), C-seed1
```

`ANTHROPIC_API_KEY` (or an `ant auth login` profile) is needed for `--llm anthropic`.
Arm C refuses to run before an arm-A store exists for the crate. The calibration
procedure for τ is `IMPLEMENTATION.md` §8: run A, run C with τ = 0, choose τ per
stage from the logged top scores, freeze it in `config.toml`, re-run C.
