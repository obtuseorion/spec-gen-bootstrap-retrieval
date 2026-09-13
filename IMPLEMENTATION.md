# Bootstrapped few-shot spec/proof pipeline — implementation spec

This file is written for an agentic coding assistant. It states fixed decisions, the target layout, data schemas, component interfaces, and an ordered task list with a "done when" check for each. Do the tasks in order. Do not skip ahead to the LLM-facing parts; the gate and proof checks come first and are tested on hand-written inputs.

Companion design rationale: `bootstrapped-fewshot-spec-pipeline.md`. When this file and that one disagree, this file wins.

---

## 0. Before writing any code

1. Read the repo. Confirm the following exist and note their exact paths: the `corpus/` crate, `scripts/check.sh` (charon → aeneas → lake), `graph.json` (ground-truth dependency graph), the Lean project Aeneas emits, its `lakefile`, and the pinned toolchain (aeneas `2e8b804e`, charon `fea3fc68`, Lean `v4.31.0`).
2. Run `scripts/check.sh` end to end once and record the emitted Lean module names and the root namespace (e.g. `Corpus.*`). Everything below assumes `lake build` on the emitted project succeeds; if it does not, stop and report.
3. Identify the existing orchestration language. If there is an existing Python pipeline (`PIPELINE_C` lineage), reuse its config/logging conventions. Default assumption: **Python 3.11+ orchestrator, Lean 4 for anything that touches the environment** (graph, spec-form checks, mutation, PBT, proof checks). Do not implement Lean-side logic by regex over source text when a metaprogram is feasible.
4. Do not install or run any LLM client until Task 8.

---

## 1. Fixed decisions (do not relitigate)

| topic | decision |
|---|---|
| Unit of work | Aeneas-emitted Lean `def` + its `_loop` helpers, or one SCC (`mutual` block). Never the Rust function. |
| Processing order | Reverse topological order over the Lean dependency graph, SCCs collapsed. |
| Spec form | `@[progress] theorem <f>_spec (binders) (hyps) : ∃ r, f args = ok r ∧ Post r := by sorry` or `... : f args = ok <expr> := by sorry`. No other conclusion shape. |
| Spec vocabulary | Binders, result, and constants from `Aeneas.Std`, Lean core, Mathlib **only**. No new declarations in spec files. No reference to any Aeneas-emitted constant of the crate (including the target). |
| Decidable fragment | `=`, `<`, `≤`, `∧`, `∨`, `¬`, bounded `∀`/`∃` over `List`/`Array`/`Slice`, `List.length`, `List.Mem`. Enforced by synthesizing `Decidable` for the closed Prop. |
| Closed Prop | Derived mechanically from the theorem statement (∀-close binders, →-close hyps). Never the reverse. |
| Gate | Kill rate 1.0 over *distinguishable* mutants (distinguished on in-precondition inputs only) ∧ precondition density ≥ δ ∧ all effective PBT runs pass on the original. Defaults: δ = 0.2. |
| Corpus admission | Only `proved` and `proved_modular`. Gate-passing-but-unproved specs go to the failure log, never the corpus. |
| Proof exemplars | `proved_modular` only. Spec exemplars: `proved` or `proved_modular`. |
| Retrieval | Exclude current unit and its transitive callees by identity. Structural filter, then embedding rank. Top-2 if top score ≥ τ else none. τ frozen after calibration. |
| Rendering | Never truncate an example; drop it and try the next. Example cap K = 1500 tokens. Callee specs always precede examples and are never dropped. |
| Proof discipline | Unfold target (and its `_loop`s) only; every call handled via `progress`; no `sorry`, `native_decide`, or new `axiom`. |
| Proof checks | (1) axioms ⊆ `{propext, Classical.choice, Quot.sound}`; (2) static: no callee equation lemmas in `getUsedConstants`; (3) opaque re-check with callees replaced by `opaque` + spec `axiom`. Run all three in-loop at admission. |
| Intra-unit failures | Parent proof failing on a `_loop`/SCC-member obligation is spec-loop feedback for the unit, not callee blame. |
| Callee strengthening | Not in v1. Record `proof_blocked_by_callee` and move on. Admitted records are frozen. |
| Corpus scope | Per-crate for all experiments. |
| Budgets (defaults) | spec attempts 5, proof attempts 5, PBT effective runs 200, mutants per unit ≤ 200, per-evaluation timeout 10 s. All in config. |
| Out of scope v1 | Generics/traits, `divergent def` (skip these units and log), cross-crate corpus, spec revision after admission. |

---

## 2. Target layout

```
pipeline/
  config.toml                  # budgets, δ, τ, K, model names, paths
  orchestrator/                # Python
    run.py                     # entry: python -m orchestrator.run --crate corpus --arm C
    units.py                   # load graph, build units, order
    retrieval.py               # corpus filter + scoring + selection
    render.py                  # prompt assembly (spec / proof)
    gate.py                    # drives mutation + PBT via lean_tools, applies gate rule
    proofcheck.py              # drives axiom/static/opaque checks via lean_tools
    corpus.py                  # corpus store (SQLite + JSON files)
    llm.py                     # single thin client, retry, token accounting
    log.py                     # per-unit JSONL event log
    arms.py                    # A/B/C/D/E/F behaviour switches
  lean_tools/                  # Lean 4 package, depends on the emitted project
    lakefile.lean
    LeanTools/
      Graph.lean               # dependency graph → JSON
      SpecForm.lean            # shape + vocabulary check, spec_stmt → spec_prop
      Sample.lean              # SampleableExt/Shrinkable for Aeneas.Std types
      Mutate.lean              # mutant generation
      Eval.lean                # batched Bool evaluation with timeout + discard counting
      ProofCheck.lean          # axiom set, static walk, opaque environment rebuild
      Main.lean                # CLI: lake exe leantools <cmd> <args...> → JSON on stdout
  corpus_store/<crate>/        # created at runtime
    records/<id>.json
    specs/<id>.lean
    failures/<id>.json
    corpus.sqlite
  runs/<crate>/<arm>/<timestamp>/   # logs, metrics
tests/
  lean/                        # hand-written specs/proofs used by Tasks 2–5
  python/
```

Every `lean_tools` command is invoked by the orchestrator as a subprocess and returns a single JSON object on stdout; errors go to a JSON `{ "error": ... }` on stdout with non-zero exit. No parsing of human-readable Lean output anywhere in Python.

---

## 3. Schemas

### 3.1 Unit (output of `leantools graph`)

```json
{
  "id": "Corpus.adt_borrows.array_shared_borrow",
  "kind": "def | scc",
  "members": ["Corpus.adt_borrows.array_shared_borrow"],
  "loops": ["Corpus.adt_borrows.array_shared_borrow_loop"],
  "callees": ["<unit ids, direct>"],
  "is_divergent": false,
  "is_generic": false,
  "signature": {
    "arg_type_heads": ["Usize", "Array"],
    "ret_type_head": "Result Array",
    "called_consts": ["Aeneas.Std.Array.index_usize"],
    "has_loop": true
  },
  "source": "<pretty-printed def(s), including loops>"
}
```

`callees` are unit ids (SCC-collapsed), not raw constants. `is_generic` is true if any member has instance-implicit or universe-polymorphic-over-type arguments beyond Aeneas's standard `N : Usize` pattern; such units are skipped in v1.

### 3.2 Corpus record (`records/<id>.json`)

```json
{
  "id": "...",
  "crate": "corpus",
  "unit": { "...": "as 3.1" },
  "embedding": [0.0],
  "spec_stmt": "<theorem source with `by sorry`>",
  "spec_prop": "<closed Prop source>",
  "proof": "<tactic block>",
  "status": "proved | proved_modular",
  "mutants": { "total": 0, "distinguishable": 0 },
  "precond_density": 0.0,
  "pbt_effective_runs": 0,
  "axioms": ["propext"],
  "attempts": { "spec": 1, "proof": 1 },
  "tokens": { "spec": 0, "proof": 0 },
  "arm": "C",
  "order_index": 0,
  "examples_used": { "spec": ["<ids>"], "proof": ["<ids>"] }
}
```

### 3.3 Failure record (`failures/<id>.json`)

Same shape, with `status ∈ {spec_rejected, proof_failed, proof_blocked_by_callee, skipped_generic, skipped_divergent}`, plus `blame: "<callee id>|null"` and `last_error: "<Lean error text>"`.

### 3.4 Gate result (output of `leantools gate`)

```json
{
  "spec_ok_on_original": true,
  "precond_density": 0.63,
  "effective_runs": 200,
  "mutants": [
    { "id": "m17", "op": "ok_to_fail", "killed": true,  "distinguishable": true,  "witness": null },
    { "id": "m18", "op": "rel_swap",   "killed": false, "distinguishable": true,  "witness": "<input literal>" },
    { "id": "m19", "op": "bound_shift","killed": false, "distinguishable": false, "witness": null },
    { "id": "m20", "op": "branch_swap","killed": false, "distinguishable": true,  "witness": "<input>", "timeout": true }
  ]
}
```

Gate passes iff `spec_ok_on_original` ∧ `precond_density ≥ δ` ∧ every mutant with `distinguishable = true` has `killed = true`. A mutant that times out on an input where the original terminates is `distinguishable = true, killed = false` unless the spec rejects it on another input.

### 3.5 Proof check result (output of `leantools proofcheck`)

```json
{
  "kernel_ok": true,
  "axioms": ["propext", "Classical.choice", "Quot.sound"],
  "axioms_ok": true,
  "static_ok": false,
  "static_violations": ["Corpus.foo.eq_1"],
  "opaque_ok": null,
  "error": null,
  "blame": null
}
```

`opaque_ok` is `null` when not run (static failed). `blame` is set when `kernel_ok = false` and the failing goal was introduced by `progress` on a callee outside the unit; it is the callee unit id.

---

## 4. `lean_tools` command interface

All commands take the emitted project's root as `--project` and print one JSON object.

| command | args | output |
|---|---|---|
| `graph` | `--project` | `{ "units": [Unit], "order": ["<ids in processing order>"] }` |
| `specform` | `--project --unit <id> --spec <file>` | `{ "shape_ok", "vocab_ok", "vocab_violations": [], "decidable_ok", "spec_prop": "<src>" , "error" }` |
| `gate` | `--project --unit <id> --spec <file> --runs N --max-mutants M --timeout S` | Gate result (3.4) |
| `proofcheck` | `--project --unit <id> --spec <file> --proof <file> --callee-specs <dir>` | Proof check result (3.5) |
| `embedtext` | `--project --unit <id>` | `{ "text": "<canonicalized def source for embedding>" }` — names of local hypotheses and bound variables normalized to `x0, x1, …`; constants kept |

Implementation notes per command are in the tasks below.

---

## 5. Tasks

Each task ends with a check. Do not begin the next task until the check passes. Commit after each task.

### Task 1 — `leantools graph`

- Load the emitted project's environment. Collect every constant whose module is one Aeneas emitted (filter by module prefix from step 0.2; exclude `Aeneas.Std`).
- Edges: `d → c` for each `c ∈ d.value.getUsedConstants` that is in the collected set. Include constants reached through auxiliary definitions Lean generates (`_unsafe_rec`, `match_n`, `proof_n`), then drop the auxiliaries themselves from the node set.
- Attach `f_loop*` to `f` by name pattern **and** by edge (`f` must reference it); if a `_loop` has no parent by edge, treat it as its own unit and log a warning.
- Tarjan SCC. Units of kind `scc` for size > 1. Reverse topological order; break ties by module then name for determinism.
- `is_divergent`: constant was defined with `divergent def` (check for the Aeneas fixpoint wrapper in the value, or the `divergent` attribute if present in this Aeneas version — determine which at implementation time).
- `is_generic`: any binder that is instance-implicit, or any explicit binder of type `Type`/`Type u`.

**Done when:** on `corpus/`, the unit set and edges match `graph.json` (write a comparison script; differences must be explained, e.g. auxiliaries). The order is deterministic across two runs.

### Task 2 — `leantools specform` and `spec_stmt → spec_prop`

- Parse and elaborate the spec file in the project environment with the target unit's module imported.
- Shape: conclusion (after stripping ∀ and →) is `Exists (fun r => And (Eq (f args) (ok r)) Post)` or `Eq (f args) (ok e)`, where `f` is the unit's member (or a loop of it) applied to exactly its explicit arguments in binder order.
- Vocabulary: collect constants of the statement; each must have module prefix in `{Aeneas.Std, Init, Std, Lean core, Mathlib}` or be the head `f`. Any constant from the crate namespace other than `f` → violation. Any declaration in the spec file other than the one theorem → violation.
- `spec_prop`: build `∀ binders, hyps → conclusion` as an `Expr`, pretty-print it back to source that re-elaborates. Attempt `Decidable` synthesis on it (after instantiating with concrete sampled values? No — synthesize for the body under the binders: build `∀ b, [Decidable (body b)]` by `inferInstance` in the binder context). Report `decidable_ok`.

**Done when:** `tests/lean/specform/` contains ≥ 8 hand-written specs: 2 good in each shape, 1 wrong shape, 1 vocab violation via new def, 1 vocab violation via crate constant, 1 undecidable postcondition, 1 with loop helper. Each produces the expected JSON.

### Task 3 — `Sample.lean` (PBT instances)

Instances of `Plausible.SampleableExt` and `Plausible.Shrinkable` for:

- `U8 … U128`, `I8 … I128`, `Usize`, `Isize`: generator draws from `{0, 1, 2, max−1, max}` with weight 0.3 total, small values `< 64` with weight 0.5, uniform otherwise. Shrink toward 0.
- `Array α N`: dependent. Generator for `N` draws `≤ 16`; then a list of exactly `N.val` elements; package with the length proof. Provide `SampleableExt (Σ N, Array α N)` and a helper that, given the spec's binders, samples `N` first and the array second.
- `Slice α`: list of length ≤ 16.
- `Result α`: not needed as input; skip.
- Structs/enums from the crate: a `deriving` handler `deriving instance SampleableExt for Foo` that maps fields recursively. If the handler fails on some type, emit `{ "error": "no generator for <T>" }` from `gate` and the orchestrator marks the unit `spec_rejected` with reason `no_generator` (do not silently pass).

**Done when:** `tests/lean/sample/` samples 1000 values for each std type and for 3 crate structs from `corpus/` without error, and the value distributions include the boundary values.

### Task 4 — `Mutate.lean`

Type-preserving operators over the Aeneas-emitted `Expr`/`Syntax` (prefer `Syntax` transformation of the pretty-printed def, re-elaborated; it is far simpler than `Expr` surgery, and re-elaboration guarantees typeability). Each mutant is emitted as a new `def <f>_mut<n>` with identical signature, in a scratch module.

Operators (each tagged in `op`):

- `arith_swap`: `+`↔`-`, `*`↔`/`, on machine-int ops (`Aeneas.Std.*.add` etc.)
- `rel_swap`: `<`↔`≤`, `=`↔`≠`, `>`↔`≥`
- `bound_shift`: integer literal `n` → `n+1`, `n-1` (skip 0−1 on unsigned)
- `branch_swap`: swap `then`/`else`; rotate `match` arm bodies when types agree
- `ok_to_fail`: `ok e` → `fail .panic`
- `drop_bind`: `do let x ← e; k` → `k[x := default]` when `Inhabited` is available for `x`'s type
- `list_perm` / `list_dup` / `list_drop`: applied to any list/array-valued `ok e`: `ok e.reverse`, `ok (e ++ e.take 1)`, `ok e.tail`

Cap at `--max-mutants`; sample uniformly across operators if over cap. Loops: apply operators inside `_loop` bodies as well; the loop mutant is a mutant of the unit.

**Done when:** for 5 hand-picked `corpus/` units, every emitted mutant elaborates and `lake build`s in the scratch module; no operator produces an ill-typed mutant.

### Task 5 — `Eval.lean` and `leantools gate`

- Compile `spec_prop`'s `Decidable` instance to a `Bool`-valued function over the binder tuple. Use `#eval`-style compiled evaluation (`Lean.Elab.Command.elabEvalUnsafe` or `evalExpr` after `compileDecl`), **not** kernel `decide`.
- Sampling: draw inputs until `--runs` inputs satisfy the hypotheses or until `10 × runs` total draws; `precond_density = satisfying / total_draws`.
- For the original: evaluate spec on all satisfying inputs → `spec_ok_on_original`.
- For each mutant: run original and mutant on the same satisfying inputs (batched, one compiled call per mutant). `distinguishable` = ∃ input where outputs differ (or mutant times out and original does not). `killed` = ∃ input where spec is false on the mutant's output. `witness` = the first distinguishing input, as a Lean literal.
- Timeout: run each batched evaluation in a task with a deadline (`IO.asTask` + `IO.cancel`/heartbeat). Record `timeout: true` per mutant.

**Done when:** on `tests/lean/gate/`, (a) a `True`-postcondition spec yields kill rate 0; (b) the `array_shared_borrow` exact spec yields kill rate 1.0; (c) a `x = 0` precondition yields `precond_density < 0.2`; (d) a spec with `h : x < 100` is not penalized for a mutant that differs only at `x ≥ 100`; (e) a loop-exit-removing mutant is reported `timeout: true` and the run finishes within `2 × timeout`.

### Task 6 — `ProofCheck.lean` and `leantools proofcheck`

- Elaborate spec file with `sorry` replaced by the proof; `kernel_ok` = no errors, no `sorry` warning.
- `axioms`: `Lean.collectAxioms` on the theorem.
- Static: `getUsedConstants` of the proof term, transitively through auxiliary lemmas *generated for this proof* (`_proof_n`), not through library lemmas. Violation = any constant whose name is `g.eq_n`, `g.eq_def`, `g.eq_unfold`, `g._unfold`, `g.match_n`, or `g._unsafe_rec` for `g` an Aeneas-emitted constant **outside the unit**. `g` itself is allowed.
- Opaque: build a scratch module that imports `Aeneas.Std` and the crate's *type* declarations only, then for each transitive callee `g` outside the unit emits `opaque g : <g's type>` (needs `Inhabited`; derive from `Result.fail`) and `@[progress] axiom g_spec : <g's admitted spec statement>` read from `--callee-specs`, then the unit's own defs verbatim, then the spec+proof. `opaque_ok` = elaborates without error. If `@[progress]` on an `axiom` is rejected by this Aeneas version, wrap: `theorem g_spec' := g_spec` with the attribute on the theorem.
- Blame: when `kernel_ok = false`, inspect the error's goal; if the goal's head hypothesis was introduced by `progress` with a lemma named `<h>_spec` for `h` outside the unit, set `blame = <h's unit id>`. Best-effort; leave `null` when unsure.

**Done when:** `tests/lean/proofcheck/` covers: (a) clean `progress` proof → all ok; (b) `simp [g]` proof → static violation names `g.eq_1`; (c) `rfl`-through-callee proof → static ok, opaque fails; (d) proof using `native_decide` → `axioms_ok = false`; (e) proof unfolding the unit's own `_loop` → all ok; (f) proof failing on a weak callee spec → `blame` set.

### Task 7 — Corpus store and retrieval (`corpus.py`, `retrieval.py`)

- SQLite table mirrors 3.2 minus `embedding`; embeddings in a numpy file keyed by id. Spec source written to `specs/<id>.lean` so the opaque check can read callee specs from disk.
- `retrieve(unit, stage, arm)`:
  1. candidates = records with allowed status for `stage`, minus `unit.id`, minus transitive callees of `unit` (from the graph).
  2. structural filter — spec stage: `arg_type_heads` multiset equal and `ret_type_head` equal; proof stage: additionally `has_loop` and `is_divergent` equal and Jaccard(`called_consts`) ≥ 0.3.
  3. score = cosine(embedding(unit), embedding(candidate)) over `embedtext` output.
  4. return top 2 if `score[0] ≥ τ[stage]` else `[]`.
- Arm D: replace step 2–4 with a uniform random draw of 2 from step 1's set (seeded). Arm F: skip step 3, rank by Jaccard. Arm B/E: candidates additionally include a fixed external corpus loaded from `config.external_corpus_dir` (Aeneas test-suite specs/proofs, converted to records by a one-off script).
- Embedding model: a local code-embedding model pinned in config; the orchestrator must run offline after model download. Record the model name in every run's metadata.

**Done when:** python tests: exclusion by identity works for a unit with callees; retrieval returns `[]` below τ; arm D is seed-reproducible; embeddings are cached and not recomputed on rerun.

### Task 8 — Prompt rendering and LLM client (`render.py`, `llm.py`)

- `render_spec_prompt(unit, callee_specs, examples)` and `render_proof_prompt(unit, spec_stmt, callee_specs, examples)`. When `examples == []`, the examples section is absent — not an empty header.
- Templates live in `pipeline/prompts/spec.md` and `proof.md` with `{{ }}` placeholders; the rules text (spec form, vocabulary, decidable fragment, proof discipline) is in the template, not in Python.
- Feedback rendering: on gate failure, append a section listing up to 5 surviving distinguishable mutants as (op, unified diff of the def, witness input, observed output); on proof failure, append the Lean error verbatim and, on static violation, the offending constant names with the sentence "Do not unfold these; use their `progress` lemmas."
- `llm.py`: one function `complete(prompt, max_tokens) -> (text, usage)`. Extract exactly one ```lean block; reject responses with zero or multiple blocks and count that as an attempt.
- Token counting for K uses the same tokenizer as the model or a fixed approximation recorded in config.

**Done when:** golden-file tests for both prompts with 0 and 2 examples; the 0-example prompt contains no reference to examples.

### Task 9 — Orchestrator loop (`run.py`, `gate.py`, `proofcheck.py`, `units.py`)

Per unit, in order:

```
if unit.is_generic or unit.is_divergent: log skipped_*; continue
callee_specs = load from corpus (all direct + transitive callees); if any callee lacks a record → log proof_blocked_by_callee(blame=that callee) before spending any LLM calls; continue
examples = retrieve(unit, "spec", arm)
for attempt in 1..spec_budget:
    stmt = llm(render_spec_prompt(...))
    sf = leantools specform; if not (shape_ok ∧ vocab_ok ∧ decidable_ok): feedback; continue
    g  = leantools gate; if pass: break; else feedback
else: log spec_rejected; continue
examples = retrieve(unit, "proof", arm)
for attempt in 1..proof_budget:
    proof = llm(render_proof_prompt(...))
    pc = leantools proofcheck
    if pc.kernel_ok ∧ pc.axioms_ok ∧ pc.static_ok:
        status = proved_modular if pc.opaque_ok else proved; admit; break
    if pc.blame is not None and blame not in unit: log proof_blocked_by_callee; break
    if failure is on a _loop/SCC-member obligation:
        # intra-unit: regenerate that helper's spec with this goal as feedback, re-run gate for the unit, then continue proof attempts (counts against a shared unit budget)
    feedback
else: log proof_failed
```

- Every LLM call, gate result, and proof check result is appended to `runs/.../events.jsonl` with unit id, attempt number, and timing.
- Idempotent: rerunning with the same run directory skips units that already have a record or failure entry (`--resume`).
- `--arm` selects behaviour in `arms.py`; `--order-seed` permutes among valid topological orders for the order-sensitivity experiment.

**Done when:** a dry run with `--llm fake` (a stub returning canned specs/proofs from `tests/fixtures/`) processes `corpus/` end to end, produces records for the fixture units, and `--resume` performs no LLM calls on a second invocation.

### Task 10 — Metrics and ablation harness

- `metrics.py` reads `events.jsonl` + records and writes `summary.json` and a markdown table: per-status counts; median/p90 attempts and tokens per stage; retrieval hit rate and top-score histogram; `proof_blocked_by_callee` rate among callers of admitted specs; precondition-density distribution; per-unit difficulty proxy = arm-A attempts (join on unit id when arm A exists).
- `ablate.sh <crate>`: runs arms in the order A, C, D, F, B, E with a shared config, and a second C with `--order-seed 1`.

**Done when:** `metrics.py` runs on the Task 9 dry-run output and on an arm-A run of `corpus/`.

---

## 6. Config keys (`config.toml`)

```toml
[paths]
project = "corpus/lean"          # confirm at step 0
callee_specs = "corpus_store/corpus/specs"
external_corpus = ""             # arms B/E

[budgets]
spec_attempts = 5
proof_attempts = 5
pbt_runs = 200
max_mutants = 200
eval_timeout_s = 10

[gate]
precond_density_floor = 0.2

[retrieval]
tau_spec = 0.0                   # set after calibration; 0.0 = always retrieve top-2 (calibration mode)
tau_proof = 0.0
jaccard_min = 0.3
example_token_cap = 1500
embedding_model = "<pinned>"

[llm]
model = "<pinned>"
max_tokens_spec = 1500
max_tokens_proof = 4000
```

---

## 7. Things not to do

- Do not parse Lean's human-readable error output in Python for anything except displaying it in a prompt. All decisions come from `lean_tools` JSON.
- Do not evaluate the closed Prop with kernel `decide`.
- Do not let a spec file contain more than one declaration.
- Do not truncate examples. Drop them.
- Do not retrieve callees as examples; they are context.
- Do not admit anything below `proved`.
- Do not implement callee strengthening, corpus versioning, generics, or divergent-function support in v1, even if it looks easy in the moment. Log and skip.
- Do not lower τ or δ mid-run.
- Do not run arm C before arm A has been run on the same crate.

---

## 8. Calibration procedure (after Task 10)

1. Run arm A on `corpus/`. Record zero-example success rate per status. If `proved_modular` rate < 20%, stop and report; the base pipeline needs work before bootstrapping is meaningful.
2. Run arm C with `tau_* = 0.0` (always retrieve). For each unit, log the top-1 score and whether the examples were used in a successful attempt vs. a failed one.
3. Choose τ per stage as the score below which retrieved examples were associated with no improvement over arm A at the same unit. Freeze in config. Re-run C.
4. Run D and F. Then B/E if an external corpus has been prepared.
