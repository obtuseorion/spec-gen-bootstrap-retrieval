# Bootstrapped few-shot spec/proof pipeline — engineering write-up

Status as of 2026-09-13. Repository: `~/Documents/spec-gen-bootstrap-retrieval` (9 commits, one per task group of `IMPLEMENTATION.md`). Everything below was built and checked in this session; the full arm-A run and the τ calibration of §8 have not been run.

## 1. What was built

The pipeline takes the Lean 4 code Aeneas emits for a Rust crate and, unit by unit in dependency order, (1) asks a model for a `@[step]` specification, (2) validates it empirically by mutation testing and property-based testing, (3) asks the model for a proof, (4) checks the proof against the kernel plus three modularity checks, and (5) admits the (definition, spec, proof) triple to a corpus that later units retrieve few-shot examples from. Arms A–F switch how examples are chosen so the bootstrapping hypothesis can be tested.

| component | language | lines | role |
|---|---|---|---|
| `pipeline/lean_tools/` | Lean 4 (12 modules) | 2 397 | everything that touches the Lean environment: graph, spec-form check, sampling, mutation, gate evaluation, proof checks, embedding text |
| `pipeline/orchestrator/` | Python (13 modules) | 1 750 | loop, corpus store, retrieval, prompt rendering, LLM client, metrics |
| `pipeline/prompts/` | Markdown templates | 110 | spec and proof prompts (rules live here, not in Python) |
| `scripts/` | bash / Python | 327 | `check.sh` (cargo → charon → aeneas → lake), `compare_graph.py` |
| `tests/` | Lean fixtures + pytest | 39 tests | one "done when" check per task; ≈3 minutes end to end |

The design rule from the spec was kept strictly: **Python never parses Lean output**. Every decision (shape, decidability, gate verdict, kernel/axiom/static/opaque results, blame) comes from a JSON object printed by `lake exe leantools <command>`. Lean error text is carried through only to be pasted into the next prompt.

## 2. Phase 0: what the environment actually was

The spec assumed aeneas `2e8b804e`, charon `fea3fc68`, a `corpus/` crate, `scripts/check.sh` and `graph.json`. Investigation found:

- The crate, `graph.json` and an emitted Lean project were in `~/Documents/GitHub/rust-spec-synthesis/corpus`, but its lakefile pointed at an Aeneas checkout that no longer exists on disk. `check.sh` was in `~/Downloads`.
- The only Aeneas that exists in binary form is the release `nightly-2026.08.20-5d08da4` (aeneas `5d08da45`, charon `f5208b1c`) cached by that repo's toolchain lock, together with a built Mathlib/Aeneas package checkout under `build/lake-packages`.
- With that release, six modules of `corpus/` do not translate (Aeneas internal errors, one kernel positivity failure, two codegen bugs). The repo already carried `corpus-pinned`, the same crate minus those six files.

Decisions (all recorded in `docs/phase0.md`):

1. **Toolchain**: use the cached release. Rebuilding Aeneas at the older pin from source (OCaml + a matching Charon + Rust nightly) was judged not worth days of work. `scripts/check.sh` was adapted: binaries from the cache, the Aeneas Lean backend as a git dependency at rev `5d08da45`, and `.lake/packages` symlinked to the shared checkout so Mathlib is never rebuilt. The full check (cargo, charon, aeneas, lake) runs in about two minutes.
2. **Crate**: `corpus/` in this repo is `corpus-pinned`. `graph.json` (made with the old pin) is still the ground truth; the comparison script explains the six missing modules as a category.
3. **Spec form**: in this Aeneas, `progress` is a deprecated alias of `step`, and the `@[step]` attribute *rejects* both conclusion shapes the spec mandates (`Exists is not a supported spec statement name`, `Eq is not a supported spec statement name`). The only registered statements are `Aeneas.Std.WP.spec` (`f args ⦃ r => P r ⦄`) and its partial-correctness variant `dspec`. Since `WP.spec x p ↔ ∃ y, x = ok y ∧ p y` (`WP.spec_equiv_exists`), the pipeline uses `@[step] theorem f_spec (binders) (hyps) : f args ⦃ r => P r ⦄ := by sorry`; the exact flavour is `⦃ r => r = e ⦄`; `dspec` is rejected.
4. **Divergence**: there is no `divergent def`. Non-structural recursion is `def … partial_fixpoint` (72 units), recognisable in the environment because the value references `Lean.Order.fix` (through a packed `<first>.mutual` constant for `mutual` blocks). Loops are otherwise the `Aeneas.Std.loop` combinator with `@[rust_loop] f_loop` and `@[rust_loop_body] f_loop.body` helpers.
5. **Generics**: type parameters are *implicit* `{T : Type}` binders and trait instances are explicit `(OrdInst : avl.Ord T)` binders; `is_generic` checks for Sort-typed binders, instance-implicit binders, and crate-struct binders named `…Inst`.

Emitted project: `corpus/lean/Corpus/{Types,Funs}.lean` (1 063 + 11 347 lines), namespace `Corpus`, 1 093 definitions, 172 `rust_loop`s, 4 `mutual` blocks.

## 3. The Lean side (`leantools`)

All commands load the emitted environment with `importModules` (≈2–4 s), run metaprograms, and print one JSON object. `Main.lean` flushes stdout and calls `IO.Process.exit` after emitting, because a diverging mutant evaluated in a task can never be cancelled and would otherwise block the runtime's shutdown (this was a real hang: the process kept spinning after the JSON was complete).

### 3.1 `graph` (Task 1)

- Nodes: definitions in crate modules whose return type is `Result _`, excluding Lean auxiliaries (`_unsafe_rec`, `match_n`, `_proof_n`, `.mutual`, equation lemmas, projections, matchers, instances).
- Edges: `getUsedConstants` of the value, walking *through* crate auxiliaries (instance structures, matchers, `.mutual` packings) but not into `_proof_n` terms. Trait dispatch therefore resolves through the instance structure to the implementing method.
- `mutual … partial_fixpoint` members reference each other only through the fixpoint tuple, never as constants; the members of each `.mutual` group are made mutually reachable so Tarjan finds the SCC.
- Loop attachment: name pattern (`f_loop<digits>`, `.body`, nested `f_loop0_loop0`) *and* reachability from the root through the whole name-based family (nested loops are reached via the outer body). Unreached candidates become their own unit with a warning (none on this crate).
- Order: Kahn over the SCC condensation with the ready set sorted by `(module, name)`; deterministic across runs (verified byte-identical).
- Signature: explicit-argument type heads, `Result <head>`, `Aeneas.Std` constants called (types filtered out), `has_loop`. Source text is taken from the persisted declaration ranges, so it includes doc comments, attributes and `partial_fixpoint`.

Performance note: the first version took 9 min 50 s. Per-phase timing showed the entire cost was in the Kahn loop, which rebuilt string sort keys inside every comparison; precomputing keys and using sorted insertion brought the whole command to 8.5 s (2.1 s of it environment loading).

Result on `corpus/`: 742 units over 1 038 nodes (4 SCCs, 72 divergent, 210 generic, 513 processable, 93 with loops). `scripts/compare_graph.py` reports `RESULT: OK` with every difference from `graph.json` categorised: 14 nodes in excluded modules, 118 `.body` helpers (graph.json lists only `_loop`), 12 globals returning `Result`, 11 edges to globals, 6 edges resolved through trait instances; 0 missing truth edges, 0 loop-attachment mismatches, 0 order violations, 4/4 SCCs matched.

### 3.2 `specform` (Task 2)

The spec file contains only the theorem; the tool prepends a fixed header (`open Aeneas Aeneas.Std Result`, options, `namespace Corpus`) and elaborates the commands on the already-loaded environment (`Lean.Elab.IO.processCommands`), so no re-import per check. Checks:

- exactly one command, a `theorem`, with `@[step]` (or the deprecated `@[progress]`);
- conclusion `WP.spec (f args) P` after the ∀/→ telescope, `f` a member of the unit, applied to exactly its arity of *distinct bound variables*; `dspec` is a shape error;
- vocabulary: crate constants other than `f` may appear only if they are types, constructors, projections, instances or matcher auxiliaries — never another emitted function or global; extra declarations in the file are violations;
- decidability: `synthInstance (Decidable …)` for every Prop binder and for the conclusion under the binders. `LeanTools.Instances` supplies `Decidable (WP.spec x p)` (by cases on `x`), `DecidablePred` through `uncurry'`/`uncurry` (the `⦃ a b => … ⦄` desugaring), and `DecidableEq` for `Array`, `Slice`, `Vec` (subtypes declared with `def`, invisible to instance search) and `Result`;
- the closed Prop is `∀ <binders>, <conclusion>` built *textually* from the theorem syntax, which re-elaborates by construction (pretty-printing the Expr lost `32#usize` literals and anonymous binders). The pretty-printed form is kept as an informational field.

Nine hand-written cases (two exact, two postcondition, wrong shape, new def, crate constant, undecidable, loop helper) all produce the expected JSON.

### 3.3 `Sample` (Task 3)

`Plausible.Arbitrary`/`Shrinkable` (hence `SampleableExt` via `selfContained`) for `UScalar ty`/`IScalar ty` with the mandated distribution (boundary 0.3, small 0.5, uniform 0.2), `Array α n` (exactly `n.val` elements with the length proof built by recursion), `Slice`/`Vec` (≤ 16), and `(N : Usize) × Array α N` with `N ≤ 16`. Crate structs and enums get `deriving instance Repr, DecidableEq, Arbitrary, Shrinkable` in the gate's scratch module; Plausible ships the deriving handlers. High-priority `Repr` instances print values as literals (`5#u32`, `(-3)#i8`, `Array.make 3#usize […]`) so witnesses in feedback are readable and mostly re-elaboratable. The test samples 1 000 values of every std type and three crate types and asserts boundary values and shrinking toward 0.

### 3.4 `mutate` (Task 4)

Mutants are source splices on the unit's pretty-printed definitions rather than `Expr` surgery. The unit text is renamed apart (`_mut0`), parsed through the frontend (so `open`s and Aeneas notations are in effect), sites are collected on the syntax tree restricted to definition bodies, and each site yields one candidate. Every member (`f`, `f_loop`, `f_loop.body`) is renamed to `<name>_mutN` with a tokenizer-based identifier rewrite (references included), and the candidate is re-elaborated; failures are dropped. Operators:

| op | site | edit |
|---|---|---|
| `arith_swap` | `«term_+_»` etc. | swap the operator atom |
| `rel_swap` | `<`/`≤`, `>`/`≥`, `=`/`≠`, `==`/`!=` | swap |
| `bound_shift` | numeric literal `n` | `n+1`, `n−1` (not below 0) |
| `branch_swap` | `if`/`doIf`, `match`/`doMatch` | swap branches; rotate arm bodies |
| `ok_to_fail` | `ok e` | `fail panic` |
| `drop_bind` | `let x ← e` in `do` | `let x ← LeanTools.Mut.dropBind e` (value `default`, failure dropped) |
| `list_perm/dup/drop` | `ok e` | `ok (LeanTools.Mut.perm/dup/drop e)` via a `SeqLike` class for `List`, `Array`, `Slice`, `Vec` |

Two things needed care: the `else` branch of a `doIf` sits inside a trailing null node, and a multi-line branch moved to a different column must be re-indented or layout-sensitive `do` parsing fails. Candidates are interleaved uniformly across operators with a seeded shuffle before the cap. For five hand-picked units every emitted mutant elaborates and the assembled scratch module builds.

### 3.5 `gate` (Task 5)

The gate builds a scratch program incrementally on top of the loaded environment: derivings for every crate type reachable from the binders and the target's type (each derivation elaborated separately; failures tolerated and reported), the mutants, then

```
abbrev LT_In := (N : Usize) × (Array U32 N)             -- data binders as nested Σ
def LT_gen : Gen LT_In := do let N ← genSmallUsize; let x ← arbitrary; pure ⟨N, x⟩
def LT_pre : LT_In → Bool := fun ⟨N, x⟩ => decide (h₁ ∧ …)
def LT_spec_orig : LT_In → Bool := fun ⟨N, x⟩ => decide (f x ⦃ r => … ⦄)
def LT_spec_m3, LT_diff_m3, LT_out_m3 …                  -- per mutant, target renamed
def LT_main : IO String := LeanTools.Eval.gateMain …
```

`LT_main` is evaluated with `evalExpr` (compiled IR through the interpreter, never kernel `decide`) and calls the natively compiled `LeanTools.Eval.gateMain`. A `Usize` binder that a later binder's type depends on is drawn small (array lengths). Inputs are drawn until `runs` satisfy the hypotheses or `10 × runs` draws; density is the ratio. The original and each mutant run as one deadline-bounded task over all inputs, mutants in chunks of 16 concurrent tasks; a task that misses the deadline is reported `timeout` with the input it was on as witness. Output difference uses `ObsEq`: exact `DecidableEq` where it exists, structural through `Result`/`Prod`/`Option`/lists, and *observational* for function-valued components (Aeneas back functions are compared on 8 sampled arguments). When no comparison is available the mutant is marked `comparable = false` and `distinguishable := killed`, which is the "presumptively equivalent" rule of §1 made explicit.

Checked cases: a `True` postcondition (with a precondition excluding underflow) has kill rate 0 among distinguishable mutants; the exact `array_shared_borrow` spec kills all 4 mutants; `h : x = 0` gives density < 0.2; on `decode_loop0_loop0` with `h : dst ≤ 32` the mutant `32 → 33` is reported not distinguishable while the exit-removing mutants are reported `timeout = true, distinguishable = true, killed = false`, and the whole run finishes in about 8 s with a 5 s timeout. Dependent inputs need one trick: a lambda returning the program's result cannot be typed through the Σ pattern, so the program text is inlined into the diff/printer closures instead of a shared `LT_run` definition.

### 3.6 `proofcheck` (Task 6)

- Callee specs (from `--callee-specs/<callee>.lean`) are loaded as `@[step] axiom`s in the kernel-check environment and removed from the reported axiom set (they are proved theorems elsewhere). Aeneas's own standard library uses `@[step] axiom`, so the attribute accepts axioms.
- `kernel_ok`: spec with `sorry` replaced by the proof elaborates with no errors and no sorry warning. Spec and proof arguments may be directories holding `<member>.lean` per member; members are checked together, helpers first.
- `axioms`: `collectAxioms` ⊆ {`propext`, `Classical.choice`, `Quot.sound`}. `native_decide` is caught here.
- static: `getUsedConstants` of the proof terms and of the auxiliaries the proof generated (constants with no module), flagging `g.eq_n`, `g.eq_def`, `g.eq_unfold`, `g._unfold`, `g.match_n`, `g._unsafe_rec`, `g.mutual` for emitted `g` outside the unit. A second, syntax-level pass flags callees named inside unfolding tactics (`simp […]`, `unfold`, `delta`, `rw`, …), because `simp [g]` on a *non-recursive* `g` delta-unfolds without any equation lemma in the term.
- opaque: a fresh environment importing `Aeneas`, `Corpus.Types` and the instances only; every needed crate constant in file order, nodes outside the unit as `opaque g : <signature>` (signature cut textually at the first ` :=`) followed by the callee's spec axiom, other constants (globals, instance structures) verbatim; then the unit's definitions and the spec+proof.
- blame: Aeneas's `step` leaves `[> let i ← mul2_add1 x <]` annotations in the goal context, so identifier tokens of the error text are matched against the callee set; exactly one match ⇒ that callee is blamed.

Six cases: clean `step*` proof (all ok), `simp [g]` (static violation), `rfl` through a callee (static ok, opaque fails), `native_decide` (axioms fail), unfolding the unit's own loop (all ok), weak callee spec (kernel fails, `blame = Corpus.demo.mul2_add1`).

### 3.7 `embedtext`

Unit source with comments and attributes stripped and every identifier that does not resolve to a global constant (under the same `open`s) renamed to `x0, x1, …` in order of first appearance; field access keeps its tail (`self.len` → `x0.len`). Only identifiers with original source positions are rewritten; macro-expanded ones report zero-width positions and would corrupt the splice.

## 4. The Python side

- `units.py` loads and caches the graph, computes transitive callees, and produces seeded valid topological orders (random choice among ready units) for the order-sensitivity experiment.
- `corpus.py`: `corpus_store/<crate>/<arm>/` with `records/<id>.json`, `specs/<member>.lean` (one file per member so the opaque check can read callee specs from disk), `failures/<id>.json`, a SQLite index mirroring §3.2, and `embeddings.npy` + id list. Stores are per (crate, arm[, order seed]) so arm C really starts from an empty corpus.
- `embedding.py`: the pinned model through `sentence-transformers` when it is installed and available offline; otherwise a deterministic hashed character n-gram embedding. The descriptor is written to `run.json` so arms are never compared across embedders.
- `retrieval.py`: identity exclusion of the unit and its transitive callees, structural filter (arg-head multiset and return head; proof stage adds `has_loop`, `is_divergent`, Jaccard ≥ 0.3), cosine ranking, top-2 if the top score ≥ τ. Arm D draws 2 uniformly (seeded), F ranks by Jaccard, B/E add an external corpus.
- `render.py`: `{{var}}` and `{{#section}}…{{/section}}` templates; the examples section is absent, not empty, with zero examples; an example over the 1 500-token cap is dropped and the next tried, never truncated; callee specs always precede examples. Feedback renderers: spec-form messages, gate feedback (spec false with witness, density too low, up to 5 surviving distinguishable mutants each with op, unified diff of the definition, witness input, mutant and original output), proof feedback (Lean error verbatim, forbidden axioms, and the sentence "Do not unfold these; use their `step` lemmas." with the offending constants).
- `llm.py`: `complete(prompt, max_tokens) -> (text, usage)` over the Anthropic SDK (model from config, streaming, server-side refusal fallbacks, SDK retries); exactly one ```lean block is extracted, otherwise the attempt is counted and rejected. A `FakeLLM` serves canned files keyed by unit, stage, member and attempt for dry runs.
- `run.py`: per unit — skip generic/divergent; every transitive callee must have a record (else `proof_blocked_by_callee` before any LLM call); **one spec per member** (loop body, loop, parent — the spec-file rule of one declaration per file forces this), each gated with the mutants of the whole unit; then one proof per member, checked incrementally on the members so far. Callee blame ends the unit; an intra-unit failure (the parent's proof mentioning a helper) regenerates that helper's spec with the failing goal as feedback, re-gates it, and redoes the proofs from that helper on, once per helper. Admission is `proved_modular` when the final opaque check passes, else `proved`. Every LLM call, gate and proof check goes to `events.jsonl`; `--resume` skips units with a record or failure (verified: a second invocation makes zero LLM calls).
- `metrics.py`: per-status counts, median/p90 attempts and tokens per stage (all units and admitted units), retrieval hit rate and top-score histogram, blocked-by-callee rate among callers of admitted specs, density and kill-rate distributions, proof-check tallies, wall clock, and outcomes bucketed by the arm-A attempt count when an arm-A store exists.
- `ablate.sh` runs A, C, D, F, then B/E if an external corpus is configured, then C with `--order-seed 1`, writing `summary.md` for each.

## 5. Evidence

| check | result |
|---|---|
| graph vs `graph.json` | OK, all differences categorised; deterministic across runs |
| specform fixtures | 9/9 |
| sampling | 1 000 samples × 12 std types + Array/Slice/Vec/Σ + 3 crate types, boundaries present |
| mutation | 5 units, every mutant elaborates and the scratch module builds |
| gate fixtures | 4/4 (kill 0, kill 1, density, out-of-precondition + timeout) |
| proofcheck fixtures | 6/6 |
| retrieval / render / extractor | 13 pure-Python tests, golden prompts for 0 and 2 examples |
| fake-LLM dry run | 4 fixture units admitted `proved_modular` including a caller that used its callee's admitted spec; `--resume` makes no LLM calls |
| real model (arm A, 3 units) | `demo.incr` and `demo.mul2_add1` proved modularly on the first spec and proof attempt (36 s and 30 s per unit); the loop unit was refused before any LLM call because its callee was outside the filtered set |

Typical costs on this machine: environment load 2–4 s per command; specform ≈4 s; gate 4–20 s for small units (more with many mutants or slow bodies); proofcheck ≈10 s (two environment loads, one for the opaque check).

## 6. Known limitations and open items

- **Pin drift** is the largest caveat: results are for aeneas `5d08da45`, not the pinned `2e8b804e`, and for `corpus-pinned` (six modules fewer).
- The spec form is `WP.spec`; any downstream tooling expecting `∃ r, … = ok r ∧ …` must use `spec_equiv_exists`.
- Blame is heuristic (callee names in the error text); it is exact on the fixtures but will misfire on errors that mention several callees (left `null` then).
- Loop bodies are PBT'd on sampled mid-iteration states, as the design doc anticipated; nothing seeds them from parent traces.
- `partial_fixpoint` units (72, including some recursive `_loop` helpers) and generic units (210) are skipped by policy; that is 229 of 742 units.
- The hashed n-gram embedder is what runs today; install the `embed` extra and run once online to switch to `jinaai/jina-embeddings-v2-base-code`, and record the change in `run.json`.
- Arms B/E need an external example corpus in `paths.external_corpus` (JSON records); none was prepared.
- Timeouts are per batch (one mutant over all inputs), which is stricter than a per-evaluation budget; a diverging task cannot be cancelled and is abandoned at process exit.

## 7. Next steps

1. Run arm A on the crate (`orchestrator.run --arm A --resume`), then `metrics.py`; if the `proved_modular` rate is below 20 % stop and improve the base prompts (§8 step 1).
2. Run arm C with τ = 0, log top-1 scores against success, choose τ per stage, freeze it in `config.toml`, re-run C.
3. Run D and F; prepare an external corpus from the Aeneas test suite for B/E.
4. Consider seeding loop-body inputs from parent traces and a less heuristic blame (recording which `step` lemma produced each hypothesis).
