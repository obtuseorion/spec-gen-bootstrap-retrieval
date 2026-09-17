# Results so far (to 2026-09-17)

Bootstrapped specification and proof generation for Aeneas-translated Rust: what was built, what it proved on
libcrux-ml-kem, what broke, and what the Aristotle escalation added.

| headline | |
|---|---|
| ml-kem units proved modularly (arm A, no examples) | 149 / 243 runnable |
| hard roots proved by Aristotle and accepted by our checker | 4 / 4 |
| model spend on ml-kem over three passes | ≈ $135 |
| unsound admissions | 0 (every accepted proof re-checks with callees opaque) |

## 1. What was built

A two-part pipeline. A Lean 4 executable (`pipeline/lean_tools`) does the trusted work: call-graph units,
spec-form checking, syntax-level mutants, a mutation-plus-property-testing gate for specifications, and a
four-way proof check (kernel, axiom set, no callee unfolding, re-check with callees opaque). A Python
orchestrator (`pipeline/orchestrator`) walks the graph callees-first, prompts the model for specs and proofs
with the admitted callee specs in context, retries with checker feedback, and writes admitted units to a
corpus store that the bootstrapped arms retrieve from. Six ablation arms differ only in which examples the
prompt gets. All ten planned tasks are implemented and covered by fixtures; the corpus crate validated the
loop end to end before any paid run. Details: `docs/engineering.md`.

## 2. libcrux-ml-kem, arm A

The crate was extracted through Charon and Aeneas with the SIMD paths disabled, SHA-3 modelled as opaque
externals with hand-written step lemmas, and definitions that do not elaborate pruned
(`crates/mlkem-lean/README.md`). 395 units; 243 runnable after excluding generic units and units that reach
a SHA-3 stub.

| status | units | note |
|---|---|---|
| proved_modular | 149 | spec passed the gate, proof passed all four checks |
| queued (pass 3 paused) | 76 | mostly NTT and serializer callers behind four hard roots |
| proof_failed | 12 | bit-packing codecs, reduction arithmetic, one loop |
| spec_rejected | 4 | two formatter impls (untestable), two loops |
| proof_blocked_by_callee | 2 | |
| skipped | 152 | 138 generic, 14 reach SHA-3 |

Admitted units take a median of 37 s wall clock; a low-effort proof call takes 4 s, a medium-effort one
90 s. Precondition density of admitted specs: median 0.49. Mutant kill rate over distinguishable mutants:
1.0 at the median.

## 3. What the run taught us

Pass 1 admitted 135 units; 95 of the remaining were never attempted because a callee below them had failed,
and those failures traced to a few roots. Two things kept the roots from being proved, both fixed during the
run:

- **Tool gaps, not model gaps.** Loop bodies (no decidability for `ControlFlow`), Result-valued functions,
  eight-tuple postconditions, slices longer than 16 and ranges were untestable by the gate regardless of
  what the model wrote; loop parents were proved before their helpers. Ten gate fixes and one ordering fix
  later, plus checker-verified loop skeletons and cast-to-`Int.bmod` recipes in the prompt, every loop unit
  that had failed both earlier passes was proved in pass 3.
- **Budgets.** Loop units need body, loop and parent proofs; five attempts per member and a 12k-token reply
  were not enough. Now 10 attempts and 32k tokens.

The residue after those fixes is genuine mathematics: bit-packing codecs and Montgomery/Barrett reduction,
which also sit at the roots of the call graph. Full failure-mode analysis: `docs/failure-modes-mlkem.md`.

## 4. Aristotle on the residue

The four hardest gate-admitted specs were submitted to Harmonic's Aristotle as a Lean project with the callee
lemmas as axioms (`docs/aristotle/f70bc649/`). Round 1 (33 min) proved all four; three used `bv_decide`,
whose native checker adds axioms our policy excludes. A follow-up (73 min) redid them with ordinary
arithmetic lemmas. With the helper lemmas inlined, all four pass our checker unchanged.

| target | pipeline model | Aristotle | our checker |
|---|---|---|---|
| `montgomery_reduce_element` | failed, 12 attempts | proved | accepted |
| `serialize_10_int` | failed, 5 attempts | proved | accepted |
| `deserialize_11_int` | failed, 5 attempts | proved | accepted |
| `deserialize_5_int` | failed, 5 attempts | proved | accepted |

Aristotle is slow on easy units (minutes of floor per theorem against seconds for the pipeline) and decisive
on hard ones. It fits as an escalation for budget-exhausted roots, not as the main prover. Its proofs are
kept out of the arm-A store.

## 5. Open items

1. Decide whether Aristotle's four proofs enter a store; if so, resume pass 3 and most of the 76 queued units
   should close.
2. Run the ablation (IMPLEMENTATION.md §8): arm C at threshold zero, choose thresholds, re-run C, then D and
   F. B and E need an external corpus.
3. Before the next paid run: a smoke set with one unit per shape class, re-queue failures right after a fix,
   retry roots before callers, budgets by member kind.

Sources: `corpus_store/mlkem/A`, `runs/mlkem/A/full/events.jsonl`, `docs/aristotle/f70bc649`,
`docs/engineering.md`, commits `bbbfba4…49c893b`.
