# Why passes 1 and 2 left most of ML-KEM unproved

Failure-mode analysis of the arm-A run on libcrux-ml-kem (243 runnable units), reconstructed from
`runs/mlkem/A/full/events.jsonl` and `corpus_store/mlkem/A`. Counts are gate runs and proof checks, not
units, unless stated.

| | |
|---|---|
| admitted in pass 1 | 135 of 243 |
| pass-1 units never attempted because a callee below them had failed | 95 (93 with no model call at all) |
| admitted in pass 2 | 8, of 20 decided before the API credit ran out (70 of 90 retried never reached) |
| admitted in pass 3 so far | 6, including 4 loop units that failed both earlier passes |
| spend | ≈ $55 pass 1, ≈ $50 pass 2, ≈ $30 pass 3 |

## 1. Short version

The passes did not fail on the model's understanding of the code. They failed on things between the model
and the checker, each fixed only after the units it affected had burned their budget:

- **The gate could not test whole shape classes.** Loop bodies, Result-valued functions, the eight-component
  KEM API postconditions and anything with a slice longer than 16 bytes were rejected as undecidable or
  density 0 regardless of what the model wrote: 270 of 641 pass-1 gate runs ended in a spec-form rejection,
  84 more in a density rejection.
- **Loop units were proved in the wrong order.** The parent came before its loop helper, so every parent
  proof failed with "could not find theorem …_loop_spec". No loop unit was admitted in pass 1; the bug was
  live for the first third of pass 2.
- **Cascades multiplied every root failure.** Callees go first; a caller whose transitive callee has no
  admitted spec is marked `proof_blocked_by_callee` at zero cost. Three root families (Montgomery and
  Barrett reduction, the eight bit-packing codecs, the vector arithmetic loops) sit under 50 of the 95.
- **Pass 2 spent six hours on twenty units.** The retried queue was led by the loop units, each burning
  its budget on the ordering bug and then on loop-proof mechanics the prompt had not covered, at four to
  seven minutes per attempt.

## 2. Pass 1: gate rejections (641 runs)

| outcome | runs | cause | kind |
|---|---|---|---|
| pass | 173 | | |
| spec form: undecidable | 143 | 106 on plain defs (Result `match`, 8-tuple posts hitting the instance-search limit, missing `DecidableEq`); 37 on loop members (`ControlFlow` had no instances) | tool gap |
| spec form: vocabulary | 73 | almost entirely the two formatter impls, retried five times each pass | untestable |
| spec form: bad field or name | 41 | `end_` for `«end»`, a type alias the vocabulary rule did not allow | tool gap / model |
| density below 0.2 | 84 | 23 units: slices capped at 16, ranges rarely `start ≤ end ≤ len`, 16-lane conjunctions at 0.67^16 | generator gap |
| gate error | 27 | fallback generators on parameterised structures, keyword fields | tool gap |
| surviving mutants | 15 | spec too weak | model |
| no generator | 14 | `core.fmt.Formatter` | untestable |
| spec false on original | 3 | | model |

Undecidability decays through the pass as fixes landed (63 in the 01:00 hour, 21, 5, 20, then 29 after the
restart when loop bodies came up, then 5 once `ControlFlow` had instances); failed units were not re-queued
until the pass ended.

## 3. Pass 1: proof-check rejections (~300 calls, 131 accepted)

| outcome | checks | reading |
|---|---|---|
| unsolved goals | 58 | serializers, Montgomery/Barrett arithmetic |
| `scalar_tac` failed | 31 | values behind casts (`Int.bmod`), lane indices behind pair projections |
| termination | 12 | the model referenced the theorem inside its own proof |
| "could not find theorem …_loop_spec" | 10 | ordering bug, fatal for every loop unit |
| `omega` failed | 9 | unreduced projections, missing `bmod` bounds |
| step failed | 6 | the missing loop spec again |
| heartbeats / recursion depth | 6 | bitvector reasoning in the 10-, 11-, 5-bit codecs |
| tactic-shape errors ("no goals" …) | ~25 | each costs an attempt |

## 4. Cascade roots (pass 1)

| root | root status | units blocked |
|---|---|---|
| `montgomery_reduce_element` | proof failed (5 attempts) | 12 |
| `barrett_reduce_element` | proof failed (5 attempts) | 8 |
| the eight `serialize_N_int` / `deserialize_N_int` codecs | proof failed or spec rejected | 24 |
| `arithmetic.add` (loop) | spec rejected (undecidable body) | 3 |
| other loop units | spec rejected (undecidable body) | ~30 |

The graph is shallow but wide: a few leaf arithmetic functions sit under the whole NTT, and each portable
vector operation has a trait-impl wrapper that adds a second blocked unit. The roots were of two kinds:
genuinely hard proofs that had five attempts, and loop units that were impossible until the tool gaps closed.

## 5. Pass 2 (90 retried; 20 decided in six hours)

| outcome | count | why |
|---|---|---|
| admitted | 8 | key/ciphertext indexing and `unpack_private_key`: the units the new slice and range generators unlocked |
| proof failed | 4 | compare, select_ct, add, bitwise_and: 15 attempts each |
| spec rejected | 3 | two formatters, `prf_input_inc` |
| blocked, zero attempts | 5 | three behind the failed constant-time loops, two behind `montgomery_reduce_element` (kept from pass 1) |
| never reached | 70 | still queued when the credit ran out; 72 bogus records were written and deleted |

The four loop units' checks fail in a sequence that mirrors the fixes being written: missing loop spec (3,
member order), anonymous-constructor shape (16, flat conjunction), step/rewrite mechanics (12, iterator `if`
split), `apply` with an explicit `post :=` (5), arithmetic side goals (44, `.bv` equality and projection
reduction). Budgets compounded it: 15 attempts per three-member unit, bodies taking 8 to 14, and 35 of 145
proof calls returning no proof because thinking exhausted the reply.

## 6. Evidence from pass 3

With the ordering fix, the checker-verified skeletons, 10 attempts per member and 32k tokens: compare (7
attempts), select_ct (3), add (18), bitwise_and (11) proved, and their two blocked callers followed with one
or two attempts.

## 7. Failure modes ranked by cost

1. Untested shape classes: the smoke runs contained no loop, no Result value, no long slice.
2. Fix-then-wait: each fix took effect for later units only; failed units waited for the pass boundary.
3. Roots kept, callers retried: harmless in cost, but the largest roots got no second chance.
4. Flat budgets: five attempts per member regardless of kind; a reply budget thinking could exhaust.
5. Genuinely hard proofs: codecs and modular reduction (since proved by Aristotle, `docs/aristotle/`).

## 8. Before the next crate

- Smoke-test one unit per shape class (loop, Result, Option, slice ≥ 32, multi-tuple post, cast-heavy
  arithmetic) through gate and one proof before a paid run.
- Re-queue affected failures immediately after a fix, by failure class.
- Retry roots before cascades, weighted by the number of units blocked behind them.
- Budget by member kind; thinking budget at least 32k for invariants.
- Keep the account-error abort.
