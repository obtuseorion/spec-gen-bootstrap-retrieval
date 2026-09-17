# Aristotle experiment on the hard ML-KEM specs (2026-09-17)

Project `f70bc649-faae-44c0-9e00-57d7d969b799` (Harmonic Aristotle, `aristotlelib` 2.1.0), submitted from a copy of
`crates/mlkem-lean` with the Aeneas package vendored and one extra file, `AristotleTargets.submitted.lean`: the
external cast/classify step lemmas as axioms and four gate-admitted specs with `sorry`.

Round 1 (33 minutes, Lean 4.31 accepted with a toolchain warning): all four sorries filled.
Verified with `leantools proofcheck` (kernel, axiom set, static modularity, opaque re-check):

| target | result |
|---|---|
| `vector.portable.arithmetic.montgomery_reduce_element_spec` | accepted on all four checks (`montgomery_check/`) |
| `serialize_10_int_spec`, `deserialize_11_int_spec`, `deserialize_5_int_spec` | kernel and static OK once the helper lemmas are inlined as `have`s; rejected on the axiom set: `bv_decide` introduces `_native.bv_decide.ax_N` axioms |

Round 2 (follow-up task `3060cb5e-…`, 73 minutes): the three codec proofs redone without `bv_decide`, using
13 small helper lemmas (`Int.bmod`/`emod` facts, `hcast` value lemmas, or-as-addition on disjoint bits).
With the helpers each proof references inlined as `have`s (the pipeline splices a tactic block, not a file), all four
targets pass `leantools proofcheck` on every check: `checked/<unit>/{spec,proof}.lean`, `verify.round2.json`.

| target | round 2 |
|---|---|
| `montgomery_reduce_element_spec` | accepted (unchanged from round 1) |
| `serialize_10_int_spec` | accepted, 7 helpers inlined |
| `deserialize_11_int_spec` | accepted, 9 helpers inlined |
| `deserialize_5_int_spec` | accepted, 4 helpers inlined |

These proofs were produced by Aristotle, not by the pipeline's model, and are kept out of the arm-A corpus store.
