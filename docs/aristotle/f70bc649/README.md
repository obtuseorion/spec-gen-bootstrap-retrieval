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

A follow-up asked for the three codec proofs without `bv_decide` (task `3060cb5e-…`).
These proofs were produced by Aristotle, not by the pipeline's model, and are kept out of the arm-A corpus store.
