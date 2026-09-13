# corpus-pinned

The canonical pipeline input: `corpus/` trimmed to the 73 modules the pinned
Charon/Aeneas release (see `src/rust_spec_synthesis/toolchain.lock.json`)
handles end-to-end. Derived mechanically from `corpus/` — copy
`Cargo.toml`, `Cargo.lock`, `src/`, then remove each excluded module file and
its `pub mod` line in `src/lib.rs`.

Excluded modules (each exists to test an upstream fix newer than the pin;
bumping the toolchain lock to a current Aeneas release should restore them):

| module | pinned-toolchain failure |
|---|---|
| `issue_1140_global_loop` | Aeneas: unresolved globals |
| `issue_1260_eliminate_shared_loans` | Aeneas: internal `Unreachable` |
| `issue_1138_slice_positivity` | Lean kernel: positivity check |
| `constants_lean` | codegen: `do` block on non-monadic global |
| `lean_keywords` | codegen: unescaped `end` binder |
| `lean_keywords_clash` | codegen: unescaped `end` binder |

Default run:

```sh
uv run rust-spec-synth verify corpus-pinned --output build/corpus-lean
```

(Seed `build/corpus-lean/.lake/packages` as a symlink to `build/lake-packages`
before the first full build to reuse the shared dependency checkout.)
