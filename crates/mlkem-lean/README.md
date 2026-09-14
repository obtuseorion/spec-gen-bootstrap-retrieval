# libcrux-ml-kem, emitted for the spec pipeline

Source: https://github.com/celabshq/libcrux (`libcrux-ml-kem`, cloned 2026-09-14 into `crates/libcrux`).

Extraction (workspace crate, so `scripts/check.sh` was not used):

```sh
cd crates/libcrux/libcrux-ml-kem
cargo +nightly-2026-06-01 generate-lockfile && cargo +nightly-2026-06-01 build --locked
LIBCRUX_DISABLE_SIMD128=1 LIBCRUX_DISABLE_SIMD256=1 \
  $AENEAS_RELEASE/charon cargo --preset=aeneas --dest-file=$PWD/libcrux_ml_kem.llbc -- --locked
$AENEAS_RELEASE/aeneas -backend lean -split-files -dest lean2 -subdir MlKem -namespace MlKem -emit-json \
  -all-computable libcrux_ml_kem.llbc
```

`LIBCRUX_DISABLE_SIMD*` keeps the build scripts from enabling the NEON/AVX2 paths
(63 intrinsic externals otherwise). `-all-computable` removes the `noncomputable
section`, which the gate's compiled evaluation needs.

External models (`MlKem/FunsExternal.lean`, `MlKem/TypesExternal.lean`) were written
by hand from Aeneas's templates:

- `libcrux_secrets` classify/declassify and `CastOps` casts: identities and Aeneas scalar casts
  (the Rust functions are identities when secret-independence checking is off);
- `core::array::from_fn`, `[T; N]::map`, `IntoIter`, `PartialEq<&[U]> for [T; N]`,
  `Result::map_err`, `hint::black_box`: real semantics;
- `libcrux_platform::simd*_support`: `false`;
- `libcrux_traits::kem` error conversions: variant-wise;
- **SHA-3 (`libcrux_sha3::portable::*`): stubs that `fail`**. They are listed in
  `external_stubs.txt`; the orchestrator records every unit that reaches one as
  `skipped_external` before spending a model call, so no spec is ever tested against a
  fake hash.

`MlKem.lean` is the root module. Dependencies are shared through the
`.lake/packages` symlink like `corpus/lean`.
