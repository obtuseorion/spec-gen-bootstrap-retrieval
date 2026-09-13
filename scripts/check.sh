#!/usr/bin/env bash
# check.sh — the single oracle for "does this crate translate through Aeneas".
#
# Usage: scripts/check.sh <crate-dir>
#
# Stages (each prints a line; the first failing stage sets the exit code):
#   1. cargo build                                     (exit 10)
#   2. charon cargo --preset=aeneas → <crate>.llbc     (exit 20)
#   3. aeneas -backend lean -split-files → Lean sources (exit 30)
#   4. no-holes gate: *External_Template.lean must not declare axioms (exit 40)
#   5. lake build of the generated Lean package        (exit 50)
#
# Adapted from the original (scripts/check.sh.orig) for the toolchain actually
# available on this machine: the pinned Aeneas *release* used by
# rust-spec-synthesis (aeneas 5d08da45, charon f5208b1c, Lean v4.31.0), whose
# Lean backend is consumed as a git dependency rather than a path checkout.
# See docs/phase0.md for the pin drift relative to IMPLEMENTATION.md.
#
# Environment (all optional):
#   AENEAS_RELEASE  root of the extracted Aeneas release (has ./aeneas, ./charon, ./backends/lean)
#   CHARON_BIN      charon binary       (default: $AENEAS_RELEASE/charon)
#   AENEAS_BIN      aeneas binary       (default: $AENEAS_RELEASE/aeneas)
#   AENEAS_REV      git rev of the Aeneas Lean backend to `require` (default: 5d08da45…)
#   LAKE_PACKAGES   an existing, built `.lake/packages` checkout to share (symlinked)
#   LAKE_TIMEOUT    seconds for lake build (default 1800)
#   OUT_DIR         where the generated Lean package goes (default: <crate>/lean)
#   NAMESPACE       Lean namespace for the emitted definitions (default: Corpus)

set -uo pipefail

CRATE="${1:?usage: check.sh <crate-dir>}"
CRATE="$(cd "$CRATE" && pwd)"
CRATE_NAME="$(basename "$CRATE")"
AENEAS_RELEASE="${AENEAS_RELEASE:-$HOME/.cache/rust-spec-synthesis/nightly-2026.08.20-5d08da4/macos-aarch64/8291c8304951b91f}"
CHARON_BIN="${CHARON_BIN:-$AENEAS_RELEASE/charon}"
AENEAS_BIN="${AENEAS_BIN:-$AENEAS_RELEASE/aeneas}"
AENEAS_REV="${AENEAS_REV:-5d08da45a405913bbee6fd544e01debf8154ac9d}"
LAKE_PACKAGES="${LAKE_PACKAGES:-$HOME/Documents/GitHub/rust-spec-synthesis/build/lake-packages}"
LAKE_TIMEOUT="${LAKE_TIMEOUT:-1800}"
OUT_DIR="${OUT_DIR:-$CRATE/lean}"
NAMESPACE="${NAMESPACE:-Corpus}"
LOG_DIR="$CRATE/check-logs"
mkdir -p "$LOG_DIR"
export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"

stage() { printf '\n== [%s] %s\n' "$1" "$2"; }
fail()  { printf '\n!! FAILED at stage %s (exit %s). Log: %s\n' "$1" "$2" "$3"; exit "$2"; }

# ---------------------------------------------------------------- 1. cargo
stage 1 "cargo build"
( cd "$CRATE" && cargo build --locked 2>&1 ) | tee "$LOG_DIR/1-cargo.log"
[ "${PIPESTATUS[0]}" -eq 0 ] || fail cargo 10 "$LOG_DIR/1-cargo.log"

# ---------------------------------------------------------------- 2. charon
stage 2 "charon cargo --preset=aeneas"
LLBC="$CRATE/$CRATE_NAME.llbc"
rm -f "$LLBC"
( cd "$CRATE" && "$CHARON_BIN" cargo --preset=aeneas "--dest-file=$LLBC" -- --locked 2>&1 ) | tee "$LOG_DIR/2-charon.log"
[ "${PIPESTATUS[0]}" -eq 0 ] || fail charon 20 "$LOG_DIR/2-charon.log"
[ -f "$LLBC" ] || { echo "no .llbc produced at $LLBC"; fail charon 20 "$LOG_DIR/2-charon.log"; }
echo "llbc: $LLBC"

# ---------------------------------------------------------------- 3. aeneas
stage 3 "aeneas -backend lean -split-files"
# Keep lake state (packages symlink, build cache) across regenerations; only the
# emitted sources are replaced.
mkdir -p "$OUT_DIR"
rm -rf "$OUT_DIR/$NAMESPACE"

EXTRA_FLAGS=()
if [ -f "$CRATE/AENEAS_FLAGS" ]; then
  while IFS= read -r line; do
    [ -n "$line" ] && [ "${line:0:1}" != "#" ] && EXTRA_FLAGS+=("$line")
  done < "$CRATE/AENEAS_FLAGS"
fi

( cd "$CRATE" && "$AENEAS_BIN" -backend lean -split-files -dest "$OUT_DIR" -subdir "$NAMESPACE" -namespace "$NAMESPACE" -emit-json "${EXTRA_FLAGS[@]}" "$LLBC" 2>&1 ) \
  | tee "$LOG_DIR/3-aeneas.log"
[ "${PIPESTATUS[0]}" -eq 0 ] || fail aeneas 30 "$LOG_DIR/3-aeneas.log"

# ---------------------------------------------------------------- 4. holes
stage 4 "no-holes gate on *External_Template.lean"
HOLES="$(grep -rn -E '^\s*(axiom|sorry)\b|\bsorry\b' "$OUT_DIR" --include='*External_Template.lean' 2>/dev/null || true)"
if [ -n "$HOLES" ]; then
  echo "$HOLES" | tee "$LOG_DIR/4-holes.log"
  echo "Missing external models — drop the offending Rust, do not write models."
  fail holes 40 "$LOG_DIR/4-holes.log"
fi
echo "no holes"

# ---------------------------------------------------------------- 5. lake
stage 5 "lake build"
if [ ! -f "$OUT_DIR/lakefile.toml" ]; then
  echo "leanprover/lean4:v4.31.0" > "$OUT_DIR/lean-toolchain"
  cat > "$OUT_DIR/lakefile.toml" <<TOML
name = "${CRATE_NAME}"
defaultTargets = ["${NAMESPACE}"]

[[require]]
name = "aeneas"
git = "https://github.com/AeneasVerif/aeneas"
subDir = "backends/lean"
rev = "${AENEAS_REV}"

[[lean_lib]]
name = "${NAMESPACE}"
TOML
  echo "wrote $OUT_DIR/lakefile.toml"
fi
# Root module <NAMESPACE>.lean importing every emitted module, so that
# `lake build` and `import Corpus` cover the whole crate.
( cd "$OUT_DIR" && {
    echo "-- Root module generated by scripts/check.sh"
    find "$NAMESPACE" -name '*.lean' | sed 's#\.lean$##; s#/#.#g' | sort | sed 's/^/import /'
  } > "$NAMESPACE.lean" )
if [ -n "$LAKE_PACKAGES" ] && [ -d "$LAKE_PACKAGES" ] && [ ! -e "$OUT_DIR/.lake/packages" ]; then
  mkdir -p "$OUT_DIR/.lake"
  ln -s "$LAKE_PACKAGES" "$OUT_DIR/.lake/packages"
  echo "shared packages: $OUT_DIR/.lake/packages -> $LAKE_PACKAGES"
fi

( cd "$OUT_DIR" && perl -e 'alarm shift; exec @ARGV' "$LAKE_TIMEOUT" lake build 2>&1 ) | tee "$LOG_DIR/5-lake.log"
rc="${PIPESTATUS[0]}"
[ "$rc" -eq 142 ] && { echo "lake build timed out after ${LAKE_TIMEOUT}s"; fail lake 50 "$LOG_DIR/5-lake.log"; }
[ "$rc" -eq 0 ] || fail lake 50 "$LOG_DIR/5-lake.log"

printf '\n== OK: %s translates and builds. Lean output in %s\n' "$CRATE_NAME" "$OUT_DIR"
exit 0
