#!/usr/bin/env bash
# ablate.sh <crate> [extra run.py args…]
#
# Runs the ablation arms in the order A, C, D, F, B, E with the shared config, then a
# second C run with --order-seed 1 (order sensitivity), and writes metrics for each.
# Arms B/E are skipped when config `paths.external_corpus` is empty.
#
# Environment: LLM (anthropic|fake, default anthropic), RUN_ID (default: timestamp).
set -euo pipefail
CRATE="${1:?usage: ablate.sh <crate> [run.py args…]}"; shift || true
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
LLM="${LLM:-anthropic}"
RUN_ID="${RUN_ID:-$(date -u +%Y%m%dT%H%M%SZ)}"
PY="$ROOT/.venv/bin/python"
export PYTHONPATH="$HERE"

EXTERNAL="$($PY - <<'EOF'
import tomllib; print(tomllib.load(open("pipeline/config.toml","rb"))["paths"].get("external_corpus",""))
EOF
)"

run_arm() {  # arm [order-seed]
  local arm="$1" seed="${2:-}" tag="$1"
  local args=(--crate "$CRATE" --arm "$arm" --llm "$LLM" --resume "$@")
  if [ -n "$seed" ]; then args+=(--order-seed "$seed"); tag="$arm-seed$seed"; fi
  local dir="$ROOT/runs/$CRATE/$tag/$RUN_ID"
  echo "== arm $tag → $dir"
  (cd "$ROOT" && $PY -m orchestrator.run "${args[@]}" --run-dir "$dir")
  (cd "$ROOT" && $PY -m orchestrator.metrics "$dir" --arm-a-store "$ROOT/corpus_store/$CRATE/A" > /dev/null)
  echo "   metrics: $dir/summary.md"
}

run_arm A
run_arm C
run_arm D
run_arm F
if [ -n "$EXTERNAL" ]; then run_arm B; run_arm E; else echo "== arms B/E skipped: no external corpus configured"; fi
run_arm C 1
echo "== done: runs/$CRATE/*/$RUN_ID"
