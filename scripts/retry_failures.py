#!/usr/bin/env python3
"""Delete failure records that should be retried after a tooling fix, so `--resume` reprocesses them.

Usage: scripts/retry_failures.py <store-dir> [--statuses spec_rejected,proof_blocked_by_callee] [--dry-run]

* `spec_rejected` records are deleted (the spec stage is where tool limitations surface).
* `proof_blocked_by_callee` records are deleted only when the blamed callee has no admitted
  record (the block was a cascade from a failure, not a weak admitted spec).
* `proof_failed` records are kept unless listed explicitly with --statuses.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("store")
    ap.add_argument("--statuses", default="spec_rejected,proof_blocked_by_callee")
    ap.add_argument("--dry-run", action="store_true")
    a = ap.parse_args()
    store = Path(a.store)
    statuses = set(a.statuses.split(","))
    admitted = {p.stem for p in (store / "records").glob("*.json")}
    deleted = []
    for f in sorted((store / "failures").glob("*.json")):
        r = json.loads(f.read_text())
        st = r["status"]
        if st not in statuses:
            continue
        if st == "proof_blocked_by_callee" and r.get("blame") in admitted:
            continue
        deleted.append((f, st, r.get("blame")))
    for f, st, blame in deleted:
        print("retry:", st, f.stem, f"(blame {blame})" if blame else "")
        if not a.dry_run:
            f.unlink()
    print(f"{len(deleted)} failure records {'would be' if a.dry_run else ''} removed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
