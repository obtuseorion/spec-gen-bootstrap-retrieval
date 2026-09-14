#!/usr/bin/env python3
"""Prune definitions that do not elaborate from an Aeneas-emitted Funs.lean until `lake build` passes.

Usage: scripts/prune_funs.py <project-dir> <Namespace> [max-rounds]

Each round: `lake build`, collect `Funs.lean:LINE:COL: error` positions, map each to
the enclosing top-level declaration block (doc comment + attributes + `def`/`mutual`),
remove those blocks, log them to `pruned.log`, repeat. Definitions that depend on a
removed one fail in the next round and are removed in turn.
"""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path


def blocks(lines: list[str]) -> list[tuple[int, int, str]]:
    """(start, end, name) of top-level declaration blocks, 0-based, end exclusive."""
    starts = []
    for i, l in enumerate(lines):
        if l.startswith("/--") or l.startswith("mutual") or (l.startswith("@[") and not lines[i - 1].startswith("/--") and not lines[i - 1].startswith("@[")):
            starts.append(i)
        elif l.startswith("def ") and i > 0 and not lines[i - 1].startswith("@[") and not lines[i - 1].rstrip().endswith("-/"):
            starts.append(i)
    # dedupe & sort
    starts = sorted(set(starts))
    out = []
    for k, s in enumerate(starts):
        e = starts[k + 1] if k + 1 < len(starts) else len(lines)
        # a `mutual` block extends to its `end`
        if lines[s].startswith("mutual"):
            j = s
            while j < len(lines) and lines[j].strip() != "end":
                j += 1
            e = min(len(lines), j + 1)
        name = ""
        for l in lines[s:e]:
            m = re.match(r"^(?:def|structure|inductive|abbrev|opaque) +([A-Za-z0-9_.']+)", l)
            if m:
                name = m.group(1)
                break
        out.append((s, e, name))
    # merge blocks nested inside a mutual block
    merged = []
    for b in out:
        if merged and b[0] < merged[-1][1]:
            continue
        merged.append(b)
    return merged


def main() -> int:
    proj = Path(sys.argv[1])
    ns = sys.argv[2]
    max_rounds = int(sys.argv[3]) if len(sys.argv) > 3 else 12
    funs = proj / ns / "Funs.lean"
    log = proj / "pruned.log"
    for r in range(1, max_rounds + 1):
        proc = subprocess.run(["lake", "build"], cwd=proj, capture_output=True, text=True)
        out = proc.stdout + proc.stderr
        errs = sorted({int(m.group(1)) for m in re.finditer(rf"error: (?:[^\s:]*/)?{ns}/Funs\.lean:(\d+):\d+", out)})
        if proc.returncode == 0 and not errs:
            print(f"round {r}: build OK")
            return 0
        if not errs:
            print(f"round {r}: build failed without Funs.lean errors:\n{(proc.stdout + proc.stderr)[-3000:]}")
            return 1
        lines = funs.read_text().split("\n")
        bl = blocks(lines)
        kill: list[tuple[int, int, str]] = []
        for ln in errs:
            i = ln - 1
            for b in bl:
                if b[0] <= i < b[1]:
                    if b not in kill:
                        kill.append(b)
                    break
        if not kill:
            print(f"round {r}: could not map errors {errs[:5]} to blocks")
            return 1
        with open(log, "a") as f:
            for b in kill:
                first_err = next((m for m in re.finditer(rf"error: (?:[^\s:]*/)?{ns}/Funs\.lean:(\d+):\d+: ([^\n]*)", out)
                                  if b[0] <= int(m.group(1)) - 1 < b[1]), None)
                f.write(f"round {r}: removed {b[2] or '<block>'} (lines {b[0]+1}-{b[1]}): {first_err.group(2)[:160] if first_err else ''}\n")
        keep = []
        killed = set(range(0))
        for b in kill:
            killed |= set(range(b[0], b[1]))
        for i, l in enumerate(lines):
            if i not in killed:
                keep.append(l)
        funs.write_text("\n".join(keep))
        print(f"round {r}: {len(errs)} errors, removed {len(kill)} blocks: {[b[2] for b in kill][:8]}")
    print("max rounds reached")
    return 1


if __name__ == "__main__":
    sys.exit(main())
