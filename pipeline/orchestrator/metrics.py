"""Metrics (IMPLEMENTATION.md Task 10).

    python -m orchestrator.metrics <run-dir> [--arm-a-store DIR] [--out DIR]

Reads `<run-dir>/events.jsonl` and `run.json`, the corpus store the run wrote to,
and writes `summary.json` + `summary.md`:
  per-status counts; median/p90 attempts and tokens per stage; retrieval hit rate and
  top-score histogram; proof_blocked_by_callee rate among callers of admitted specs;
  precondition-density distribution; per-unit difficulty proxy = arm-A attempts
  (joined on unit id when an arm-A store exists).
"""

from __future__ import annotations

import argparse
import json
import statistics
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any


def _pct(xs: list[float], p: float) -> float | None:
    if not xs:
        return None
    ys = sorted(xs)
    k = max(0, min(len(ys) - 1, round(p * (len(ys) - 1))))
    return ys[k]


def _dist(xs: list[float]) -> dict[str, Any]:
    return {"n": len(xs), "median": statistics.median(xs) if xs else None, "p90": _pct(xs, 0.9), "mean": statistics.fmean(xs) if xs else None,
            "max": max(xs) if xs else None}


def load_store_records(store: Path) -> dict[str, dict[str, Any]]:
    out: dict[str, dict[str, Any]] = {}
    for sub in ("records", "failures"):
        d = store / sub
        if d.is_dir():
            for f in d.glob("*.json"):
                r = json.loads(f.read_text())
                out[r["id"]] = r
    return out


def compute(run_dir: Path, arm_a_store: Path | None = None) -> dict[str, Any]:
    meta = json.loads((run_dir / "run.json").read_text()) if (run_dir / "run.json").is_file() else {}
    events = [json.loads(l) for l in (run_dir / "events.jsonl").read_text().splitlines() if l.strip()]
    store = Path(meta.get("store", ""))
    records = load_store_records(store) if store.is_dir() else {}
    done = [e for e in events if e["event"] == "unit_done"]
    status_counts = Counter(e["status"] for e in done)
    by_unit = {e["unit"]: e for e in done}

    # attempts / tokens per stage, over units that reached the stage
    attempts_spec = [e["attempts"]["spec"] for e in done if e.get("attempts") and e["attempts"]["spec"] > 0]
    attempts_proof = [e["attempts"]["proof"] for e in done if e.get("attempts") and e["attempts"]["proof"] > 0]
    tokens_spec = [e["tokens"]["spec"] for e in done if e.get("tokens") and e["tokens"]["spec"] > 0]
    tokens_proof = [e["tokens"]["proof"] for e in done if e.get("tokens") and e["tokens"]["proof"] > 0]
    admitted = {u for u, e in by_unit.items() if e["status"] in ("proved", "proved_modular")}
    attempts_spec_adm = [by_unit[u]["attempts"]["spec"] for u in admitted]
    attempts_proof_adm = [by_unit[u]["attempts"]["proof"] for u in admitted]

    # retrieval
    retr = [e for e in events if e["event"] == "retrieval"]
    retrieval: dict[str, Any] = {}
    for stage in ("spec", "proof"):
        rs = [e for e in retr if e["stage"] == stage]
        hits = [e for e in rs if e["examples"]]
        scores = [e["top_score"] for e in rs if e.get("top_score") is not None]
        hist = Counter(f"{int(s * 10) / 10:.1f}" for s in scores)
        retrieval[stage] = {"queries": len(rs), "hit_rate": (len(hits) / len(rs)) if rs else None,
                            "top_score_histogram": dict(sorted(hist.items())), "top_score": _dist(scores),
                            "candidates_mean": statistics.fmean([e["candidates"] for e in rs]) if rs else None}

    # blocked-by-callee rate among callers of admitted specs
    callers_of_admitted = [u for u, r in records.items() if any(c in admitted for c in r.get("unit", {}).get("callees", []))]
    blocked = [u for u in callers_of_admitted if records[u]["status"] == "proof_blocked_by_callee" and records[u].get("blame") in admitted]
    blocked_rate = (len(blocked) / len(callers_of_admitted)) if callers_of_admitted else None

    # gate statistics
    gates = [e for e in events if e["event"] == "gate"]
    densities = [e["precond_density"] for e in gates if e.get("precond_density") is not None]
    kill = [(e["mutants_killed"] / e["mutants_distinguishable"]) for e in gates if e.get("mutants_distinguishable")]
    gate_reasons = Counter(e.get("reason") for e in gates)
    pcs = [e for e in events if e["event"] == "proofcheck"]
    pc_summary = {"checks": len(pcs), "accepted": sum(1 for e in pcs if e.get("accepted")), "modular": sum(1 for e in pcs if e.get("modular")),
                  "static_violations": sum(1 for e in pcs if e.get("static_violations")), "blamed": sum(1 for e in pcs if e.get("blame"))}

    # difficulty proxy: arm-A attempts per unit
    difficulty: dict[str, Any] = {}
    if arm_a_store and arm_a_store.is_dir():
        a_records = load_store_records(arm_a_store)
        buckets: dict[str, list[str]] = defaultdict(list)
        for u, e in by_unit.items():
            a = a_records.get(u)
            if a is None:
                continue
            k = a["attempts"]["spec"] + a["attempts"]["proof"]
            bucket = "A:skipped" if a["status"].startswith("skipped") else f"A:{min(k, 10)}"
            buckets[bucket].append(e["status"])
        difficulty = {b: dict(Counter(v)) for b, v in sorted(buckets.items())}

    llm_calls = [e for e in events if e["event"] == "llm_call"]
    wall = [e.get("elapsed_s", 0) for e in done if e.get("elapsed_s")]
    return {
        "run_dir": str(run_dir), "arm": meta.get("arm"), "order_seed": meta.get("order_seed"), "llm": meta.get("llm"),
        "model": meta.get("model"), "embedder": meta.get("embedder"), "units_done": len(done),
        "status_counts": dict(status_counts),
        "admitted": len(admitted),
        "attempts": {"spec": _dist(attempts_spec), "proof": _dist(attempts_proof),
                     "spec_admitted": _dist(attempts_spec_adm), "proof_admitted": _dist(attempts_proof_adm)},
        "tokens": {"spec": _dist(tokens_spec), "proof": _dist(tokens_proof),
                   "total": sum(e["usage"]["input_tokens"] + e["usage"]["output_tokens"] for e in llm_calls)},
        "llm_calls": len(llm_calls), "llm_calls_without_block": sum(1 for e in llm_calls if not e.get("block_ok")),
        "retrieval": retrieval,
        "proof_blocked_by_callee_rate_among_callers_of_admitted": blocked_rate,
        "callers_of_admitted": len(callers_of_admitted),
        "gate": {"runs": len(gates), "reasons": dict(gate_reasons), "precond_density": _dist(densities),
                 "density_histogram": dict(sorted(Counter(f"{int(d * 10) / 10:.1f}" for d in densities).items())),
                 "kill_rate": _dist(kill)},
        "proofcheck": pc_summary,
        "wall_clock_s_per_unit": _dist(wall),
        "difficulty_by_arm_A_attempts": difficulty,
    }


def to_markdown(s: dict[str, Any]) -> str:
    def row(k: str, v: Any) -> str:
        return f"| {k} | {v} |"

    def dist(d: dict[str, Any]) -> str:
        if not d or d.get("n") is None:
            return "–"
        return f"n={d['n']}, median={d['median']}, p90={d['p90']}"

    lines = [f"# Run summary: arm {s.get('arm')} ({s.get('run_dir')})", "",
             f"llm: {s.get('llm')} / {s.get('model')}; embedder: {s.get('embedder')}; order seed: {s.get('order_seed')}", "",
             "| status | count |", "|---|---|"]
    lines += [row(k, v) for k, v in sorted(s["status_counts"].items())]
    lines += ["", "| metric | value |", "|---|---|",
              row("units done", s["units_done"]), row("admitted", s["admitted"]),
              row("spec attempts (all)", dist(s["attempts"]["spec"])), row("spec attempts (admitted)", dist(s["attempts"]["spec_admitted"])),
              row("proof attempts (all)", dist(s["attempts"]["proof"])), row("proof attempts (admitted)", dist(s["attempts"]["proof_admitted"])),
              row("tokens spec", dist(s["tokens"]["spec"])), row("tokens proof", dist(s["tokens"]["proof"])), row("tokens total", s["tokens"]["total"]),
              row("LLM calls / without block", f"{s['llm_calls']} / {s['llm_calls_without_block']}"),
              row("retrieval hit rate spec", s["retrieval"]["spec"]["hit_rate"]), row("retrieval hit rate proof", s["retrieval"]["proof"]["hit_rate"]),
              row("top-score histogram spec", s["retrieval"]["spec"]["top_score_histogram"]),
              row("top-score histogram proof", s["retrieval"]["proof"]["top_score_histogram"]),
              row("blocked-by-callee rate among callers of admitted", s["proof_blocked_by_callee_rate_among_callers_of_admitted"]),
              row("gate runs / reasons", f"{s['gate']['runs']} / {s['gate']['reasons']}"),
              row("precondition density", dist(s["gate"]["precond_density"])), row("density histogram", s["gate"]["density_histogram"]),
              row("kill rate over distinguishable", dist(s["gate"]["kill_rate"])),
              row("proof checks (accepted / modular / static viol. / blamed)",
                  f"{s['proofcheck']['checks']} ({s['proofcheck']['accepted']} / {s['proofcheck']['modular']} / {s['proofcheck']['static_violations']} / {s['proofcheck']['blamed']})"),
              row("wall clock per unit (s)", dist(s["wall_clock_s_per_unit"]))]
    if s["difficulty_by_arm_A_attempts"]:
        lines += ["", "## Outcome by difficulty proxy (arm-A attempts)", "", "| arm-A attempts | outcomes |", "|---|---|"]
        lines += [row(k, v) for k, v in s["difficulty_by_arm_A_attempts"].items()]
    return "\n".join(lines) + "\n"


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("run_dir")
    ap.add_argument("--arm-a-store", default=None)
    ap.add_argument("--out", default=None)
    args = ap.parse_args(argv)
    run_dir = Path(args.run_dir)
    arm_a = Path(args.arm_a_store) if args.arm_a_store else None
    if arm_a is None:
        meta = json.loads((run_dir / "run.json").read_text()) if (run_dir / "run.json").is_file() else {}
        store = Path(meta.get("store", ""))
        cand = store.parent / "A"
        arm_a = cand if cand.is_dir() and meta.get("arm") != "A" else None
    s = compute(run_dir, arm_a)
    out = Path(args.out) if args.out else run_dir
    out.mkdir(parents=True, exist_ok=True)
    (out / "summary.json").write_text(json.dumps(s, indent=1, default=str))
    (out / "summary.md").write_text(to_markdown(s))
    print(to_markdown(s))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
