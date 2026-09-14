"""Orchestrator entry point (IMPLEMENTATION.md Task 9).

    python -m orchestrator.run --crate corpus --arm C [--llm anthropic|fake] [--order-seed N]
                               [--units id,id] [--limit N] [--resume] [--run-dir DIR]

Per unit, in processing order (callees first):
  skip generic / divergent units (logged);
  require a corpus record for every transitive callee (else proof_blocked_by_callee, no LLM call);
  spec stage per member (loop body, loop, parent): retrieve → prompt → specform → gate, ≤ spec_attempts;
  proof stage per member: retrieve → prompt → proofcheck on the members so far, ≤ proof_attempts;
  admit (proved / proved_modular) or record the failure.

The corpus store is per (crate, arm[, order seed]); every LLM call, gate and proof check is
appended to `<run-dir>/events.jsonl`. `--resume` skips units that already have a record or failure.
"""

from __future__ import annotations

import argparse
import json
import shutil
import sys
import time
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

from orchestrator.arms import Arm
from orchestrator.config import Config, load_config
from orchestrator.corpus import CorpusStore, Record
from orchestrator.embedding import Embedder
from orchestrator.gate import GateOutcome, run_gate
from orchestrator.leantools import LeanTools
from orchestrator.llm import FakeLLM, extract_lean_block, make_llm
from orchestrator.log import EventLog
from orchestrator.proofcheck import ProofOutcome, run_proofcheck
from orchestrator.render import Renderer, approx_tokens
from orchestrator.retrieval import Retriever
from orchestrator.units import Graph, Unit, load_graph


def member_order(unit: Unit, namespace: str = "Corpus") -> list[str]:
    """Members in source order: loop bodies, loops, then parents (the order of the pretty-printed unit)."""
    def pos(m: str) -> int:
        short = m[len(namespace) + 1:] if m.startswith(namespace + ".") else m
        i = unit.source.find(f"def {short}\n")
        if i < 0:
            i = unit.source.find(f"def {short} ")
        return i if i >= 0 else 10**9
    return sorted(unit.all_members, key=pos)


class Pipeline:
    def __init__(self, config: Config, crate: str, arm: Arm, llm, run_dir: Path, *, order_seed: int | None = None,
                 resume: bool = False, units_filter: list[str] | None = None, limit: int | None = None,
                 external: list[Record] | None = None, embedder: Embedder | None = None):
        self.config = config
        self.crate = crate
        self.arm = arm
        self.llm = llm
        self.run_dir = run_dir.resolve()
        self.order_seed = order_seed
        self.resume = resume
        self.units_filter = units_filter
        self.limit = limit
        self.tools = LeanTools(config)
        store_tag = arm.name if order_seed is None else f"{arm.name}-seed{order_seed}"
        self.store = CorpusStore(config.corpus_store / crate, store_tag)
        self.graph: Graph = load_graph(config, self.tools, crate)
        self.member_to_unit = self.graph.member_to_unit()
        self.log = EventLog(run_dir / "events.jsonl")
        self.embedder = embedder or Embedder.create(config.retrieval["embedding_model"])
        self.retriever = Retriever(self.store, self.graph, self.embedder, config.retrieval, external=external,
                                   seed=order_seed or 0, embed_text_fn=self._embed_text)
        self.renderer = Renderer(config.prompts, int(config.retrieval["example_token_cap"]),
                                 float(str(config.llm.get("tokenizer", "approx:chars/3.5")).split("/")[-1]), config.namespace)
        self.work = self.run_dir / "work"
        self.work.mkdir(parents=True, exist_ok=True)
        # external models that are stubs (`<project>/external_stubs.txt`): units reaching one are skipped
        stubs_file = config.project / "external_stubs.txt"
        self.external_stubs = set(stubs_file.read_text().split()) if stubs_file.is_file() else set()
        self._write_metadata()

    # ---- helpers -------------------------------------------------------------
    def _write_metadata(self) -> None:
        meta = {"crate": self.crate, "arm": self.arm.name, "arm_description": self.arm.description,
                "order_seed": self.order_seed, "llm": getattr(self.llm, "name", "?"), "model": self.config.llm.get("model"),
                "embedder": self.embedder.descriptor, "tokenizer": self.config.llm.get("tokenizer"),
                "started": datetime.now(UTC).isoformat(), "config": self.config.raw, "store": str(self.store.root),
                "units_filter": self.units_filter, "limit": self.limit}
        (self.run_dir / "run.json").write_text(json.dumps(meta, indent=1, default=str))

    def _embed_text(self, unit_id: str) -> str:
        u = self.graph.units[unit_id]
        out = self.tools.embedtext(unit_id, list(u.all_members))
        return out.get("text") or u.source

    def _llm(self, prompt: str, max_tokens: int, unit: Unit, stage: str, member: str, attempt: int) -> tuple[str | None, dict[str, Any]]:
        if isinstance(self.llm, FakeLLM):
            self.llm.context = {"unit": unit.id, "stage": stage, "member": member, "attempt": str(attempt)}
        t0 = time.monotonic()
        text, usage = self.llm.complete(prompt, max_tokens)
        block = extract_lean_block(text)
        info = {"unit": unit.id, "stage": stage, "member": member, "attempt": attempt, "prompt_tokens_approx": approx_tokens(prompt),
                "usage": usage.to_json(), "elapsed_s": round(time.monotonic() - t0, 3), "block_ok": block is not None}
        self.log.emit("llm_call", **info)
        (self.work / unit.id / f"{stage}.{member}.{attempt}.prompt.md").parent.mkdir(parents=True, exist_ok=True)
        (self.work / unit.id / f"{stage}.{member}.{attempt}.prompt.md").write_text(prompt)
        (self.work / unit.id / f"{stage}.{member}.{attempt}.response.md").write_text(text)
        return block, info

    def _callee_specs(self, unit: Unit) -> dict[str, str]:
        out: dict[str, str] = {}
        for c in unit.callees:
            for m in self.graph.units[c].all_members:
                p = self.store.spec_path(m)
                if p.is_file():
                    out[m] = p.read_text()
        return out

    def _failure(self, unit: Unit, status: str, order_index: int, attempts: dict[str, int], tokens: dict[str, int],
                 blame: str | None = None, last_error: str | None = None, **extra: Any) -> None:
        rec = Record(id=unit.id, crate=self.crate, unit=unit.to_json(), spec_stmt="", spec_prop="", proof="", status=status,
                     attempts=attempts, tokens=tokens, arm=self.arm.name, order_index=order_index, blame=blame,
                     last_error=(last_error or "")[:4000] or None, extra=extra)
        self.store.fail(rec)
        self.log.emit("unit_done", unit=unit.id, status=status, blame=blame, attempts=attempts, tokens=tokens)

    # ---- main loop -----------------------------------------------------------
    def run(self) -> dict[str, int]:
        order = self.graph.seeded_order(self.order_seed)
        if self.units_filter:
            wanted = set(self.units_filter)
            order = [u for u in order if u in wanted]
        if self.limit:
            order = order[: self.limit]
        counts: dict[str, int] = {}
        self.log.emit("run_start", arm=self.arm.name, units=len(order), order_seed=self.order_seed)
        for idx, uid in enumerate(order):
            unit = self.graph.units[uid]
            if self.resume and (self.store.has_record(uid) or self.store.has_failure(uid)):
                self.log.emit("unit_skipped_resume", unit=uid)
                counts["resumed"] = counts.get("resumed", 0) + 1
                continue
            status = self.process_unit(unit, idx)
            counts[status] = counts.get(status, 0) + 1
        self.log.emit("run_end", counts=counts)
        (self.run_dir / "counts.json").write_text(json.dumps(counts, indent=1))
        return counts

    def process_unit(self, unit: Unit, order_index: int) -> str:
        t_unit = time.monotonic()
        self.log.emit("unit_start", unit=unit.id, kind=unit.kind, members=list(unit.all_members), callees=list(unit.callees))
        attempts = {"spec": 0, "proof": 0}
        tokens = {"spec": 0, "proof": 0}
        if unit.is_generic:
            self._failure(unit, "skipped_generic", order_index, attempts, tokens)
            return "skipped_generic"
        if unit.is_divergent:
            self._failure(unit, "skipped_divergent", order_index, attempts, tokens)
            return "skipped_divergent"
        stubs = sorted(self.graph.transitive_externals(unit.id) & self.external_stubs)
        if stubs:
            self._failure(unit, "skipped_external", order_index, attempts, tokens,
                          last_error="reaches external stub(s): " + ", ".join(stubs), externals=stubs)
            return "skipped_external"
        for c in sorted(self.graph.transitive_callees(unit.id)):
            if not self.store.has_record(c):
                self._failure(unit, "proof_blocked_by_callee", order_index, attempts, tokens, blame=c,
                              last_error=f"callee {c} has no admitted record")
                return "proof_blocked_by_callee"
        members = member_order(unit, self.config.namespace)
        udir = self.work / unit.id
        specs_dir, proofs_dir = udir / "specs", udir / "proofs"
        for d in (specs_dir, proofs_dir):
            if d.exists():
                shutil.rmtree(d)
            d.mkdir(parents=True)
        callee_specs = self._callee_specs(unit)
        budgets = self.config.budgets

        # ---------------- spec stage ----------------
        ret = self.retriever.retrieve(unit, "spec", self.arm.name)
        self.log.emit("retrieval", unit=unit.id, stage="spec", **ret.to_json())
        member_specs: dict[str, str] = {}
        member_props: dict[str, str] = {}
        gate_summary: dict[str, Any] = {}
        examples_used: dict[str, list[str]] = {"spec": [], "proof": []}
        spec_budget_left = {m: int(budgets["spec_attempts"]) for m in members}

        def spec_stage(member: str, feedback: str) -> tuple[bool, str]:
            nonlocal gate_summary
            while spec_budget_left[member] > 0:
                spec_budget_left[member] -= 1
                attempts["spec"] += 1
                attempt = attempts["spec"]
                others = {m: s for m, s in member_specs.items() if m != member}
                prompt, chosen = self.renderer.render_spec_prompt(unit, member, callee_specs, ret.examples, others, feedback)
                examples_used["spec"] = sorted({*examples_used["spec"], *(r.id for r in chosen)})
                block, info = self._llm(prompt, int(self.config.llm["max_tokens_spec"]), unit, "spec", member, attempt)
                tokens["spec"] += info["usage"]["input_tokens"] + info["usage"]["output_tokens"]
                if block is None:
                    feedback = "The reply must contain exactly one ```lean block with the theorem."
                    continue
                spec_file = specs_dir / f"{member}.lean"
                spec_file.write_text(block.rstrip() + "\n")
                outcome: GateOutcome = run_gate(self.config, self.tools, unit, members, spec_file, seed=attempt)
                self.log.emit("gate", unit=unit.id, member=member, attempt=attempt, **outcome.summary,
                              specform={k: outcome.specform.get(k) for k in ("shape_ok", "attr_ok", "vocab_ok", "decidable_ok", "shape", "error")})
                if outcome.passed:
                    member_specs[member] = block
                    member_props[member] = outcome.specform.get("spec_prop", "")
                    gate_summary = outcome.summary
                    return True, ""
                if outcome.reason == "no_generator":
                    return False, f"no_generator: {outcome.gate.get('error') if outcome.gate else ''}"
                if outcome.reason == "specform":
                    feedback = self.renderer.specform_feedback(outcome.specform)
                elif outcome.reason == "error":
                    feedback = "The gate could not run this specification:\n```\n" + str(outcome.gate.get("error", ""))[:1500] + "\n```"
                else:
                    feedback = self.renderer.gate_feedback(outcome.gate or {}, unit.source, float(self.config.gate["precond_density_floor"]))
                spec_file.unlink(missing_ok=True)
            return False, "spec budget exhausted"

        for member in members:
            ok, why = spec_stage(member, "")
            if not ok:
                self._failure(unit, "spec_rejected", order_index, attempts, tokens, last_error=why, member=member,
                              elapsed_s=round(time.monotonic() - t_unit, 1))
                return "spec_rejected"

        # ---------------- proof stage ----------------
        retp = self.retriever.retrieve(unit, "proof", self.arm.name)
        self.log.emit("retrieval", unit=unit.id, stage="proof", **retp.to_json())
        member_proofs: dict[str, str] = {}
        proof_budget = int(budgets["proof_attempts"]) * len(members)
        regenerated: set[str] = set()
        last_pc: ProofOutcome | None = None
        i = 0
        feedback = ""
        while i < len(members):
            member = members[i]
            if proof_budget <= 0:
                self._failure(unit, "proof_failed", order_index, attempts, tokens, last_error="proof budget exhausted",
                              member=member, elapsed_s=round(time.monotonic() - t_unit, 1))
                return "proof_failed"
            proof_budget -= 1
            attempts["proof"] += 1
            attempt = attempts["proof"]
            others = {m: s for m, s in member_specs.items() if m != member}
            prompt, chosen = self.renderer.render_proof_prompt(unit, member, member_specs[member], callee_specs, retp.examples, others, feedback)
            examples_used["proof"] = sorted({*examples_used["proof"], *(r.id for r in chosen)})
            block, info = self._llm(prompt, int(self.config.llm["max_tokens_proof"]), unit, "proof", member, attempt)
            tokens["proof"] += info["usage"]["input_tokens"] + info["usage"]["output_tokens"]
            if block is None:
                feedback = "The reply must contain exactly one ```lean block with the tactic proof."
                continue
            (proofs_dir / f"{member}.lean").write_text(block.rstrip() + "\n")
            checked = members[: i + 1]
            pc = run_proofcheck(self.tools, unit, checked, specs_dir, proofs_dir, self.store.specs_dir, self.member_to_unit, member)
            self.log.emit("proofcheck", unit=unit.id, member=member, attempt=attempt, members_checked=checked, **pc.summary)
            if pc.accepted:
                member_proofs[member] = block
                last_pc = pc
                feedback = ""
                i += 1
                continue
            if pc.blame_unit is not None:
                self._failure(unit, "proof_blocked_by_callee", order_index, attempts, tokens, blame=pc.blame_unit,
                              last_error=pc.result.get("error"), member=member, elapsed_s=round(time.monotonic() - t_unit, 1))
                return "proof_blocked_by_callee"
            if pc.intra_unit_member and pc.intra_unit_member not in regenerated and pc.intra_unit_member in members[:i]:
                # intra-unit failure: regenerate the helper's spec with this goal as feedback, re-gate, redo its proof
                helper = pc.intra_unit_member
                regenerated.add(helper)
                self.log.emit("intra_unit_regenerate", unit=unit.id, helper=helper, from_member=member)
                ok, why = spec_stage(helper, "The proof of the parent failed on an obligation about this helper:\n```\n"
                                     + (pc.result.get("error") or "")[:3000] + "\n```\nStrengthen or adjust this helper's specification.")
                if not ok:
                    self._failure(unit, "spec_rejected", order_index, attempts, tokens, last_error=why, member=helper,
                                  elapsed_s=round(time.monotonic() - t_unit, 1))
                    return "spec_rejected"
                # the helper's proof and everything after it must be redone
                j = members.index(helper)
                for m in members[j:]:
                    member_proofs.pop(m, None)
                    (proofs_dir / f"{m}.lean").unlink(missing_ok=True)
                i = j
                feedback = ""
                continue
            feedback = self.renderer.proof_feedback(pc.result)

        assert last_pc is not None
        status = "proved_modular" if last_pc.modular else "proved"
        gs = gate_summary
        rec = Record(
            id=unit.id, crate=self.crate, unit=unit.to_json(),
            spec_stmt="\n\n".join(member_specs[m] for m in members), spec_prop="\n\n".join(member_props.get(m, "") for m in members),
            proof="\n\n".join(f"-- {m}\n{member_proofs[m]}" for m in members), status=status,
            mutants={"total": int(gs.get("mutants_total") or 0), "distinguishable": int(gs.get("mutants_distinguishable") or 0)},
            precond_density=float(gs.get("precond_density") or 0.0), pbt_effective_runs=int(gs.get("effective_runs") or 0),
            axioms=list(last_pc.result.get("axioms", [])), attempts=attempts, tokens=tokens, arm=self.arm.name,
            order_index=order_index, examples_used=examples_used, member_specs=member_specs, member_proofs=member_proofs,
            extra={"opaque_ok": last_pc.result.get("opaque_ok"), "elapsed_s": round(time.monotonic() - t_unit, 1)})
        self.store.admit(rec)
        self.log.emit("unit_done", unit=unit.id, status=status, attempts=attempts, tokens=tokens,
                      elapsed_s=round(time.monotonic() - t_unit, 1))
        return status


def load_external(config: Config) -> list[Record]:
    d = config.external_corpus
    if d is None or not d.is_dir():
        return []
    out = []
    for f in sorted(d.glob("*.json")):
        out.append(Record.from_json(json.loads(f.read_text())))
    return out


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description="Bootstrapped few-shot spec/proof pipeline")
    ap.add_argument("--crate", default="corpus")
    ap.add_argument("--arm", default="A")
    ap.add_argument("--llm", default="anthropic", choices=["anthropic", "fake"])
    ap.add_argument("--fixtures", default=None, help="fake LLM fixture directory")
    ap.add_argument("--order-seed", type=int, default=None)
    ap.add_argument("--units", default=None, help="comma-separated unit ids to process (others skipped)")
    ap.add_argument("--limit", type=int, default=None)
    ap.add_argument("--resume", action="store_true")
    ap.add_argument("--run-dir", default=None)
    ap.add_argument("--config", default=None)
    ap.add_argument("--store-root", default=None, help="override paths.corpus_store (e.g. for smoke runs)")
    args = ap.parse_args(argv)

    config = load_config(Path(args.config) if args.config else None)
    if args.store_root:
        raw = json.loads(json.dumps(config.raw))
        raw["paths"]["corpus_store"] = str(Path(args.store_root).resolve())
        config = Config(raw=raw, root=config.root)
    arm = Arm(args.arm)
    if arm.name == "C" and not (config.corpus_store / args.crate / "A").exists():
        print("refusing to run arm C before arm A has been run on this crate (IMPLEMENTATION.md §7)", file=sys.stderr)
        return 2
    ts = datetime.now(UTC).strftime("%Y%m%dT%H%M%SZ")
    run_dir = (Path(args.run_dir) if args.run_dir else config.runs / args.crate / arm.name / ts).resolve()
    fixtures = Path(args.fixtures) if args.fixtures else config.root / "tests/fixtures/fake_llm"
    llm = make_llm(args.llm, config.llm, fixtures)
    external = load_external(config) if arm.uses_external else []
    pipe = Pipeline(config, args.crate, arm, llm, run_dir, order_seed=args.order_seed, resume=args.resume,
                    units_filter=args.units.split(",") if args.units else None, limit=args.limit, external=external)
    counts = pipe.run()
    print(json.dumps({"run_dir": str(run_dir), "counts": counts}))
    return 0


if __name__ == "__main__":
    sys.exit(main())
