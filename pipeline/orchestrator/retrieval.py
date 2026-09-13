"""Retrieval of few-shot examples from the corpus (IMPLEMENTATION.md Task 7).

    retrieve(unit, stage, arm):
      1. candidates = records with the stage's allowed status, minus the unit,
         minus its transitive callees (by identity)
      2. structural filter (spec: arg-type-head multiset and return-type head equal;
         proof: additionally has_loop / is_divergent equal and Jaccard(called_consts) ≥ jaccard_min)
      3. score = cosine of the embeddings of the canonical definition texts
      4. top-k if score[0] ≥ τ[stage] else []
    Arm D replaces 2–4 with a seeded uniform draw of k from step 1.
    Arm F ranks by Jaccard instead of embeddings.
    Arms B/E add records from the external corpus directory to the candidate set.
"""

from __future__ import annotations

import random
from collections import Counter
from dataclasses import dataclass, field
from typing import Any

from orchestrator.corpus import ADMITTED, CorpusStore, Record
from orchestrator.embedding import Embedder, cosine
from orchestrator.units import Graph, Unit

SPEC_STATUSES = ("proved", "proved_modular")
PROOF_STATUSES = ("proved_modular",)


@dataclass
class RetrievalResult:
    examples: list[Record]
    scores: list[float]
    candidates: int
    filtered: int
    top_score: float | None
    method: str
    external_ids: list[str] = field(default_factory=list)

    def to_json(self) -> dict[str, Any]:
        return {"examples": [r.id for r in self.examples], "scores": self.scores, "candidates": self.candidates,
                "filtered": self.filtered, "top_score": self.top_score, "method": self.method}


def jaccard(a: tuple[str, ...] | list[str], b: tuple[str, ...] | list[str]) -> float:
    sa, sb = set(a), set(b)
    if not sa and not sb:
        return 1.0
    return len(sa & sb) / len(sa | sb)


def structural_ok(unit: Unit, rec: Record, stage: str, jaccard_min: float) -> bool:
    sig = rec.signature
    if Counter(unit.signature.arg_type_heads) != Counter(sig["arg_type_heads"]):
        return False
    if unit.signature.ret_type_head != sig["ret_type_head"]:
        return False
    if stage == "proof":
        if bool(sig["has_loop"]) != unit.signature.has_loop:
            return False
        if bool(rec.unit.get("is_divergent", False)) != unit.is_divergent:
            return False
        if jaccard(unit.signature.called_consts, sig["called_consts"]) < jaccard_min:
            return False
    return True


class Retriever:
    def __init__(self, store: CorpusStore, graph: Graph, embedder: Embedder, config: dict[str, Any],
                 external: list[Record] | None = None, seed: int = 0, embed_text_fn=None):
        self.store = store
        self.graph = graph
        self.embedder = embedder
        self.cfg = config
        self.external = external or []
        self.rng = random.Random(seed)
        self.embed_text_fn = embed_text_fn  # unit id -> canonical text (leantools embedtext), cached in the store

    # ---- embeddings, cached in the store ----------------------------------
    def embedding(self, unit_id: str):
        vec = self.store.embedding(unit_id)
        if vec is not None:
            return vec
        text = self.store.embed_text(unit_id)
        if text is None:
            if self.embed_text_fn is None:
                text = self.graph.units[unit_id].source if unit_id in self.graph.units else unit_id
            else:
                text = self.embed_text_fn(unit_id)
            self.store.set_embed_text(unit_id, text)
        vec = self.embedder.embed(text)
        self.store.set_embedding(unit_id, vec)
        return vec

    def _record_embedding(self, rec: Record):
        if rec.crate == self.store.crate:
            return self.embedding(rec.id)
        # external record: embed its stored text (cached under a namespaced id)
        key = f"external:{rec.id}"
        vec = self.store.embedding(key)
        if vec is None:
            text = rec.extra.get("embed_text") or rec.unit.get("source", rec.id)
            vec = self.embedder.embed(text)
            self.store.set_embedding(key, vec)
        return vec

    # ---- main entry ---------------------------------------------------------
    def retrieve(self, unit: Unit, stage: str, arm: str) -> RetrievalResult:
        k = int(self.cfg.get("top_k", 2))
        statuses = SPEC_STATUSES if stage == "spec" else PROOF_STATUSES
        if arm == "A":
            return RetrievalResult([], [], 0, 0, None, "none")
        excluded = {unit.id} | self.graph.transitive_callees(unit.id)
        candidates: list[Record] = []
        if arm != "B":
            candidates += [r for r in self.store.admitted(statuses) if r.id not in excluded]
        if arm in ("B", "E"):
            candidates += [r for r in self.external if r.status in statuses]
        n_candidates = len(candidates)
        if arm == "D":
            chosen = self.rng.sample(candidates, min(k, len(candidates))) if candidates else []
            return RetrievalResult(chosen, [1.0] * len(chosen), n_candidates, n_candidates, None, "random")
        jmin = float(self.cfg.get("jaccard_min", 0.3))
        filtered = [r for r in candidates if structural_ok(unit, r, stage, jmin)]
        if not filtered:
            return RetrievalResult([], [], n_candidates, 0, None, "structural-empty")
        if arm == "F":
            scored = [(jaccard(unit.signature.called_consts, r.signature["called_consts"]), r) for r in filtered]
            method = "jaccard"
        else:
            uvec = self.embedding(unit.id)
            scored = [(cosine(uvec, self._record_embedding(r)), r) for r in filtered]
            method = "embedding"
        scored.sort(key=lambda t: (-t[0], t[1].id))
        tau = float(self.cfg.get(f"tau_{stage}", 0.0))
        top = scored[0][0]
        if top < tau:
            return RetrievalResult([], [], n_candidates, len(filtered), top, method + "-below-tau")
        chosen = scored[:k]
        return RetrievalResult([r for _, r in chosen], [s for s, _ in chosen], n_candidates, len(filtered), top, method,
                               external_ids=[r.id for _, r in chosen if r.crate != self.store.crate])
