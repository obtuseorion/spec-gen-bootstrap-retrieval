"""Corpus store: `corpus_store/<crate>/` — SQLite index, JSON records, spec files, failures, embeddings.

Layout (IMPLEMENTATION.md §2/§3):
    records/<id>.json      admitted records (status ∈ {proved, proved_modular})
    specs/<member>.lean    spec statement of every member of an admitted unit (`by sorry`),
                           read by the opaque re-check as callee specs
    failures/<id>.json     failure records
    corpus.sqlite          index mirroring the record (minus embedding)
    embeddings.npy / embeddings_ids.json   embedding vectors keyed by unit id (all units, cached)
    embedtexts.json        canonical text per unit id (cached `leantools embedtext` output)
"""

from __future__ import annotations

import json
import sqlite3
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

import numpy as np

ADMITTED = ("proved", "proved_modular")
FAILURE_STATUSES = ("spec_rejected", "proof_failed", "proof_blocked_by_callee", "skipped_generic", "skipped_divergent")

SCHEMA = """
CREATE TABLE IF NOT EXISTS records (
    id TEXT PRIMARY KEY,
    crate TEXT NOT NULL,
    status TEXT NOT NULL,
    kind TEXT,
    members TEXT,
    loops TEXT,
    callees TEXT,
    arg_type_heads TEXT,
    ret_type_head TEXT,
    called_consts TEXT,
    has_loop INTEGER,
    is_divergent INTEGER,
    is_generic INTEGER,
    spec_stmt TEXT,
    spec_prop TEXT,
    proof TEXT,
    mutants_total INTEGER,
    mutants_distinguishable INTEGER,
    precond_density REAL,
    pbt_effective_runs INTEGER,
    axioms TEXT,
    attempts_spec INTEGER,
    attempts_proof INTEGER,
    tokens_spec INTEGER,
    tokens_proof INTEGER,
    arm TEXT,
    order_index INTEGER,
    examples_spec TEXT,
    examples_proof TEXT
);
"""


@dataclass
class Record:
    """A corpus record (IMPLEMENTATION.md §3.2) or failure record (§3.3)."""
    id: str
    crate: str
    unit: dict[str, Any]
    spec_stmt: str
    spec_prop: str
    proof: str
    status: str
    mutants: dict[str, int] = field(default_factory=lambda: {"total": 0, "distinguishable": 0})
    precond_density: float = 0.0
    pbt_effective_runs: int = 0
    axioms: list[str] = field(default_factory=list)
    attempts: dict[str, int] = field(default_factory=lambda: {"spec": 0, "proof": 0})
    tokens: dict[str, int] = field(default_factory=lambda: {"spec": 0, "proof": 0})
    arm: str = "A"
    order_index: int = 0
    examples_used: dict[str, list[str]] = field(default_factory=lambda: {"spec": [], "proof": []})
    member_specs: dict[str, str] = field(default_factory=dict)
    member_proofs: dict[str, str] = field(default_factory=dict)
    blame: str | None = None
    last_error: str | None = None
    extra: dict[str, Any] = field(default_factory=dict)

    def to_json(self) -> dict[str, Any]:
        d = {k: v for k, v in self.__dict__.items() if k != "extra"}
        d.update(self.extra)
        return d

    @staticmethod
    def from_json(d: dict[str, Any]) -> Record:
        known = {k for k in Record.__dataclass_fields__ if k != "extra"}
        extra = {k: v for k, v in d.items() if k not in known}
        return Record(**{k: v for k, v in d.items() if k in known}, extra=extra)

    @property
    def signature(self) -> dict[str, Any]:
        return self.unit["signature"]


class CorpusStore:
    def __init__(self, root: Path, crate: str):
        self.crate = crate
        self.root = root / crate
        for sub in ("records", "specs", "failures"):
            (self.root / sub).mkdir(parents=True, exist_ok=True)
        self.db = sqlite3.connect(self.root / "corpus.sqlite")
        self.db.executescript(SCHEMA)
        self._embeddings: dict[str, np.ndarray] = {}
        self._embed_texts: dict[str, str] = {}
        self._load_embeddings()

    # ---- records ------------------------------------------------------------
    def record_path(self, unit_id: str) -> Path:
        return self.root / "records" / f"{unit_id}.json"

    def failure_path(self, unit_id: str) -> Path:
        return self.root / "failures" / f"{unit_id}.json"

    def spec_path(self, member: str) -> Path:
        return self.root / "specs" / f"{member}.lean"

    @property
    def specs_dir(self) -> Path:
        return self.root / "specs"

    def has_record(self, unit_id: str) -> bool:
        return self.record_path(unit_id).is_file()

    def has_failure(self, unit_id: str) -> bool:
        return self.failure_path(unit_id).is_file()

    def get(self, unit_id: str) -> Record | None:
        p = self.record_path(unit_id)
        return Record.from_json(json.loads(p.read_text())) if p.is_file() else None

    def get_failure(self, unit_id: str) -> Record | None:
        p = self.failure_path(unit_id)
        return Record.from_json(json.loads(p.read_text())) if p.is_file() else None

    def admit(self, rec: Record) -> None:
        """Write an admitted record: JSON, SQLite row and one spec file per member. Frozen thereafter."""
        if rec.status not in ADMITTED:
            raise ValueError(f"only proved/proved_modular records are admitted, got {rec.status}")
        self.record_path(rec.id).write_text(json.dumps(rec.to_json(), indent=1, sort_keys=True))
        for member, stmt in rec.member_specs.items():
            self.spec_path(member).write_text(stmt.rstrip() + "\n")
        self._upsert(rec)

    def fail(self, rec: Record) -> None:
        if rec.status not in FAILURE_STATUSES:
            raise ValueError(f"not a failure status: {rec.status}")
        self.failure_path(rec.id).write_text(json.dumps(rec.to_json(), indent=1, sort_keys=True))
        self._upsert(rec)

    def _upsert(self, rec: Record) -> None:
        sig = rec.signature
        u = rec.unit
        self.db.execute(
            "INSERT OR REPLACE INTO records VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
            (rec.id, rec.crate, rec.status, u.get("kind"), json.dumps(u.get("members", [])), json.dumps(u.get("loops", [])),
             json.dumps(u.get("callees", [])), json.dumps(sig["arg_type_heads"]), sig["ret_type_head"],
             json.dumps(sig["called_consts"]), int(sig["has_loop"]), int(u.get("is_divergent", False)),
             int(u.get("is_generic", False)), rec.spec_stmt, rec.spec_prop, rec.proof, rec.mutants.get("total", 0),
             rec.mutants.get("distinguishable", 0), rec.precond_density, rec.pbt_effective_runs, json.dumps(rec.axioms),
             rec.attempts.get("spec", 0), rec.attempts.get("proof", 0), rec.tokens.get("spec", 0), rec.tokens.get("proof", 0),
             rec.arm, rec.order_index, json.dumps(rec.examples_used.get("spec", [])), json.dumps(rec.examples_used.get("proof", []))))
        self.db.commit()

    def admitted(self, statuses: tuple[str, ...] = ADMITTED) -> list[Record]:
        rows = self.db.execute("SELECT id FROM records WHERE status IN (%s) ORDER BY order_index, id" % ",".join("?" * len(statuses)), statuses).fetchall()
        out = []
        for (uid,) in rows:
            r = self.get(uid)
            if r is not None:
                out.append(r)
        return out

    def statuses(self) -> dict[str, str]:
        return dict(self.db.execute("SELECT id, status FROM records").fetchall())

    # ---- embeddings ---------------------------------------------------------
    def _load_embeddings(self) -> None:
        ids = self.root / "embeddings_ids.json"
        vecs = self.root / "embeddings.npy"
        if ids.is_file() and vecs.is_file():
            names = json.loads(ids.read_text())
            arr = np.load(vecs)
            self._embeddings = {n: arr[i] for i, n in enumerate(names)}
        texts = self.root / "embedtexts.json"
        if texts.is_file():
            self._embed_texts = json.loads(texts.read_text())

    def embedding(self, unit_id: str) -> np.ndarray | None:
        return self._embeddings.get(unit_id)

    def embed_text(self, unit_id: str) -> str | None:
        return self._embed_texts.get(unit_id)

    def set_embed_text(self, unit_id: str, text: str) -> None:
        self._embed_texts[unit_id] = text
        (self.root / "embedtexts.json").write_text(json.dumps(self._embed_texts, indent=0, sort_keys=True))

    def set_embedding(self, unit_id: str, vec: np.ndarray) -> None:
        self._embeddings[unit_id] = np.asarray(vec, dtype=np.float32)
        self._save_embeddings()

    def _save_embeddings(self) -> None:
        names = sorted(self._embeddings)
        if not names:
            return
        arr = np.stack([self._embeddings[n] for n in names])
        np.save(self.root / "embeddings.npy", arr)
        (self.root / "embeddings_ids.json").write_text(json.dumps(names))
