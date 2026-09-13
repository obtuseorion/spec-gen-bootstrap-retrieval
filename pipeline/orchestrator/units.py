"""Units: load the dependency graph (`leantools graph`), build Unit objects, order them.

The graph JSON is cached at `corpus_store/<crate>/graph.json`; `--order-seed`
draws a different valid topological order (callees still first).
"""

from __future__ import annotations

import json
import random
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from orchestrator.config import Config
from orchestrator.leantools import LeanTools


@dataclass(frozen=True)
class Signature:
    arg_type_heads: tuple[str, ...]
    ret_type_head: str
    called_consts: tuple[str, ...]
    has_loop: bool

    @staticmethod
    def from_json(d: dict[str, Any]) -> Signature:
        return Signature(tuple(d["arg_type_heads"]), d["ret_type_head"], tuple(d["called_consts"]), bool(d["has_loop"]))

    def to_json(self) -> dict[str, Any]:
        return {"arg_type_heads": list(self.arg_type_heads), "ret_type_head": self.ret_type_head,
                "called_consts": list(self.called_consts), "has_loop": self.has_loop}


@dataclass(frozen=True)
class Unit:
    id: str
    kind: str
    members: tuple[str, ...]
    loops: tuple[str, ...]
    callees: tuple[str, ...]
    is_divergent: bool
    is_generic: bool
    signature: Signature
    source: str
    module: str = ""

    @property
    def all_members(self) -> tuple[str, ...]:
        """Members followed by loop helpers, in a stable order (the tools sort by source position)."""
        return tuple(self.members) + tuple(self.loops)

    @staticmethod
    def from_json(d: dict[str, Any]) -> Unit:
        return Unit(id=d["id"], kind=d["kind"], members=tuple(d["members"]), loops=tuple(d["loops"]),
                    callees=tuple(d["callees"]), is_divergent=bool(d["is_divergent"]), is_generic=bool(d["is_generic"]),
                    signature=Signature.from_json(d["signature"]), source=d["source"], module=d.get("module", ""))

    def to_json(self) -> dict[str, Any]:
        return {"id": self.id, "kind": self.kind, "members": list(self.members), "loops": list(self.loops),
                "callees": list(self.callees), "is_divergent": self.is_divergent, "is_generic": self.is_generic,
                "signature": self.signature.to_json(), "source": self.source, "module": self.module}


@dataclass
class Graph:
    units: dict[str, Unit]
    order: list[str]
    warnings: list[str] = field(default_factory=list)

    @staticmethod
    def from_json(d: dict[str, Any]) -> Graph:
        units = {u["id"]: Unit.from_json(u) for u in d["units"]}
        return Graph(units=units, order=list(d["order"]), warnings=list(d.get("warnings", [])))

    def transitive_callees(self, unit_id: str) -> set[str]:
        seen: set[str] = set()
        stack = list(self.units[unit_id].callees)
        while stack:
            c = stack.pop()
            if c in seen:
                continue
            seen.add(c)
            stack.extend(self.units[c].callees)
        return seen

    def member_to_unit(self) -> dict[str, str]:
        return {m: u.id for u in self.units.values() for m in u.all_members}

    def seeded_order(self, seed: int | None) -> list[str]:
        """A valid topological order (callees first); `None` keeps the tool's deterministic order."""
        if seed is None:
            return list(self.order)
        rng = random.Random(seed)
        indeg = {uid: 0 for uid in self.units}
        callers: dict[str, list[str]] = {uid: [] for uid in self.units}
        for u in self.units.values():
            for c in u.callees:
                indeg[u.id] += 1
                callers[c].append(u.id)
        ready = sorted(uid for uid, d in indeg.items() if d == 0)
        out: list[str] = []
        while ready:
            i = rng.randrange(len(ready))
            uid = ready.pop(i)
            out.append(uid)
            for caller in sorted(callers[uid]):
                indeg[caller] -= 1
                if indeg[caller] == 0:
                    ready.append(caller)
        if len(out) != len(self.units):
            raise RuntimeError("dependency graph has a cycle at unit level")
        return out


def load_graph(config: Config, tools: LeanTools, crate: str, refresh: bool = False) -> Graph:
    cache = config.corpus_store / crate / "graph.json"
    if cache.is_file() and not refresh:
        return Graph.from_json(json.loads(cache.read_text()))
    out = tools.graph()
    if "error" in out:
        raise RuntimeError(f"leantools graph failed: {out['error']}")
    cache.parent.mkdir(parents=True, exist_ok=True)
    cache.write_text(json.dumps(out, indent=1))
    return Graph.from_json(out)
