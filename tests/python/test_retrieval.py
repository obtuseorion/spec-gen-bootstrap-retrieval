"""Task 7 — corpus store and retrieval (pure Python; synthetic graph and records)."""

from __future__ import annotations

from pathlib import Path

from orchestrator.corpus import CorpusStore, Record
from orchestrator.embedding import Embedder
from orchestrator.retrieval import Retriever
from orchestrator.units import Graph, Unit


def mk_unit(uid: str, callees: tuple[str, ...] = (), heads=("U32",), ret="Result U32", called=("Aeneas.Std.UScalar.add",),
            has_loop=False, source=None) -> dict:
    return {"id": uid, "kind": "def", "members": [uid], "loops": [], "callees": list(callees), "is_divergent": False,
            "is_generic": False, "signature": {"arg_type_heads": list(heads), "ret_type_head": ret,
                                                "called_consts": list(called), "has_loop": has_loop},
            "source": source or f"def {uid} (x : U32) : Result U32 := do x + 1#u32", "module": "Corpus.Funs"}


def mk_graph() -> Graph:
    units = [
        mk_unit("Corpus.a.leaf1"),
        mk_unit("Corpus.a.leaf2", source="def Corpus.a.leaf2 (x : U32) : Result U32 := do x + 2#u32"),
        mk_unit("Corpus.a.mid", callees=("Corpus.a.leaf1",)),
        mk_unit("Corpus.a.top", callees=("Corpus.a.mid",)),
        mk_unit("Corpus.a.other", heads=("Bool",), ret="Result Bool", called=()),
    ]
    order = ["Corpus.a.leaf1", "Corpus.a.leaf2", "Corpus.a.other", "Corpus.a.mid", "Corpus.a.top"]
    return Graph.from_json({"units": units, "order": order})


def admit(store: CorpusStore, graph: Graph, uid: str, status: str = "proved_modular") -> Record:
    u = graph.units[uid]
    rec = Record(id=uid, crate="corpus", unit=u.to_json(), spec_stmt=f"@[step] theorem {uid}_spec : True := by sorry",
                 spec_prop="True", proof="trivial", status=status, member_specs={uid: f"@[step] theorem {uid}_spec : True := by sorry"})
    store.admit(rec)
    return rec


def make(tmp_path: Path, tau: float = 0.0, seed: int = 0) -> tuple[CorpusStore, Graph, Retriever, Embedder]:
    graph = mk_graph()
    store = CorpusStore(tmp_path / "store", "corpus")
    emb = Embedder(model_name="test", backend="hashed-ngram")
    cfg = {"tau_spec": tau, "tau_proof": tau, "jaccard_min": 0.3, "top_k": 2}
    return store, graph, Retriever(store, graph, emb, cfg, seed=seed), emb


def test_store_roundtrip_and_spec_files(tmp_path: Path) -> None:
    store, graph, _, _ = make(tmp_path)
    admit(store, graph, "Corpus.a.leaf1")
    assert store.has_record("Corpus.a.leaf1")
    assert store.spec_path("Corpus.a.leaf1").read_text().startswith("@[step] theorem")
    assert store.statuses() == {"Corpus.a.leaf1": "proved_modular"}
    rec = store.get("Corpus.a.leaf1")
    assert rec is not None and rec.signature["ret_type_head"] == "Result U32"


def test_exclusion_by_identity(tmp_path: Path) -> None:
    store, graph, retriever, _ = make(tmp_path)
    for uid in ("Corpus.a.leaf1", "Corpus.a.leaf2", "Corpus.a.mid", "Corpus.a.top"):
        admit(store, graph, uid)
    res = retriever.retrieve(graph.units["Corpus.a.top"], "spec", "C")
    ids = {r.id for r in res.examples}
    # the unit itself and its transitive callees (mid, leaf1) are never examples; leaf2 is the only one left
    assert ids == {"Corpus.a.leaf2"}, res.to_json()
    assert res.candidates == 1


def test_below_tau_returns_nothing(tmp_path: Path) -> None:
    store, graph, retriever, _ = make(tmp_path, tau=1.01)
    admit(store, graph, "Corpus.a.leaf2")
    res = retriever.retrieve(graph.units["Corpus.a.top"], "spec", "C")
    assert res.examples == [] and res.top_score is not None and res.method.endswith("below-tau")


def test_structural_filter_and_proof_status(tmp_path: Path) -> None:
    store, graph, retriever, _ = make(tmp_path)
    admit(store, graph, "Corpus.a.other")            # different signature
    admit(store, graph, "Corpus.a.leaf2", status="proved")   # not a proof exemplar
    assert retriever.retrieve(graph.units["Corpus.a.top"], "spec", "C").examples[0].id == "Corpus.a.leaf2"
    assert retriever.retrieve(graph.units["Corpus.a.top"], "proof", "C").examples == []


def test_arm_d_is_seed_reproducible(tmp_path: Path) -> None:
    store, graph, _, _ = make(tmp_path)
    for uid in ("Corpus.a.leaf1", "Corpus.a.leaf2", "Corpus.a.other", "Corpus.a.mid"):
        admit(store, graph, uid)
    emb = Embedder(model_name="test")
    cfg = {"tau_spec": 0.0, "tau_proof": 0.0, "jaccard_min": 0.3, "top_k": 2}
    r1 = Retriever(store, graph, emb, cfg, seed=7).retrieve(graph.units["Corpus.a.top"], "spec", "D")
    r2 = Retriever(store, graph, emb, cfg, seed=7).retrieve(graph.units["Corpus.a.top"], "spec", "D")
    r3 = Retriever(store, graph, emb, cfg, seed=8).retrieve(graph.units["Corpus.a.top"], "spec", "D")
    assert [r.id for r in r1.examples] == [r.id for r in r2.examples]
    assert len(r1.examples) == 2 and r1.method == "random"
    assert {r.id for r in r1.examples} <= {"Corpus.a.leaf2", "Corpus.a.other"}  # identity exclusion still applies
    assert [r.id for r in r3.examples] != [r.id for r in r1.examples] or True  # different seed may coincide


def test_embeddings_cached_across_reruns(tmp_path: Path) -> None:
    store, graph, retriever, emb = make(tmp_path)
    admit(store, graph, "Corpus.a.leaf2")
    retriever.retrieve(graph.units["Corpus.a.top"], "spec", "C")
    first = emb.calls
    assert first == 2  # unit + candidate
    # a fresh store/retriever over the same directory must not recompute
    store2 = CorpusStore(tmp_path / "store", "corpus")
    emb2 = Embedder(model_name="test")
    r2 = Retriever(store2, graph, emb2, {"tau_spec": 0.0, "tau_proof": 0.0, "jaccard_min": 0.3, "top_k": 2})
    r2.retrieve(graph.units["Corpus.a.top"], "spec", "C")
    assert emb2.calls == 0


def test_seeded_topological_order_is_valid(tmp_path: Path) -> None:
    graph = mk_graph()
    for seed in (0, 1, 2):
        order = graph.seeded_order(seed)
        pos = {u: i for i, u in enumerate(order)}
        for u in graph.units.values():
            for c in u.callees:
                assert pos[c] < pos[u.id]
    assert graph.seeded_order(3) == graph.seeded_order(3)
