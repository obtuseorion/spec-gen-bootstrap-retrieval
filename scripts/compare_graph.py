#!/usr/bin/env python3
"""Compare `leantools graph` output with the ground-truth `corpus/graph.json`.

Usage: scripts/compare_graph.py <graph-output.json> <corpus/graph.json>

Exit 0 when every difference falls into an explained category, 1 otherwise.
The categories are documented in docs/phase0.md and in `explain()` below.
"""

from __future__ import annotations

import json
import sys
from collections import Counter, defaultdict

# Modules that do not translate with the available Aeneas release (docs/phase0.md, deviation 2).
EXCLUDED_MODULES = {
    "issue_1140_global_loop",
    "issue_1260_eliminate_shared_loans",
    "issue_1138_slice_positivity",
    "constants_lean",
    "lean_keywords",
    "lean_keywords_clash",
}


def truth_units(truth: dict) -> tuple[dict[str, dict], dict[str, str]]:
    """Ground-truth function nodes keyed by Lean name, plus loop_aux → parent Lean name."""
    by_id = {n["id"]: n for n in truth["nodes"]}
    fns: dict[str, dict] = {}
    loop_parent: dict[str, str] = {}
    for n in truth["nodes"]:
        if "lean" not in n["in"]:
            continue
        if n["kind"] == "fn":
            fns["Corpus." + n["lean_name"]] = n
        elif n["kind"] == "loop_aux":
            parent = by_id.get(n["parent"])
            if parent is not None:
                loop_parent["Corpus." + n["lean_name"]] = "Corpus." + parent["lean_name"]
    return fns, loop_parent


def module_of(node: dict) -> str:
    return node["module"].split("::")[0]


def explain(name: str, truth_node: dict | None, ours: dict[str, dict], truth_fns: dict[str, dict]) -> str:
    """Categorise a node-set difference. Returns "" when unexplained."""
    if truth_node is not None:
        if module_of(truth_node) in EXCLUDED_MODULES:
            return "excluded-module"
        # Trait method declarations are structure fields in Lean (not `def`s returning Result).
        if truth_node["id"].count("::") >= 2 and "{" not in truth_node["id"] and truth_node["id"].split("::")[-2][:1].isupper():
            return "trait-method-decl"
    if name.endswith(".body"):
        return "loop-body-helper"
    if truth_node is None and name in GLOBALS:
        return "global-const"
    return ""


GLOBALS: set[str] = set()


def main() -> int:
    ours_raw = json.load(open(sys.argv[1]))
    truth = json.load(open(sys.argv[2]))
    GLOBALS.update("Corpus." + n["lean_name"] for n in truth["nodes"] if n["kind"] == "const")
    units = ours_raw["units"]
    truth_fns, truth_loop_parent = truth_units(truth)

    # ---- node sets -------------------------------------------------------------
    our_nodes: dict[str, dict] = {}
    our_family: dict[str, str] = {}  # member or loop → unit id
    for u in units:
        for m in u["members"]:
            our_nodes[m] = u
            our_family[m] = u["id"]
        for l in u["loops"]:
            our_nodes[l] = u
            our_family[l] = u["id"]
    truth_nodes = set(truth_fns) | set(truth_loop_parent)

    only_truth = sorted(truth_nodes - set(our_nodes))
    only_ours = sorted(set(our_nodes) - truth_nodes)
    cats_truth = Counter()
    unexplained: list[str] = []
    for n in only_truth:
        tn = truth_fns.get(n)
        if tn is None:  # loop_aux
            tn = next((x for x in truth["nodes"] if x["kind"] == "loop_aux" and "Corpus." + x["lean_name"] == n), None)
        c = explain(n, tn, our_nodes, truth_fns)
        cats_truth[c or "UNEXPLAINED"] += 1
        if not c:
            unexplained.append(f"only in graph.json: {n}")
    cats_ours = Counter()
    for n in only_ours:
        c = explain(n, None, our_nodes, truth_fns)
        cats_ours[c or "UNEXPLAINED"] += 1
        if not c:
            unexplained.append(f"only in leantools: {n}")

    # ---- loop attachment --------------------------------------------------------
    loop_mismatch = []
    for loop, parent in truth_loop_parent.items():
        if loop in our_nodes and parent in our_nodes and our_family[loop] != our_family[parent]:
            loop_mismatch.append((loop, parent, our_family[loop]))

    # ---- edges (family level) ---------------------------------------------------
    truth_lean_name = {n["id"]: "Corpus." + n["lean_name"] for n in truth["nodes"] if "lean" in n["in"]}
    truth_lean_name_by_id = truth_lean_name

    def truth_fam(name: str) -> str | None:
        name = truth_loop_parent.get(name, name)
        return our_family.get(name)

    truth_edges = set()
    for e in truth["edges"]:
        if "lean" not in e["in"]:
            continue
        a, b = truth_lean_name.get(e["from"]), truth_lean_name.get(e["to"])
        if a is None or b is None or a not in truth_nodes or b not in truth_nodes:
            continue
        fa, fb = truth_fam(a), truth_fam(b)
        if fa and fb and fa != fb:
            truth_edges.add((fa, fb))
    our_edges = {(u["id"], c) for u in units for c in u["callees"]}
    only_truth_e = sorted(truth_edges - our_edges)
    # Explained extra edges: (a) an endpoint is a global constant (graph.json has no
    # fn→const edges); (b) trait dispatch: we resolve `Trait.method inst x` through the
    # instance structure to the implementing method, graph.json stops at the trait_impl node.
    lean_to_id = {"Corpus." + n["lean_name"]: n["id"] for n in truth["nodes"] if "lean" in n["in"]}
    truth_raw_edges = {(e["from"], e["to"]) for e in truth["edges"]}
    impl_of = {n["id"]: n for n in truth["nodes"] if n["kind"] == "trait_impl"}

    def explain_edge(a: str, b: str) -> str:
        if a in GLOBALS or b in GLOBALS:
            return "edge-to-global"
        if ".Insts." in b:
            inst_lean = b.split(".Insts.")[0] + ".Insts." + b.split(".Insts.")[1].split(".")[0]
            impl_id = lean_to_id.get(inst_lean)
            if impl_id in impl_of and (lean_to_id.get(a), impl_id) in truth_raw_edges:
                return "edge-via-trait-impl"
            # the caller may itself be a loop/member whose family we contracted
            for fam_member in [m for m, f in our_family.items() if f == a]:
                if (lean_to_id.get(fam_member), impl_id) in truth_raw_edges:
                    return "edge-via-trait-impl"
        return ""

    edge_cats = Counter()
    only_ours_e = []
    for e in sorted(our_edges - truth_edges):
        c = explain_edge(*e)
        edge_cats[c or "UNEXPLAINED"] += 1
        if not c:
            only_ours_e.append(e)
    # SCCs: graph.json lists non-trivial SCCs by rust id
    truth_sccs = {frozenset(truth_lean_name_by_id[i] for i in scc if i in truth_lean_name_by_id)
                  for scc in truth.get("sccs", [])}
    truth_sccs = {s for s in truth_sccs if len(s) > 1 and not any(n not in our_nodes for n in s)}
    our_sccs = {frozenset(u["members"]) for u in units if u["kind"] == "scc"}
    scc_only_truth = truth_sccs - our_sccs
    scc_only_ours = our_sccs - truth_sccs

    # ---- order validity ---------------------------------------------------------
    pos = {uid: i for i, uid in enumerate(ours_raw["order"])}
    order_violations = [(u["id"], c) for u in units for c in u["callees"] if pos[c] > pos[u["id"]]]

    # ---- report -----------------------------------------------------------------
    print(f"leantools: {len(units)} units, {len(our_nodes)} nodes; graph.json: {len(truth_nodes)} fn+loop nodes")
    print(f"kinds: {Counter(u['kind'] for u in units)}; divergent: {sum(u['is_divergent'] for u in units)}; generic: {sum(u['is_generic'] for u in units)}; with loops: {sum(u['signature']['has_loop'] for u in units)}")
    print(f"only in graph.json: {len(only_truth)} {dict(cats_truth)}")
    print(f"only in leantools:  {len(only_ours)} {dict(cats_ours)}")
    print(f"loop attachment mismatches: {len(loop_mismatch)}")
    for m in loop_mismatch[:10]:
        print("   ", m)
    print(f"edges: truth {len(truth_edges)}, ours {len(our_edges)}, only truth {len(only_truth_e)}, extra ours {dict(edge_cats)}")
    print(f"sccs: truth (translatable) {len(truth_sccs)}, ours {len(our_sccs)}, only truth {len(scc_only_truth)}, only ours {len(scc_only_ours)}")
    for sc in list(scc_only_truth)[:5]: print("   scc only truth:", sorted(sc))
    for sc in list(scc_only_ours)[:5]: print("   scc only ours:", sorted(sc))
    for e in only_truth_e[:15]:
        print("   only truth:", e)
    for e in only_ours_e[:15]:
        print("   only ours: ", e)
    print(f"order violations (callee after caller): {len(order_violations)}")
    print(f"warnings from leantools: {len(ours_raw.get('warnings', []))}")
    for w in ours_raw.get("warnings", [])[:10]:
        print("   ", w)
    for u in unexplained[:30]:
        print("  ", u)
    ok = (not unexplained and not loop_mismatch and not order_violations and not only_truth_e
          and not only_ours_e and not scc_only_truth and not scc_only_ours)
    print("RESULT:", "OK" if ok else "DIFFERENCES REMAIN")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
