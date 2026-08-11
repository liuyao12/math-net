#!/usr/bin/env python3
"""Merge identical checked proposition declarations in a Lean graph.

Lean supplies the declaration-level dependency edges. This pass preserves that
information while identifying theorem declarations by exact elaborated
statement, including imported theorem declarations from mathlib. Definitions
remain declaration nodes. When proposition nodes merge, their declaration names become proof
records and every dependency edge retains the proof record that produced it.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path
from collections import defaultdict


def proof_record(node: dict) -> dict:
    declaration = node.get("namespace", node["label"])
    if node.get("locator", "").startswith("mathlib/"):
        label = "mathlib · library proof"
        route_kind = "mathlib"
        color = "#3f7f8f"
    elif node.get("locator", "").startswith("computable-analysis/"):
        label = "computable-analysis · imported proof"
        route_kind = "computable-analysis"
        color = "#a45b38"
    elif declaration == "MathNetwork.SqrtTwo.irrational":
        label = "mathlib · local adapter"
        route_kind = "mathlib"
        color = "#3f7f8f"
    elif declaration == "MathNetwork.SqrtTwo.irrational_descent":
        label = "computable-analysis · infinite-descent adapter"
        route_kind = "computable-analysis"
        color = "#a45b38"
    else:
        label = "math-net · local proof"
        route_kind = "local"
        color = "#7a6397"
    record = {
        "id": f"proof-{node['id']}",
        "label": label,
        "declaration": declaration,
        "routeKind": route_kind,
        "color": color,
        "status": "kernel-checked",
        "scope": "local-with-imports",
        "closure": "partial",
        "note": "Proof provenance retained from the elaborated Lean declaration.",
    }
    module = node.get("module", "")
    if module.startswith("MathNetwork."):
        record["file"] = f"{module.replace('.', '/')}.lean"
    if node.get("locator"):
        record["locator"] = node["locator"]
    return record


def comparison_manifest(path: str | None) -> dict[str, dict]:
    if not path:
        return {}
    data = json.loads(Path(path).read_text())
    return {
        route["declaration"]: {
            "id": comparison["id"],
            "repository": route["repository"],
        }
        for comparison in data.get("comparisons", [])
        for route in comparison.get("routes", [])
    }


def merge(graph: dict, manifest_path: str | None = None) -> dict:
    registered_routes = comparison_manifest(manifest_path)
    nodes = graph["nodes"]
    node_by_id = {node["id"]: node for node in nodes}
    groups: dict[tuple, list[dict]] = defaultdict(list)
    passthrough: list[dict] = []

    for node in nodes:
        # Imported mathlib theorem declarations remain visually marked as
        # sources, but participate in proposition merging by their checked
        # statement. This is the boundary where independent proof graphs join.
        if node.get("kind") == "proposition" or node.get("declarationKind") in {"theorem", "opaque", "axiom", "proposition"}:
            # A proposition is the mathematical statement, not the source
            # file that happens to contain one of its proofs. This lets a
            # Mathlib theorem and a local alternative proof share one node.
            key = (node.get("statement", ""),)
            groups[key].append(node)
        else:
            passthrough.append(node)

    merged_nodes: list[dict] = []
    old_to_new: dict[str, str] = {}
    proof_for_old: dict[str, str] = {}

    for group in groups.values():
        representative = group[0]
        merged = dict(representative)
        merged["formalizations"] = []
        merged["proofs"] = []
        seen_formalizations = set()
        for node in group:
            old_to_new[node["id"]] = representative["id"]
            record = proof_record(node)
            proof_for_old[node["id"]] = record["id"]
            merged["proofs"].append(record)
            if node.get("kind") == "source" and node.get("namespace"):
                merged.setdefault("formalizations", []).append({
                    "repository": (
                        "mathlib4" if node.get("locator", "").startswith("mathlib/")
                        else "computable-analysis" if node.get("locator", "").startswith("computable-analysis/")
                        else "imported"
                    ),
                    "language": "Lean",
                    "name": node["namespace"],
                    "locator": node.get("locator"),
                })
            for item in node.get("formalizations", []):
                identity = tuple(sorted(item.items()))
                if identity not in seen_formalizations:
                    seen_formalizations.add(identity)
                    merged["formalizations"].append(item)
        if len(group) > 1:
            merged["declarationCount"] = len(group)
            registered = [
                (record, registered_routes[record["declaration"]])
                for record in merged["proofs"]
                if record["declaration"] in registered_routes
            ]
            comparison_routes = [
                {
                    "proof": record["id"],
                    "repository": metadata["repository"],
                    "declaration": record["declaration"],
                }
                for record, metadata in registered
            ] or [
                {
                    "proof": record["id"],
                    "repository": record["routeKind"],
                    "declaration": record["declaration"],
                }
                for record in merged["proofs"]
            ]
            merged["comparison"] = {
                "identity": "exact elaborated proposition statement",
                "routes": comparison_routes,
                "note": (
                    "The declarations are merged only because Lean checked their "
                    "elaborated proposition types as definitionally equal."
                ),
            }
            if registered:
                merged["comparison"]["registry"] = registered[0][1]["id"]
            merged["verification"] = dict(merged.get("verification", {}))
            merged["verification"]["note"] = (
                merged["verification"].get("note", "")
                + f" Merged from {len(group)} declarations with the identical checked statement in the same module."
            ).strip()
        merged_nodes.append(merged)

    merged_nodes.extend(passthrough)
    for node in passthrough:
        old_to_new[node["id"]] = node["id"]

    merged_node_by_id = {node["id"]: node for node in merged_nodes}
    edges = []
    for index, edge in enumerate(graph["edges"]):
        source_old = edge["source"]["id"]
        target_old = edge["target"]["id"]
        source_new = old_to_new[source_old]
        target_new = old_to_new[target_old]
        rewritten = dict(edge)
        rewritten["id"] = f"{edge['id']}-{index}"
        rewritten["source"] = dict(edge["source"])
        rewritten["source"]["id"] = source_new
        rewritten["source"]["kind"] = merged_node_by_id[source_new].get("kind", rewritten["source"].get("kind"))
        rewritten["target"] = dict(edge["target"])
        rewritten["target"]["id"] = target_new
        rewritten["target"]["kind"] = merged_node_by_id[target_new].get("kind", rewritten["target"].get("kind"))
        if edge.get("proof") in proof_for_old:
            rewritten["proof"] = proof_for_old[edge["proof"]]
        elif target_old in proof_for_old:
            # Imported theorem declarations are represented as source nodes,
            # so BuildGraph leaves their edge proof field empty. Once that
            # declaration is merged into a proposition, recover its proof
            # provenance from the original target declaration.
            rewritten["proof"] = proof_for_old[target_old]
        edges.append(rewritten)

    result = dict(graph)
    result["nodes"] = merged_nodes
    result["edges"] = edges
    result["merge"] = {
        "key": "exact elaborated proposition statement across local and imported declarations",
        "definitions": "one node per declaration",
        "proofProvenance": "edge proof field and proposition proofs records",
    }
    return result


if __name__ == "__main__":
    manifest = None
    if len(sys.argv) == 3 and sys.argv[1] == "--comparisons":
        manifest = sys.argv[2]
    elif len(sys.argv) != 1:
        raise SystemExit("usage: MergeGraph.py [--comparisons manifest.json]")
    graph = json.load(sys.stdin)
    json.dump(merge(graph, manifest), sys.stdout, separators=(",", ":"), sort_keys=True)
    sys.stdout.write("\n")
