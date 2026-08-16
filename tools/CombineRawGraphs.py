#!/usr/bin/env python3
"""Combine independently extracted Lean declaration graph slices.

Every slice is produced by `build_project_graph` from a smaller elaborated
environment.  Nodes are identified by their fully qualified Lean declaration
name, then receive stable graph ids only after the environments are combined.
This keeps the extractor below CI memory limits without inventing edges or
weakening the source-of-truth requirement.
"""

from __future__ import annotations

import json
import sys


def identity(node: dict) -> tuple[str, str]:
    return (node.get("namespace") or node.get("locator") or node["id"], node.get("kind", ""))


def main() -> None:
    slices = [json.load(open(path, encoding="utf-8")) for path in sys.argv[1:]]
    by_identity: dict[tuple[str, str], dict] = {}
    source_identity: dict[tuple[int, str], tuple[str, str]] = {}
    for slice_index, graph in enumerate(slices):
        for node in graph["nodes"]:
            key = identity(node)
            source_identity[(slice_index, node["id"])] = key
            by_identity.setdefault(key, node)

    ordered_keys = sorted(by_identity, key=lambda key: (key[0], key[1]))
    ids = {key: f"node-{index}" for index, key in enumerate(ordered_keys)}
    nodes = []
    for key in ordered_keys:
        node = dict(by_identity[key])
        node["id"] = ids[key]
        nodes.append(node)

    edges_by_identity: dict[tuple[str, str, str, str], dict] = {}
    for slice_index, graph in enumerate(slices):
        for edge in graph["edges"]:
            source_key = source_identity[(slice_index, edge["source"]["id"])]
            target_key = source_identity[(slice_index, edge["target"]["id"])]
            proof_key = source_identity.get((slice_index, edge.get("proof", "")))
            proof_id = ids[proof_key] if proof_key else ""
            key = (edge.get("relation", ""), ids[source_key], ids[target_key], proof_id)
            if key in edges_by_identity:
                continue
            combined = dict(edge)
            combined["id"] = f"use-{len(edges_by_identity)}"
            combined["proof"] = proof_id
            combined["source"] = {**edge["source"], "id": ids[source_key]}
            combined["target"] = {**edge["target"], "id": ids[target_key]}
            edges_by_identity[key] = combined

    # Each slice intentionally has a one-layer overlap. Reconstruct the
    # original project-wide frontier from the union of MathNetwork targets,
    # rather than accepting a target order local to one slice as the global
    # depth. Edges point prerequisite -> proof target, so this is an upstream
    # breadth-first walk.
    roots = {node["id"] for node in nodes
             if node.get("namespace", "").startswith("MathNetwork.") and not node.get("locator")}
    incoming: dict[str, list[str]] = {}
    for edge in edges_by_identity.values():
        incoming.setdefault(edge["target"]["id"], []).append(edge["source"]["id"])
    distances = {node_id: 0 for node_id in roots}
    frontier = list(roots)
    for depth in range(1, 4):
        next_frontier = []
        for target_id in frontier:
            for source_id in incoming.get(target_id, []):
                if source_id not in distances:
                    distances[source_id] = depth
                    next_frontier.append(source_id)
        frontier = next_frontier
    allowed = set(distances)
    nodes = [node for node in nodes if node["id"] in allowed]
    for node in nodes:
        # Slice-local discovery depth is not meaningful after the union. The
        # inspector's expansion affordance must reflect the global frontier.
        if node["id"] in distances and node.get("locator"):
            depth = distances[node["id"]]
            node["dependencyDepth"] = depth
            node["dependencyBoundary"] = depth >= 3 or node.get("role") == "structure"
    combined_edges = [edge for edge in edges_by_identity.values()
                      if edge["source"]["id"] in allowed and edge["target"]["id"] in allowed]

    json.dump({
        "schemaVersion": "1.0",
        "graphId": "math-net-project-declarations",
        "label": "math-net: Lean declaration dependencies",
        "nodes": nodes,
        "edges": combined_edges,
    }, sys.stdout, separators=(",", ":"))


if __name__ == "__main__":
    main()
