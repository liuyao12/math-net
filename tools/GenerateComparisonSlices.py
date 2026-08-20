#!/usr/bin/env python3
"""Emit small upstream dependency graphs for individual comparison views.

The complete project graph remains the authoritative graph.  These slices are
only a fast first view: they contain the selected proposition and five actual
Lean proof-use generations above it.  The browser can load the full graph on
demand when a reader expands beyond that boundary.
"""

from __future__ import annotations

import json
import sys
from collections import defaultdict, deque
from pathlib import Path


MAX_UPSTREAM_DEPTH = 3


def upstream_ids(root_id: str, edges: list[dict]) -> tuple[set[str], set[str]]:
    incoming: dict[str, list[str]] = defaultdict(list)
    for edge in edges:
        incoming[edge["target"]["id"]].append(edge["source"]["id"])
    included = {root_id}
    boundary = set()
    queue = deque([(root_id, 0)])
    while queue:
        target, depth = queue.popleft()
        if depth >= MAX_UPSTREAM_DEPTH:
            if incoming[target]:
                boundary.add(target)
            continue
        for source in incoming[target]:
            if source not in included:
                included.add(source)
                queue.append((source, depth + 1))
    return included, boundary


def build(graph: dict, comparisons: dict, output_dir: Path) -> list[str]:
    output_dir.mkdir(parents=True, exist_ok=True)
    nodes = graph.get("nodes", [])
    edges = graph.get("edges", [])
    by_comparison = {
        node.get("comparison", {}).get("registry"): node
        for node in nodes
        if node.get("comparison", {}).get("registry")
    }
    # A one-route benchmark is not a merged graph node, but it still deserves
    # the same fast focused view as an exact comparison.
    for comparison in comparisons.get("comparisons", []):
        if comparison.get("id") in by_comparison:
            continue
        declarations = {route.get("declaration") for route in comparison.get("routes", [])}
        root = next((node for node in nodes
                     if node.get("namespace") in declarations or
                     any(proof.get("declaration") in declarations for proof in node.get("proofs", []))), None)
        if root:
            by_comparison[comparison["id"]] = root
    written = []
    for comparison_id, root in by_comparison.items():
        if not comparison_id:
            continue
        included, boundary = upstream_ids(root["id"], edges)
        slice_graph = {
            "schemaVersion": graph.get("schemaVersion", "1.0"),
            "graphId": f"{graph.get('graphId', 'math-net-project')}:{comparison_id}",
            "label": f"Focused dependency view: {comparison_id}",
            "partial": True,
            "partialUpstreamDepth": MAX_UPSTREAM_DEPTH,
            "partialBoundaryNodes": sorted(boundary),
            "focusComparison": comparison_id,
            "nodes": [node for node in nodes if node["id"] in included],
            "edges": [edge for edge in edges if edge["source"]["id"] in included and edge["target"]["id"] in included],
        }
        destination = output_dir / f"{comparison_id}.json"
        destination.write_text(json.dumps(slice_graph, separators=(",", ":"), sort_keys=True) + "\n")
        written.append(comparison_id)
    return written


if __name__ == "__main__":
    if len(sys.argv) != 4:
        raise SystemExit("usage: GenerateComparisonSlices.py project.json comparisons.json output-directory")
    ids = build(json.loads(Path(sys.argv[1]).read_text()),
                json.loads(Path(sys.argv[2]).read_text()), Path(sys.argv[3]))
    print(f"generated {len(ids)} comparison graph slices", file=sys.stderr)
