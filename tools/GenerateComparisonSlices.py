#!/usr/bin/env python3
"""Emit adaptive upstream dependency graphs for individual comparison views.

The complete project graph remains authoritative.  A focused slice is a fast
first view, but it is deliberately *not* a fixed number of proof-use
generations: fixed-depth slices make structures look like arbitrary top-level
ancestors.  Instead, the traversal continues through structures and routine
Lean machinery while reserving its visual budget for mathematical
declarations.  The browser can still load the complete landscape on demand.
"""

from __future__ import annotations

import json
import sys
from collections import defaultdict, deque
from pathlib import Path


MAX_INTERESTING_NODES = 56
MAX_TOTAL_NODES = 160


def presentation_category(node: dict) -> str:
    return node.get("presentation", {}).get("category", "supporting")


def is_interesting(node: dict) -> bool:
    """Count reader-facing mathematical landmarks against the slice budget."""
    return (
        presentation_category(node) == "mathematical"
        or node.get("role") == "structure"
        or bool(node.get("importance", {}).get("landmark"))
        or bool(node.get("comparison"))
    )


def is_foundation(node: dict) -> bool:
    return node.get("mathematicalRole", {}).get("category") == "foundation"


def reading_priority(node: dict) -> tuple[float, str]:
    """Prefer mathematical content without making structures artificial roots."""
    importance = node.get("importance", {}).get("score", 0)
    if len(node.get("comparison", {}).get("routes", [])) > 1:
        return (9000 + importance, node["id"])
    if presentation_category(node) == "mathematical":
        return (7000 + importance, node["id"])
    if node.get("importance", {}).get("landmark"):
        return (6000 + importance, node["id"])
    if node.get("role") == "structure":
        return (3500 + importance, node["id"])
    if presentation_category(node) == "supporting":
        return (1000 + importance, node["id"])
    return (importance, node["id"])


def upstream_ids(root_id: str, nodes: list[dict], edges: list[dict]) -> tuple[set[str], set[str]]:
    incoming: dict[str, list[str]] = defaultdict(list)
    for edge in edges:
        incoming[edge["target"]["id"]].append(edge["source"]["id"])
    by_id = {node["id"]: node for node in nodes}
    included = {root_id}
    boundary = set()
    queued = {root_id}
    interesting = int(is_interesting(by_id[root_id]))
    queue = deque([(root_id, 0)])
    while queue:
        target, depth = queue.popleft()
        # A mathematical foundation is a meaningful endpoint for the default
        # reader view. Its construction remains available by explicit expand.
        if is_foundation(by_id[target]):
            if incoming[target]:
                boundary.add(target)
            continue
        # Wide, shallow fan-out is much less readable than a path that reaches
        # several mathematical ideas.  This is a local breadth budget, not a
        # graph-depth cap: an unbranched proof path can continue indefinitely.
        branch_budget = 8 if depth == 0 else 6 if depth == 1 else 4
        accepted_here = 0
        sources = sorted(incoming[target], key=lambda source: reading_priority(by_id.get(source, {"id": source})), reverse=True)
        for source in sources:
            if source in queued:
                continue
            source_node = by_id.get(source)
            if not source_node:
                continue
            consumes_interest = int(is_interesting(source_node))
            if accepted_here >= branch_budget or len(included) >= MAX_TOTAL_NODES or interesting + consumes_interest > MAX_INTERESTING_NODES:
                boundary.add(target)
                continue
            queued.add(source)
            included.add(source)
            interesting += consumes_interest
            accepted_here += 1
            queue.append((source, depth + 1))
        if any(source not in included for source in incoming[target]):
            boundary.add(target)
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
        included, boundary = upstream_ids(root["id"], nodes, edges)
        slice_graph = {
            "schemaVersion": graph.get("schemaVersion", "1.0"),
            "graphId": f"{graph.get('graphId', 'math-net-project')}:{comparison_id}",
            "label": f"Focused dependency view: {comparison_id}",
            "partial": True,
            "partialStrategy": "adaptive-interesting-budget",
            "partialInterestingBudget": MAX_INTERESTING_NODES,
            "partialNodeBudget": MAX_TOTAL_NODES,
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
