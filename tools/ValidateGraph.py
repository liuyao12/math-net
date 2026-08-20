#!/usr/bin/env python3
"""Validate invariants required by the mathematical-landscape UI."""

from __future__ import annotations

import json
import sys
from pathlib import Path


def fail(message: str) -> None:
    raise SystemExit(f"graph validation failed: {message}")


def main(path: str, manifest_path: str | None = None) -> None:
    graph = json.loads(Path(path).read_text())
    nodes = graph.get("nodes", [])
    edges = graph.get("edges", [])
    node_ids = [node.get("id") for node in nodes]
    if len(node_ids) != len(set(node_ids)):
        fail("node ids are not unique")
    node_id_set = set(node_ids)
    proofs_by_node = {
        node["id"]: {proof["id"] for proof in node.get("proofs", [])}
        for node in nodes
    }
    all_proofs = set().union(*proofs_by_node.values()) if proofs_by_node else set()
    if len(all_proofs) != sum(len(proofs) for proofs in proofs_by_node.values()):
        fail("proof route ids are not globally unique")

    for edge in edges:
        source = edge.get("source", {}).get("id")
        target = edge.get("target", {}).get("id")
        if source not in node_id_set or target not in node_id_set:
            fail(f"edge {edge.get('id')} has a dangling endpoint")
        if source == target:
            fail(f"edge {edge.get('id')} is a collapsed self-dependency")
        if edge.get("relation") != "used-in-proof":
            fail(f"edge {edge.get('id')} has non-proof relation {edge.get('relation')!r}")
        if edge.get("proof") and edge["proof"] not in all_proofs:
            fail(f"edge {edge.get('id')} names an unknown proof route")

    exact_merges = 0
    aligned = 0
    presentations = 0
    for node in nodes:
        comparison = node.get("comparison")
        if not comparison:
            continue
        proof_ids = proofs_by_node[node["id"]]
        if comparison.get("alignment") == "exact":
            exact_merges += 1
            if len(proof_ids) < 2:
                fail(f"exact comparison {node['id']} has fewer than two proof routes")
            if not comparison.get("kernelCheck"):
                fail(f"exact comparison {node['id']} lacks kernel-check provenance")
        elif comparison.get("alignment") == "foundation-aligned":
            aligned += 1
            if comparison.get("kernelCheck"):
                fail(f"foundation-aligned comparison {node['id']} claims a kernel exact merge")
        elif comparison.get("alignment") == "presentation":
            presentations += 1
            if comparison.get("kernelCheck"):
                fail(f"checked presentation {node['id']} claims an exact merge")
            if not comparison.get("routes"):
                fail(f"checked presentation {node['id']} has no checked route")
        else:
            fail(f"comparison {node['id']} has unknown alignment")
        for route in comparison.get("routes", []):
            if route.get("proof") not in proof_ids:
                fail(f"comparison {node['id']} refers to a non-local proof route")
        seen_delegations: set[tuple[str, str]] = set()
        for delegation in node.get("proofDelegations", []):
            key = (delegation.get("proof", ""), delegation.get("declaration", ""))
            if key in seen_delegations:
                fail(f"comparison {node['id']} repeats adapter delegation {key}")
            seen_delegations.add(key)
            if delegation.get("proof") not in proof_ids or not delegation.get("declaration"):
                fail(f"comparison {node['id']} has malformed adapter delegation")

    if manifest_path:
        manifest = json.loads(Path(manifest_path).read_text())
        # A singleton in the registry can be a concrete benchmark (such as
        # irrationality of √2) whose comparison lives upstream.  Require a
        # generated landscape only for actual multi-route comparisons,
        # foundation alignments, and explicitly marked checked presentations.
        registered = {
            item.get("id"): item
            for item in manifest.get("comparisons", [])
            if item.get("id") and (
                len(item.get("routes", [])) > 1
                or item.get("alignment") in {"foundation-aligned", "presentation"}
            )
        }
        graph_comparisons = {
            comparison.get("registry"): node
            for node in nodes
            if (comparison := node.get("comparison")) and comparison.get("registry")
        }
        missing = sorted(set(registered) - set(graph_comparisons))
        if missing:
            fail(f"registered comparison(s) absent from generated graph: {', '.join(missing)}")
        for comparison_id, registered_comparison in registered.items():
            node = graph_comparisons[comparison_id]
            actual = {proof.get("declaration") for proof in node.get("proofs", [])}
            expected = {route.get("declaration") for route in registered_comparison.get("routes", [])}
            absent_routes = sorted(expected - actual)
            if absent_routes:
                fail(
                    f"registered route(s) absent from {comparison_id}: "
                    f"{', '.join(absent_routes)}"
                )

    print(
        f"validated {len(nodes)} nodes, {len(edges)} proof edges, "
        f"{exact_merges} exact comparisons, {aligned} foundation-aligned comparisons, "
        f"and {presentations} checked presentations"
    )


if __name__ == "__main__":
    if len(sys.argv) == 2:
        main(sys.argv[1])
    elif len(sys.argv) == 4 and sys.argv[2] == "--comparisons":
        main(sys.argv[1], sys.argv[3])
    else:
        raise SystemExit("usage: ValidateGraph.py project.json [--comparisons comparisons.json]")
