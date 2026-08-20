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
import math
import sys
from pathlib import Path
from collections import defaultdict


def proof_record(node: dict) -> dict:
    declaration = node.get("namespace", node["label"])
    short_declaration = declaration.rsplit(".", 1)[-1]
    if node.get("locator", "").startswith("mathlib/"):
        label = f"mathlib · {short_declaration}"
        route_kind = "mathlib"
        color = "#3f7f8f"
    elif node.get("locator", "").startswith("computable-analysis/"):
        label = f"computable-analysis · {short_declaration}"
        route_kind = "computable-analysis"
        color = "#a45b38"
    elif declaration in {
        "MathNetwork.SqrtTwo.irrational",
        "MathNetwork.MathlibSqrt.irrational_sqrt_ratCast_iff_of_nonneg",
    }:
        label = f"mathlib · {short_declaration}"
        route_kind = "mathlib"
        color = "#3f7f8f"
    elif declaration == "MathNetwork.ComputableSqrt.irrational_sqrt_ratCast_iff_of_nonneg":
        label = f"computable-analysis · {short_declaration}"
        route_kind = "computable-analysis"
        color = "#a45b38"
    else:
        label = f"math-net · {short_declaration}"
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
        "statement": node.get("statement", ""),
        # This is refined to `delegation` after the merged edge set is known.
        # A declaration that merely invokes an equal theorem is useful
        # provenance, but is not another mathematical proof route.
        "proofKind": "body",
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
            "comparisonTitle": comparison.get("title", ""),
            "comparisonDescription": comparison.get("description", ""),
            "area": comparison.get("area", "General mathematics"),
            "repository": route["repository"],
            "alignment": comparison.get("alignment", "exact"),
            "note": comparison.get("note", ""),
            "foundation": route.get("foundation"),
            "mathematicalCore": comparison.get("mathematicalCore"),
            "title": route.get("title", ""),
            "description": route.get("description", ""),
        }
        for comparison in data.get("comparisons", [])
        for route in comparison.get("routes", [])
    }


def annotate_importance(nodes: list[dict], edges: list[dict]) -> None:
    """Add reuse/reach signals without pretending they are proof difficulty.

    Edge direction is declaration-used-by-proof, so downstream reach measures
    how much of the indexed landscape can reuse a declaration. This is a
    structural landmark signal, not a claim that the node is mathematically
    more profound.
    """
    adjacency = {node["id"]: set() for node in nodes}
    direct_uses = {node["id"]: set() for node in nodes}
    for edge in edges:
        source = edge["source"]["id"]
        target = edge["target"]["id"]
        if source not in adjacency or target not in adjacency:
            continue
        adjacency[source].add(target)
        direct_uses[source].add((target, edge.get("proof") or ""))

    raw_scores = {}
    reach_counts = {}
    for node in nodes:
        seen = set()
        frontier = list(adjacency[node["id"]])
        while frontier:
            current = frontier.pop()
            if current in seen:
                continue
            seen.add(current)
            frontier.extend(adjacency.get(current, ()))
        direct = len(direct_uses[node["id"]])
        downstream = len(seen)
        proposition_bonus = 1.5 if node.get("kind") == "proposition" else 0.0
        raw_scores[node["id"]] = 2 * math.log1p(direct) + math.log1p(downstream) + proposition_bonus
        reach_counts[node["id"]] = (direct, downstream)

    maximum = max(raw_scores.values(), default=1.0)
    for node in nodes:
        direct, downstream = reach_counts[node["id"]]
        raw = raw_scores[node["id"]]
        score = round(100 * raw / maximum, 1) if maximum else 0.0
        signals = []
        if direct:
            signals.append("reused directly in indexed proofs")
        if downstream:
            signals.append("has downstream dependents")
        if node.get("kind") == "proposition":
            signals.append("proposition/theorem declaration")
        node["importance"] = {
            "score": score,
            "directUses": direct,
            "downstreamNodes": downstream,
            "landmark": score >= 65 and (direct >= 2 or downstream >= 8),
            "signals": signals,
            "method": "reuse and downstream reach; not proof-length difficulty",
        }


def annotate_presentation(nodes: list[dict]) -> None:
    """Classify how a declaration should be presented, not how true it is.

    The Lean kernel does not distinguish a mathematical theorem from the
    generated plumbing that makes a formalization work.  This conservative,
    inspectable heuristic keeps all of that plumbing in the graph while
    letting a reader see the mathematical spine first.
    """
    foundational_definition_modules = (
        "mathlib/Mathlib.Algebra.", "mathlib/Mathlib.Data.",
        "mathlib/Mathlib.Logic.", "mathlib/Mathlib.Init.", "mathlib/Mathlib.Order.",
    )
    implementation_modules = (
        "mathlib/Mathlib.Tactic.", "mathlib/Mathlib.Meta.",
        "mathlib/Mathlib.Lean.", "mathlib/Mathlib.Util.",
    )

    def foundational(node: dict) -> bool:
        return node.get("locator", "").startswith(foundational_definition_modules)

    def implementation_module(node: dict) -> bool:
        return node.get("locator", "").startswith(implementation_modules)

    for node in nodes:
        declaration_kind = node.get("declarationKind", "")
        declaration = node.get("namespace", node.get("label", ""))
        generated = declaration_kind in {"constructor", "recursor", "quotient"} or "._proof_" in declaration or ".match_" in declaration
        if generated or node.get("structuralProjection", False) or implementation_module(node):
            category = "implementation"
            reason = "Kernel-generated declaration, Lean structure projection, or tactic/meta implementation declaration."
        elif (
            declaration_kind in {"theorem", "opaque"}
            and foundational(node)
        ):
            category = "routine"
            reason = "Routine algebraic/data-foundation lemma; retained but suppressed in the explanatory view."
        elif node.get("kind") == "proposition" or declaration_kind in {"theorem", "opaque", "axiom", "proposition"}:
            category = "mathematical"
            reason = "Checked mathematical proposition or theorem declaration."
        elif declaration_kind == "definition" and not foundational(node) and "->" in node.get("statement", ""):
            category = "mathematical"
            reason = "Named mathematical definition used in the displayed proof landscape."
        else:
            category = "supporting"
            reason = "Supporting type, definition, or algebraic infrastructure needed by the proof."
        node["presentation"] = {"category": category, "reason": reason}


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
            registered = registered_routes.get(node.get("namespace", ""))
            key = (("foundation-aligned", registered["id"])
                   if registered and registered.get("alignment") == "foundation-aligned"
                   else (node.get("statement", ""),))
            groups[key].append(node)
        else:
            passthrough.append(node)

    merged_nodes: list[dict] = []
    old_to_new: dict[str, str] = {}
    proof_for_old: dict[str, str] = {}

    for group in groups.values():
        representative = group[0]
        merged = dict(representative)
        # The graph label is the actual Lean declaration name.  Conventional
        # mathematical names belong in the statement and explanatory metadata,
        # rather than silently replacing the formalization's own identifier.
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
            is_foundation_aligned = any(
                registered_routes.get(record["declaration"], {}).get("alignment") == "foundation-aligned"
                for record in merged["proofs"]
            )
            is_presentation = any(
                registered_routes.get(record["declaration"], {}).get("alignment") == "presentation"
                for record in merged["proofs"]
            )
            merged["comparison"] = {
                "identity": (
                    "foundation-aligned criteria over distinct real-number representations"
                    if is_foundation_aligned else
                    "one independently checked Lean declaration, awaiting a second route"
                    if is_presentation else "exact elaborated proposition statement"
                ),
                "alignment": "foundation-aligned" if is_foundation_aligned else
                             "presentation" if is_presentation else "exact",
                "routes": comparison_routes,
                "note": (
                    next((registered_routes[record["declaration"]].get("note", "")
                          for record in merged["proofs"]
                          if record["declaration"] in registered_routes and
                          registered_routes[record["declaration"]].get("alignment") == "foundation-aligned"), "")
                    if is_foundation_aligned else
                    "This application has one checked route. It remains visible so a later imported proof can be compared without redesigning the graph."
                    if is_presentation else
                    "The declarations are merged only because Lean checked their "
                    "elaborated proposition types as definitionally equal."
                ),
            }
            if not is_foundation_aligned and not is_presentation:
                merged["comparison"]["kernelCheck"] = (
                    "Lean's definitional-equality checker validates every route pair "
                    "when tools/build-graph.sh generates this graph."
                )
            if is_foundation_aligned:
                merged["comparison"]["foundations"] = [
                    {
                        "repository": metadata["repository"],
                        "declaration": metadata["foundation"],
                    }
                    for _, metadata in registered
                    if metadata.get("foundation")
                ]
            if registered:
                merged["comparison"]["registry"] = registered[0][1]["id"]
                merged["comparison"]["title"] = registered[0][1].get("comparisonTitle", "")
                merged["comparison"]["description"] = registered[0][1].get("comparisonDescription", "")
                merged["comparison"]["area"] = registered[0][1].get("area", "General mathematics")
                merged["comparison"]["routeAudit"] = (
                    "Every registered route is checked for the absence of Lean's "
                    "sorryAx when this graph is generated. Computational "
                    "native_decide axioms, if any, are reported separately."
                )
                mathematical_core = registered[0][1].get("mathematicalCore")
                if mathematical_core:
                    merged["comparison"]["mathematicalCore"] = mathematical_core
            merged["verification"] = dict(merged.get("verification", {}))
            merged["verification"]["note"] = (
                merged["verification"].get("note", "")
                + (f" Foundation-aligned from {len(group)} independently checked declarations; their real-number bridge is not yet formalized."
                   if is_foundation_aligned else
                   f" Presented as one independently checked route across {len(group)} indexed declaration(s)."
                   if is_presentation else
                   f" Merged from {len(group)} declarations with the identical checked statement in the same module.")
            ).strip()
        merged_nodes.append(merged)

    merged_nodes.extend(passthrough)
    for node in passthrough:
        old_to_new[node["id"]] = node["id"]

    merged_node_by_id = {node["id"]: node for node in merged_nodes}
    edges = []
    delegation_keys: set[tuple[str, str, str]] = set()
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
        if source_new == target_new:
            # A local adapter can invoke an imported theorem with exactly the
            # same proposition.  After statement merging that call would be a
            # self-loop, which is not a prerequisite of the proposition and
            # makes a directed dependency drawing falsely look circular.
            # Preserve the useful fact as route metadata for the inspector.
            source_declaration = node_by_id[source_old].get("namespace", node_by_id[source_old].get("label", ""))
            key = (target_new, rewritten.get("proof", ""), source_declaration)
            if rewritten.get("proof") and key not in delegation_keys:
                delegation_keys.add(key)
                merged_node_by_id[target_new].setdefault("proofDelegations", []).append({
                    "proof": rewritten["proof"],
                    "declaration": source_declaration,
                    "locator": node_by_id[source_old].get("locator", ""),
                })
            continue
        edges.append(rewritten)

    # A self-loop removed above witnesses an exact delegation: its proof body
    # invokes a theorem with precisely the proposition of the merged node.
    # Keep the alias visible, but never advertise it as an independent proof.
    for node in merged_nodes:
        delegations = {
            item["proof"]: item["declaration"]
            for item in node.get("proofDelegations", [])
        }
        for proof in node.get("proofs", []):
            if proof["id"] in delegations:
                proof["proofKind"] = "delegation"
                proof["delegatesTo"] = delegations[proof["id"]]

            # The comparison registry records the provenance of a route even
            # when MathNet supplies a small adapter declaration.  This makes
            # the map colour describe the proof's native repository, rather
            # than the repository that happens to host the adapter.
            metadata = registered_routes.get(proof["declaration"])
            if metadata:
                proof["repository"] = metadata["repository"]
                proof["routeTitle"] = metadata.get("title", "")
                proof["routeDescription"] = metadata.get("description", "")

        comparison = node.get("comparison")
        if comparison and comparison.get("alignment") == "exact":
            independent = [proof for proof in node.get("proofs", [])
                           if proof.get("proofKind") != "delegation"]
            # Statement aliases in mathlib and MathNet are not comparisons.
            # Leave their declarations and delegation provenance in place, but
            # reserve the comparison UI for genuinely distinct proof bodies.
            if len(independent) < 2:
                node.pop("comparison", None)
            else:
                comparison["routes"] = [
                    route for route in comparison.get("routes", [])
                    if route.get("proof") in {proof["id"] for proof in independent}
                ]

    result = dict(graph)
    result["nodes"] = merged_nodes
    result["edges"] = edges
    annotate_importance(result["nodes"], result["edges"])
    annotate_presentation(result["nodes"])
    result["merge"] = {
        "key": "exact elaborated proposition statement across local and imported declarations",
        "definitions": "one node per declaration",
        "proofProvenance": "edge proof field and proposition proofs records; aliases are marked as delegations, not proof alternatives",
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
