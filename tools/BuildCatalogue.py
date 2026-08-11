#!/usr/bin/env python3
"""Build the theorem-centred catalogue from the checked declaration graph.

The graph remains declaration-oriented. This index provides the stable place
to attach alternate formalizations and equivalence evidence as other repos are
added, without pretending that syntactic or elaborated equality proves a
broader mathematical equivalence.
"""

from __future__ import annotations

import hashlib
import json
import sys
from collections import defaultdict


def statement_key(statement: str) -> str:
    digest = hashlib.sha256(statement.encode("utf-8")).hexdigest()
    return f"statement:sha256:{digest}"


def build(graph: dict) -> dict:
    nodes = {node["id"]: node for node in graph["nodes"]}
    theorem_nodes = [node for node in graph["nodes"] if node.get("kind") == "proposition"]
    library_theorem_nodes = [
        node for node in graph["nodes"]
        if node.get("kind") == "source" and node.get("declarationKind") in {"theorem", "opaque", "axiom", "proposition"}
    ]
    uses = defaultdict(list)
    used_by = defaultdict(list)
    for edge in graph["edges"]:
        source = nodes.get(edge["source"]["id"])
        target = nodes.get(edge["target"]["id"])
        if not source or not target:
            continue
        relation = {
            "edgeId": edge["id"],
            "nodeId": source["id"],
            "label": source.get("label"),
            "namespace": source.get("namespace"),
            "kind": source.get("kind"),
            "proof": edge.get("proof") or None,
            "depth": source.get("dependencyDepth"),
        }
        reverse = {
            "edgeId": edge["id"],
            "nodeId": target["id"],
            "label": target.get("label"),
            "namespace": target.get("namespace"),
            "proof": edge.get("proof") or None,
        }
        if target.get("kind") == "proposition":
            uses[target["id"]].append(relation)
        if source.get("kind") == "proposition":
            used_by[source["id"]].append(reverse)

    theorems = []
    for node in theorem_nodes:
        theorems.append({
            "id": f"theorem:{node['id']}",
            "graphNode": node["id"],
            "label": node.get("label"),
            "statement": node.get("statement", ""),
            "identity": {
                "kind": "exact-elaborated-statement",
                "key": statement_key(node.get("statement", "")),
                "equivalenceEvidence": [],
            },
            "formalizations": node.get("formalizations", []),
            "proofs": node.get("proofs", []),
            "comparison": node.get("comparison"),
            "importance": node.get("importance"),
            "dependencies": {
                "uses": uses[node["id"]],
                "usedBy": used_by[node["id"]],
            },
            "externalFormalizations": [],
            "notes": [],
        })
    library_theorems = []
    for node in library_theorem_nodes:
        library_theorems.append({
            "id": f"library-theorem:{node['id']}",
            "graphNode": node["id"],
            "label": node.get("label"),
            "statement": node.get("statement", ""),
            "identity": {
                "kind": "exact-elaborated-statement",
                "key": statement_key(node.get("statement", "")),
                "equivalenceEvidence": [],
            },
            "formalizations": [{
                "repository": "mathlib4",
                "language": "Lean",
                "name": node.get("namespace"),
                "locator": node.get("locator"),
            }],
            "proofs": [],
            "externalFormalizations": [],
            "notes": ["Imported theorem declaration; its proof body is maintained by mathlib4."],
        })
    return {
        "schemaVersion": "1.0",
        "catalogueId": "math-net-theorems",
        "sourceGraph": graph.get("graphId"),
        "identityPolicy": {
            "automatic": "exact elaborated Lean statement",
            "equivalence": "must be represented by an explicit checked theorem or reviewed evidence",
        },
        "theorems": theorems,
        "libraryTheorems": library_theorems,
    }


if __name__ == "__main__":
    json.dump(build(json.load(sys.stdin)), sys.stdout, separators=(",", ":"), sort_keys=True)
    sys.stdout.write("\n")
