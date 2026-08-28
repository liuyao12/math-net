#!/usr/bin/env python3
"""Refresh reader-facing mathematical roles without re-extracting Lean proofs.

This is safe only for semantic-role changes: it preserves every declaration,
statement, proof edge, proof record, and verification field in ``project``.
The normal full build also runs the same classifier after extraction.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

from MergeGraph import annotate_mathematical_roles


def main(project_path: str, roles_path: str) -> None:
    destination = Path(project_path)
    graph = json.loads(destination.read_text())
    before = [(node["id"], node.get("statement"), node.get("verification")) for node in graph["nodes"]]
    annotate_mathematical_roles(graph["nodes"], roles_path)
    after = [(node["id"], node.get("statement"), node.get("verification")) for node in graph["nodes"]]
    if before != after:
        raise SystemExit("semantic role refresh attempted to change checked graph data")
    temporary = destination.with_suffix(".json.tmp")
    temporary.write_text(json.dumps(graph, separators=(",", ":"), sort_keys=True) + "\n")
    temporary.replace(destination)
    foundations = sum(node.get("mathematicalRole", {}).get("category") == "foundation" for node in graph["nodes"])
    print(f"refreshed roles for {len(graph['nodes'])} nodes; {foundations} mathematical foundations")


if __name__ == "__main__":
    if len(sys.argv) != 3:
        raise SystemExit("usage: RefreshSemanticRoles.py project.json semantic-roles.json")
    main(sys.argv[1], sys.argv[2])
