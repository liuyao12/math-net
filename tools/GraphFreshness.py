#!/usr/bin/env python3
"""Record and verify the inputs from which the checked graph was generated."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parent.parent


def input_paths() -> list[Path]:
    paths = [
        ROOT / "lean-toolchain",
        ROOT / "lakefile.toml",
        ROOT / "lake-manifest.json",
        ROOT / "tools" / "build-graph.sh",
        ROOT / "tools" / "CombineRawGraphs.py",
        ROOT / "tools" / "MergeGraph.py",
        ROOT / "tools" / "RefreshSemanticRoles.py",
        ROOT / "MathNetwork" / "Graph" / "semantic-roles.json",
        ROOT / "tools" / "ValidateGraph.py",
        ROOT / "tools" / "ValidateReaderMetadata.py",
        ROOT / "tools" / "ValidateDeclarationNotes.py",
        ROOT / "tools" / "GenerateExactMergeChecks.py",
        ROOT / "tools" / "BuildCatalogue.py",
        ROOT / "tools" / "GenerateComparisonSlices.py",
        ROOT / "tools" / "ExportSourceRevisions.py",
        ROOT / "tools" / "CheckNoSorry.py",
        ROOT / "tools" / "export-comparisons.sh",
        ROOT / "tools" / "GraphFreshness.py",
        ROOT / "MathNetwork" / "Graph" / "Extract.lean",
        ROOT / "MathNetwork" / "Graph" / "reader-statements.json",
        ROOT / "MathNetwork" / "Graph" / "route-notes.json",
        ROOT / "MathNetwork" / "Graph" / "declaration-notes.json",
    ]
    paths.extend(sorted((ROOT / "MathNetwork").rglob("*.lean")))
    # Only committed extractor entrypoints participate. A local editor backup
    # must not make the graph appear stale or become an accidental input.
    paths.extend(sorted(path for path in (ROOT / "tools").glob("BuildGraph*.lean")
                        if " " not in path.name))
    return paths


def fingerprint() -> dict[str, str]:
    result = {}
    for path in input_paths():
        relative = path.relative_to(ROOT).as_posix()
        result[relative] = hashlib.sha256(path.read_bytes()).hexdigest()
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--write", type=Path)
    group.add_argument("--check", type=Path)
    args = parser.parse_args()
    current = {"schemaVersion": 1, "inputs": fingerprint()}
    if args.write:
        args.write.write_text(json.dumps(current, indent=2, sort_keys=True) + "\n")
        return
    recorded = json.loads(args.check.read_text())
    if recorded == current:
        print(f"graph inputs are current ({len(current['inputs'])} files)")
        return
    old = recorded.get("inputs", {})
    changed = sorted({*old, *current["inputs"]} - {
        path for path in {*old, *current["inputs"]}
        if old.get(path) == current["inputs"].get(path)
    })
    print("checked graph is stale; run tools/build-graph.sh and commit its outputs", file=sys.stderr)
    for path in changed:
        print(f"  {path}", file=sys.stderr)
    raise SystemExit(1)


if __name__ == "__main__":
    main()
