#!/usr/bin/env python3
"""Export the exact external source revisions used by this Lake project."""

from __future__ import annotations

import json
import sys
from pathlib import Path


def main(manifest_path: str) -> None:
    manifest = json.loads(Path(manifest_path).read_text())
    packages = {package.get("name"): package for package in manifest.get("packages", [])}
    selected = {
        "mathlib": packages.get("mathlib", {}),
        "computable-analysis": packages.get("ComputableAnalysis", {}),
    }
    repositories = {
        name: {"repository": package.get("url"), "revision": package.get("rev")}
        for name, package in selected.items()
        if package.get("url") and package.get("rev")
    }
    json.dump({"schemaVersion": 1, "repositories": repositories}, sys.stdout, separators=(",", ":"))
    sys.stdout.write("\n")


if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("usage: ExportSourceRevisions.py lake-manifest.json")
    main(sys.argv[1])
