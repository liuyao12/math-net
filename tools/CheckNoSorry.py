#!/usr/bin/env python3
"""Reject a registered proof route whose transitive proof term uses `sorryAx`.

The comparison registry is the public contract for the explorer's
"kernel-checked" labels. This script derives every registered declaration
from that contract, asks Lean for its axiom footprint, and rejects any route
that depends on the placeholder axiom produced by `sorry`.
"""

from __future__ import annotations

import json
import re
import subprocess
import sys
from argparse import ArgumentParser
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def main(json_output: bool = False) -> int:
    manifest = subprocess.run(
        ["tools/export-comparisons.sh"],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=False,
    )
    if manifest.returncode:
        sys.stderr.write(manifest.stderr)
        return manifest.returncode
    try:
        comparisons = json.loads(manifest.stdout)["comparisons"]
    except (json.JSONDecodeError, KeyError) as error:
        print(f"could not read comparison registry: {error}", file=sys.stderr)
        return 1

    declarations = sorted({
        route["declaration"]
        for comparison in comparisons
        for route in comparison.get("routes", [])
        if route.get("declaration")
    })
    # Foundation-aligned rows can refer to an indexed Mathlib wrapper that is
    # intentionally not imported by the registry itself.
    source = (
        "import MathNetwork.Comparisons.Registry\n"
        "import MathNetwork.Comparisons.List100\n"
    ) + "\n".join(
        f"#print axioms {declaration}" for declaration in declarations
    ) + "\n"
    check = subprocess.run(
        ["lake", "env", "lean", "/dev/stdin"],
        cwd=ROOT,
        text=True,
        input=source,
        capture_output=True,
        check=False,
    )
    if check.returncode:
        sys.stderr.write(check.stdout)
        sys.stderr.write(check.stderr)
        return check.returncode
    if "sorryAx" in check.stdout or "sorryAx" in check.stderr:
        print("registered route depends on sorryAx:", file=sys.stderr)
        print(check.stdout, file=sys.stderr)
        return 1
    axiom_blocks = re.findall(
        r"'([^']+)' depends on axioms: \[(.*?)\]",
        check.stdout,
        flags=re.DOTALL,
    )
    axiom_map = {declaration: axioms for declaration, axioms in axiom_blocks}
    native_routes = [declaration for declaration in declarations if "native_decide" in axiom_map.get(declaration, "")]
    if json_output:
        print(json.dumps({
            "schemaVersion": 1,
            "routes": [{
                "declaration": declaration,
                "sorryFree": True,
                "nativeDecide": declaration in native_routes,
            } for declaration in declarations],
        }, separators=(",", ":")))
        return 0
    print(f"checked {len(declarations)} registered Lean routes: no sorryAx")
    if native_routes:
        print(
            "native_decide computational axioms occur in "
            f"{len(native_routes)} route(s): {', '.join(native_routes)}"
        )
    return 0


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true", help="emit a machine-readable per-route audit")
    raise SystemExit(main(parser.parse_args().json))
