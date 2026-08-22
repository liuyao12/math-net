#!/usr/bin/env python3
"""Emit Lean kernel checks for every exact merged proposition in a graph."""

from __future__ import annotations

import json
import sys
from pathlib import Path


IMPORTS = (
    "MathNetwork.Fermat.Registry",
    "MathNetwork.Euler.Applications",
    "MathNetwork.Comparisons.List100",
    "MathNetwork.Comparisons.RationalSquares",
    "MathNetwork.Comparisons.MathlibIrrationalSqrt",
    "MathNetwork.Comparisons.IrrationalSqrtTwo",
    "MathNetwork.Comparisons.ComputableIrrationalSqrt",
    "MathNetwork.Comparisons.ComputableFTC",
    "MathNetwork.Comparisons.ComputableFourier",
    "MathNetwork.Calculus.FinitePolynomialDerivatives",
    "MathNetwork.Calculus.DerivativeUniqueness",
)


def main(path: str) -> None:
    graph = json.loads(Path(path).read_text())
    pairs: list[tuple[str, str]] = []
    for node in graph.get("nodes", []):
        comparison = node.get("comparison", {})
        proofs = node.get("proofs", [])
        if comparison.get("alignment") != "exact" or len(proofs) < 2:
            continue
        first = proofs[0]["declaration"]
        pairs.extend((first, proof["declaration"]) for proof in proofs[1:])

    print("import Lean")
    for module in IMPORTS:
        print(f"import {module}")
    print("\nopen Lean Elab Command Meta\n")
    print("syntax \"check_exact_merge \" ident ident : command\n")
    print("""elab_rules : command
  | `(check_exact_merge $left:ident $right:ident) => do
    let env ← getEnv
    let some leftInfo := env.find? left.getId
      | throwError s!\"declaration not found: {left.getId}\"
    let some rightInfo := env.find? right.getId
      | throwError s!\"declaration not found: {right.getId}\"
    let equal ← liftTermElabM fun _ => isDefEq leftInfo.type rightInfo.type
    if !equal then
      throwError s!\"exact merge rejected: {left.getId} and {right.getId} are not definitionally equal\"
""")
    print(f"-- Generated from {len(pairs)} exact proposition merges.\n")
    for left, right in pairs:
        print(f"check_exact_merge {left} {right}")


if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("usage: GenerateExactMergeChecks.py project.json")
    main(sys.argv[1])
