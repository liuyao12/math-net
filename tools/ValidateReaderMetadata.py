#!/usr/bin/env python3
"""Validate the human-facing layer of the mathematical landscape.

This deliberately validates annotations rather than Lean proofs: a checked
declaration can be perfectly sound and still be unreadable to a mathematician
who does not know its project-local name.  Every curated comparison therefore
needs a reader statement and every route needs a short mathematical title and
description, either in the checked-comparison manifest or in the separate
route-note overlay.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


def read_json(path: Path) -> dict:
    try:
        return json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as error:
        raise SystemExit(f"cannot read {path}: {error}") from error


def nonempty(value: object) -> bool:
    return isinstance(value, str) and bool(value.strip())


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("comparisons", type=Path)
    parser.add_argument("reader_statements", type=Path)
    parser.add_argument("route_notes", type=Path)
    args = parser.parse_args()

    comparisons = read_json(args.comparisons).get("comparisons", [])
    statements = read_json(args.reader_statements).get("statements", {})
    notes = read_json(args.route_notes).get("notes", {})
    errors: list[str] = []
    registered_routes: set[str] = set()

    for comparison in comparisons:
        comparison_id = comparison.get("id", "<missing id>")
        if not nonempty(comparison.get("title")):
            errors.append(f"{comparison_id}: missing comparison title")
        if not nonempty(comparison.get("description")):
            errors.append(f"{comparison_id}: missing comparison description")
        if not nonempty(statements.get(comparison_id, {}).get("statement")):
            errors.append(f"{comparison_id}: missing reader-oriented statement")
        for route in comparison.get("routes", []):
            declaration = route.get("declaration", "<missing declaration>")
            registered_routes.add(declaration)
            overlay = notes.get(declaration, {})
            if not nonempty(route.get("title")) and not nonempty(overlay.get("title")):
                errors.append(f"{comparison_id}: {declaration} has no route title")
            if not nonempty(route.get("description")) and not nonempty(overlay.get("description")):
                errors.append(f"{comparison_id}: {declaration} has no route description")

    for declaration, note in notes.items():
        if declaration not in registered_routes:
            errors.append(f"route-note overlay refers to unregistered route {declaration}")
        if not nonempty(note.get("title")) or not nonempty(note.get("description")):
            errors.append(f"route-note overlay for {declaration} needs both title and description")

    if errors:
        print("reader metadata validation failed:", file=sys.stderr)
        print("\n".join(f"- {error}" for error in errors), file=sys.stderr)
        return 1
    route_count = sum(len(comparison.get("routes", [])) for comparison in comparisons)
    print(f"validated reader metadata for {len(comparisons)} comparisons and {route_count} routes")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
