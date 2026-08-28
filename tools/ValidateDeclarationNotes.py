#!/usr/bin/env python3
"""Validate human-facing notes attached to indexed Lean declarations."""

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
    parser.add_argument("project", type=Path, help="generated project.json")
    parser.add_argument("notes", type=Path, help="declaration-notes.json")
    args = parser.parse_args()

    namespaces = {node.get("namespace") for node in read_json(args.project).get("nodes", [])}
    notes = read_json(args.notes).get("notes", {})
    errors: list[str] = []
    for declaration, note in notes.items():
        if declaration not in namespaces:
            errors.append(f"{declaration}: no matching indexed declaration")
        for field in ("title", "statement", "why"):
            if not nonempty(note.get(field)):
                errors.append(f"{declaration}: missing reader-note {field}")
    if errors:
        print("declaration-note validation failed:", file=sys.stderr)
        print("\n".join(f"- {error}" for error in errors), file=sys.stderr)
        return 1
    print(f"validated {len(notes)} declaration notes against {len(namespaces)} indexed declarations")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
