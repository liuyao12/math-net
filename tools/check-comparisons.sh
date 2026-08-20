#!/usr/bin/env bash
set -euo pipefail

lake env lean tools/CheckComparison.lean
python3 tools/GenerateExactMergeChecks.py MathNetwork/Graph/project.json | lake env lean /dev/stdin
python3 tools/CheckNoSorry.py
