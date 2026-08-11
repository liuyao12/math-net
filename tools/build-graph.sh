#!/usr/bin/env bash
set -euo pipefail

manifest="MathNetwork/Graph/comparisons.json"
tools/export-comparisons.sh > "$manifest"
lake env lean tools/BuildGraph.lean \
  | python3 tools/MergeGraph.py --comparisons "$manifest" \
  > MathNetwork/Graph/project.json
python3 tools/BuildCatalogue.py < MathNetwork/Graph/project.json \
  > MathNetwork/Graph/theorem-catalogue.json
