#!/usr/bin/env bash
set -euo pipefail

manifest="MathNetwork/Graph/comparisons.json"
project_tmp="$(mktemp)"
catalogue_tmp="$(mktemp)"
checks_tmp="$(mktemp)"
trap 'rm -f "$project_tmp" "$catalogue_tmp" "$checks_tmp"' EXIT
tools/export-comparisons.sh > "$manifest"
lake env lean tools/BuildGraph.lean \
  | python3 tools/MergeGraph.py --comparisons "$manifest" \
  > "$project_tmp"
python3 tools/ValidateGraph.py "$project_tmp"
python3 tools/GenerateExactMergeChecks.py "$project_tmp" > "$checks_tmp"
lake env lean "$checks_tmp"
python3 tools/BuildCatalogue.py < "$project_tmp" > "$catalogue_tmp"
mv "$project_tmp" MathNetwork/Graph/project.json
mv "$catalogue_tmp" MathNetwork/Graph/theorem-catalogue.json
