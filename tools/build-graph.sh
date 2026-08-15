#!/usr/bin/env bash
set -euo pipefail

manifest="MathNetwork/Graph/comparisons.json"
raw_graph_tmp="$(mktemp)"
project_tmp="$(mktemp)"
catalogue_tmp="$(mktemp)"
checks_tmp="$(mktemp)"
trap 'rm -f "$raw_graph_tmp" "$project_tmp" "$catalogue_tmp" "$checks_tmp"' EXIT
tools/export-comparisons.sh > "$manifest"
# BuildGraph constructs the full elaborated environment.  Keeping its JSON in
# a temporary file before starting Python avoids a large Lean process and a
# JSON parser competing for peak memory on a fresh CI runner.
lake env lean tools/BuildGraph.lean > "$raw_graph_tmp"
if [[ ! -s "$raw_graph_tmp" ]]; then
  echo "BuildGraph.lean produced no graph JSON" >&2
  exit 1
fi
python3 tools/MergeGraph.py --comparisons "$manifest" < "$raw_graph_tmp" > "$project_tmp"
python3 tools/ValidateGraph.py "$project_tmp"
python3 tools/GenerateExactMergeChecks.py "$project_tmp" > "$checks_tmp"
lake env lean "$checks_tmp"
python3 tools/BuildCatalogue.py < "$project_tmp" > "$catalogue_tmp"
mv "$project_tmp" MathNetwork/Graph/project.json
mv "$catalogue_tmp" MathNetwork/Graph/theorem-catalogue.json
