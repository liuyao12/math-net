#!/usr/bin/env bash
set -euo pipefail

manifest="MathNetwork/Graph/comparisons.json"
raw_fermat_tmp="$(mktemp)"
raw_list100_tmp="$(mktemp)"
raw_mathlib_sqrt_tmp="$(mktemp)"
raw_computable_sqrt_tmp="$(mktemp)"
raw_graph_tmp="$(mktemp)"
project_tmp="$(mktemp)"
catalogue_tmp="$(mktemp)"
checks_tmp="$(mktemp)"
trap 'rm -f "$raw_fermat_tmp" "$raw_list100_tmp" "$raw_mathlib_sqrt_tmp" "$raw_computable_sqrt_tmp" "$raw_graph_tmp" "$project_tmp" "$catalogue_tmp" "$checks_tmp"' EXIT
tools/export-comparisons.sh > "$manifest"
# Each extractor sees a real elaborated Lean environment, but only for a
# coherent mathematical domain. Loading all of mathlib's calculus imports and
# the computable-analysis imports together peaks above hosted CI memory.
# Combining their declaration JSON afterwards is lossless: names and proof-use
# edges are preserved, then canonicalized to stable graph ids.
extract_slice() {
  local source="$1"
  local destination="$2"
  set +e
  lake env lean "$source" > "$destination"
  local status=$?
  set -e
  if [[ $status -ne 0 ]]; then
    echo "${source} failed with exit status ${status}" >&2
    exit "$status"
  fi
}
extract_slice tools/BuildGraphFermatEuler.lean "$raw_fermat_tmp"
extract_slice tools/BuildGraphList100.lean "$raw_list100_tmp"
extract_slice tools/BuildGraphMathlibSqrt.lean "$raw_mathlib_sqrt_tmp"
extract_slice tools/BuildGraphComputableSqrt.lean "$raw_computable_sqrt_tmp"
python3 tools/CombineRawGraphs.py "$raw_fermat_tmp" "$raw_list100_tmp" "$raw_mathlib_sqrt_tmp" "$raw_computable_sqrt_tmp" > "$raw_graph_tmp"
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
