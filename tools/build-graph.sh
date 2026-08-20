#!/usr/bin/env bash
set -euo pipefail

manifest="MathNetwork/Graph/comparisons.json"
raw_fermat_basic_tmp="$(mktemp)"
raw_fermat_registry_tmp="$(mktemp)"
raw_euler_tmp="$(mktemp)"
raw_list100_basel_tmp="$(mktemp)"
raw_list100_demoivre_tmp="$(mktemp)"
raw_list100_leibniz_tmp="$(mktemp)"
raw_list100_taylor_tmp="$(mktemp)"
raw_list100_ftc_tmp="$(mktemp)"
raw_mathlib_sqrt_tmp="$(mktemp)"
raw_computable_sqrt_tmp="$(mktemp)"
raw_computable_ftc_tmp="$(mktemp)"
raw_computable_fourier_tmp="$(mktemp)"
raw_computable_series_tmp="$(mktemp)"
raw_computable_demoivre_tmp="$(mktemp)"
raw_computable_pi_geometry_tmp="$(mktemp)"
raw_computable_logarithm_tmp="$(mktemp)"
raw_computable_nilakantha_tmp="$(mktemp)"
raw_computable_rotation_ode_tmp="$(mktemp)"
raw_graph_tmp="$(mktemp)"
project_tmp="$(mktemp)"
catalogue_tmp="$(mktemp)"
checks_tmp="$(mktemp)"
route_audit_tmp="$(mktemp)"
trap 'rm -f "$raw_fermat_basic_tmp" "$raw_fermat_registry_tmp" "$raw_euler_tmp" "$raw_list100_basel_tmp" "$raw_list100_demoivre_tmp" "$raw_list100_leibniz_tmp" "$raw_list100_taylor_tmp" "$raw_list100_ftc_tmp" "$raw_mathlib_sqrt_tmp" "$raw_computable_sqrt_tmp" "$raw_computable_ftc_tmp" "$raw_computable_fourier_tmp" "$raw_computable_series_tmp" "$raw_computable_demoivre_tmp" "$raw_computable_pi_geometry_tmp" "$raw_computable_logarithm_tmp" "$raw_computable_nilakantha_tmp" "$raw_computable_rotation_ode_tmp" "$raw_graph_tmp" "$project_tmp" "$catalogue_tmp" "$checks_tmp" "$route_audit_tmp"' EXIT
tools/export-comparisons.sh > "$manifest"
python3 tools/CheckNoSorry.py --json > "$route_audit_tmp"
# Each extractor sees a real elaborated Lean environment, but only for a
# coherent mathematical domain. Loading all of mathlib's calculus imports and
# the computable-analysis imports together peaks above hosted CI memory.
# Combining their declaration JSON afterwards is lossless: names and proof-use
# edges are preserved, then canonicalized to stable graph ids.
extract_slice() {
  local source="$1"
  local destination="$2"
  set +e
  # A declaration body can be much larger than the theorem statement itself.
  # Mathlib's deeply elaborated proof terms exceed Lean's conservative default
  # interpreter ceiling on hosted runners, even in a small import slice.
  lake env lean -M 6000 "$source" > "$destination"
  local status=$?
  set -e
  if [[ $status -ne 0 ]]; then
    echo "${source} failed with exit status ${status}" >&2
    exit "$status"
  fi
}
extract_slice tools/BuildGraphFermatBasic.lean "$raw_fermat_basic_tmp"
extract_slice tools/BuildGraphFermatRegistry.lean "$raw_fermat_registry_tmp"
extract_slice tools/BuildGraphEuler.lean "$raw_euler_tmp"
extract_slice tools/BuildGraphList100Basel.lean "$raw_list100_basel_tmp"
extract_slice tools/BuildGraphList100DeMoivre.lean "$raw_list100_demoivre_tmp"
extract_slice tools/BuildGraphList100Leibniz.lean "$raw_list100_leibniz_tmp"
extract_slice tools/BuildGraphList100Taylor.lean "$raw_list100_taylor_tmp"
extract_slice tools/BuildGraphList100FTC.lean "$raw_list100_ftc_tmp"
extract_slice tools/BuildGraphMathlibSqrt.lean "$raw_mathlib_sqrt_tmp"
extract_slice tools/BuildGraphComputableSqrt.lean "$raw_computable_sqrt_tmp"
extract_slice tools/BuildGraphComputableFTC.lean "$raw_computable_ftc_tmp"
extract_slice tools/BuildGraphComputableFourier.lean "$raw_computable_fourier_tmp"
extract_slice tools/BuildGraphComputableSeries.lean "$raw_computable_series_tmp"
extract_slice tools/BuildGraphComputableDeMoivre.lean "$raw_computable_demoivre_tmp"
extract_slice tools/BuildGraphComputablePiGeometry.lean "$raw_computable_pi_geometry_tmp"
extract_slice tools/BuildGraphComputableLogarithm.lean "$raw_computable_logarithm_tmp"
extract_slice tools/BuildGraphComputableNilakantha.lean "$raw_computable_nilakantha_tmp"
extract_slice tools/BuildGraphComputableRotationODE.lean "$raw_computable_rotation_ode_tmp"
python3 tools/CombineRawGraphs.py "$raw_fermat_basic_tmp" "$raw_fermat_registry_tmp" "$raw_euler_tmp" "$raw_list100_basel_tmp" "$raw_list100_demoivre_tmp" "$raw_list100_leibniz_tmp" "$raw_list100_taylor_tmp" "$raw_list100_ftc_tmp" "$raw_mathlib_sqrt_tmp" "$raw_computable_sqrt_tmp" "$raw_computable_ftc_tmp" "$raw_computable_fourier_tmp" "$raw_computable_series_tmp" "$raw_computable_demoivre_tmp" "$raw_computable_pi_geometry_tmp" "$raw_computable_logarithm_tmp" "$raw_computable_nilakantha_tmp" "$raw_computable_rotation_ode_tmp" > "$raw_graph_tmp"
if [[ ! -s "$raw_graph_tmp" ]]; then
  echo "BuildGraph.lean produced no graph JSON" >&2
  exit 1
fi
python3 tools/MergeGraph.py --comparisons "$manifest" --route-audit "$route_audit_tmp" < "$raw_graph_tmp" > "$project_tmp"
python3 tools/ValidateGraph.py "$project_tmp" --comparisons "$manifest"
python3 tools/GenerateExactMergeChecks.py "$project_tmp" > "$checks_tmp"
lake env lean "$checks_tmp"
python3 tools/BuildCatalogue.py < "$project_tmp" > "$catalogue_tmp"
mv "$project_tmp" MathNetwork/Graph/project.json
mv "$catalogue_tmp" MathNetwork/Graph/theorem-catalogue.json
python3 tools/ExportSourceRevisions.py lake-manifest.json > MathNetwork/Graph/source-revisions.json
python3 tools/GraphFreshness.py --write MathNetwork/Graph/extraction-inputs.json
