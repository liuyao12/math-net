#!/usr/bin/env bash
set -euo pipefail

if (($# == 0)); then
  echo "usage: tools/extract.sh Declaration.Name [...]" >&2
  exit 2
fi

names=$(printf '%s,' "$@")
names=${names%,}
MATHNET_DECLARATIONS="$names" exec lake env lean tools/Extract.lean
