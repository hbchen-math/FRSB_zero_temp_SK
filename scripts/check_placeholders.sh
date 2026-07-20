#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

if rg -n '^[[:space:]]*(sorry|admit)([[:space:]]|$)|:= by[[:space:]]+(sorry|admit)([[:space:]]|$)' FRSB.lean FRSB; then
  echo "Found a proof placeholder." >&2
  exit 1
fi

axioms="$(rg -n '^[[:space:]]*axiom[[:space:]]' FRSB.lean FRSB || true)"
unexpected_axioms="$(printf '%s\n' "$axioms" \
  | rg -v '^FRSB/Paper/ExternalInputs\.lean:[0-9]+:axiom lopatto_positiveTemperatureStructure ' \
  | rg -v '^FRSB/Paper/ExternalInputs\.lean:[0-9]+:axiom cited_positiveTemperatureEndpointData ' \
  | rg -v '^FRSB/Paper/ExternalInputs\.lean:[0-9]+:axiom zeroTemperatureParisiMinimizer ' \
  | rg -v '^FRSB/Paper/ExternalInputs\.lean:[0-9]+:axiom chenHandschyLerman_zeroField_zero_mem_stieltjesSupport ' \
  | rg -v '^FRSB/Paper/ExternalInputs\.lean:[0-9]+:axiom zeroTemperature_internalGapAnalyticInputs ' \
  | rg -v '^FRSB/Paper/ExternalInputs\.lean:[0-9]+:axiom zeroTemperature_terminalGapAnalyticInputs ' \
  | rg -v '^FRSB/Paper/ExternalInputs\.lean:[0-9]+:axiom zeroTemperature_smoothDensityAnalyticData ' \
  || true)"

if [[ -n "$unexpected_axioms" ]]; then
  printf '%s\n' "$unexpected_axioms" >&2
  echo "Found an axiom outside the external-literature whitelist." >&2
  exit 1
fi

axiom_count="$(printf '%s\n' "$axioms" | sed '/^$/d' | wc -l)"
if [[ "$axiom_count" -ne 7 ]]; then
  echo "Expected exactly seven whitelisted external axioms; found $axiom_count." >&2
  exit 1
fi

echo "No sorry or admit declarations found; the external-axiom whitelist is exact."
