#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

lean_files=(FRSB.lean)
while IFS= read -r -d '' file; do
  lean_files+=("$file")
done < <(find FRSB -type f -name '*.lean' -print0)

if grep -En '^[[:space:]]*(sorry|admit)([[:space:]]|$)|:= by[[:space:]]+(sorry|admit)([[:space:]]|$)' "${lean_files[@]}"; then
  echo "Found a proof placeholder." >&2
  exit 1
fi

axioms="$(grep -HnE '^[[:space:]]*axiom[[:space:]]' "${lean_files[@]}" || true)"
unexpected_axioms="$(printf '%s\n' "$axioms" \
  | grep -Ev '^FRSB/Paper/ExternalInputs\.lean:[0-9]+:axiom lopatto_positiveTemperatureStructure ' \
  | grep -Ev '^FRSB/Paper/ExternalInputs\.lean:[0-9]+:axiom cited_positiveTemperatureEndpointData ' \
  | grep -Ev '^FRSB/Paper/ExternalInputs\.lean:[0-9]+:axiom zeroTemperatureParisiMinimizer ' \
  | grep -Ev '^FRSB/Paper/ExternalInputs\.lean:[0-9]+:axiom chenHandschyLerman_zeroField_zero_mem_stieltjesSupport ' \
  | grep -Ev '^FRSB/Paper/ExternalInputs\.lean:[0-9]+:axiom zeroTemperature_internalGapAnalyticInputs ' \
  | grep -Ev '^FRSB/Paper/ExternalInputs\.lean:[0-9]+:axiom zeroTemperature_terminalGapAnalyticInputs ' \
  | grep -Ev '^FRSB/Paper/ExternalInputs\.lean:[0-9]+:axiom zeroTemperature_smoothDensityAnalyticData ' \
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
