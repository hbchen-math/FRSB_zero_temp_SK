#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

tex_file="${1:-my_paper.tex}"

if [[ ! -f "$tex_file" ]]; then
  echo "TeX file not found: $tex_file" >&2
  exit 1
fi

missing=0
active_tex="$(mktemp)"
trap 'rm -f "$active_tex"' EXIT

# TeX deliberately keeps some draft material between `\iffalse` and `\fi`.
# A tracked result must occur in the compiled branch, not merely somewhere in
# the source file.  The manuscript does not nest these conditionals.
awk '
  /\\iffalse/ { inactive = 1; next }
  /\\fi/      { inactive = 0; next }
  !inactive    { print }
' "$tex_file" > "$active_tex"

while IFS= read -r label; do
  if ! rg -q -F "\\label{$label}" "$active_tex"; then
    echo "Tracked label is missing from the active TeX source: $label" >&2
    missing=1
  fi
done < <(
  rg -o --no-filename '`(thm|prop|lem|eq):[^`]+`' README.md FORMALIZATION_STATUS.md AXIOMS.md FRSB \
    | sed -E 's/^`|`$//g' \
    | sort -u
)

if [[ "$missing" -ne 0 ]]; then
  exit 1
fi

echo "Every tracked LaTeX label occurs in the active (non-iffalse) part of $tex_file."
