#!/usr/bin/env bash
set -euo pipefail

ROOT="${1:-.}"

echo "Lean imports under $ROOT:"
rg -n --glob '*.lean' --glob '!*.lake/**' --glob '!.git/**' '^import ' "$ROOT" || true

echo
echo "Duplicate imports in top-level AdmissibleCarry.lean, if any:"
if [[ -f "$ROOT/AdmissibleCarry.lean" ]]; then
  sort "$ROOT/AdmissibleCarry.lean" | uniq -d || true
fi
