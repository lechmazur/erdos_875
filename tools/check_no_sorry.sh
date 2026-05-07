#!/usr/bin/env bash
set -euo pipefail

if rg --glob '*.lean' --glob '!Challenge.lean' --glob '!Scratch/**' \
    --glob '!.lake/**' --glob '!.git/**' \
    '\bsorry\b|\badmit\b|\baxiom\b|unsafe' AdmissibleCarry.lean AdmissibleCarry; then
  echo "Found sorry/admit/axiom/unsafe occurrences." >&2
  exit 1
fi

echo "No sorry/admit/axiom/unsafe occurrences found in AdmissibleCarry Lean files."
