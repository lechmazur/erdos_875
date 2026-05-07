# Decisions

## 2026-05-07: Project Name

Use `AdmissibleCarry` as the Lean project and namespace. This matches the main
construction rather than the problem number.

## 2026-05-07: Active Reference Version

Use `docs/reference/admissible_carry_note_lean_formalization_v10.tex` as the
Lean blueprint and `docs/reference/admissible_carry_note_erdos875_new_version.tex`
as the mathematical source.

## 2026-05-07: Initial Import Policy

Use broad `import Mathlib` in the first scaffold. Narrow imports only after the
module interfaces compile and the API dependencies are known.

## 2026-05-07: Strengthen Legal Schedule Growth

Strengthen `LegalSchedule.growth` from `2 * N_j < k_j` to `4 * N_j < k_j`.
The closure step consumes `OldSmall sigma M k`, and with the stage bound
`sigma ≤ M * N_j` the exact downstream theorem needs `4 * N_j < k_j`.
The concrete ceiling schedule proves this stronger inequality, so this is an
internal interface correction rather than a weakening of the public theorem.
