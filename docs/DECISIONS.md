# Decisions

## 2026-05-07: Project Name

Use `AdmissibleCarry` as the Lean project and namespace. This matches the main
construction rather than the problem number.

## 2026-05-07: Active Reference Note

Use `docs/reference/admissible_carry_note_erdos875.tex` as the published
reference note and mathematical source for the checked construction.

## 2026-05-07: Initial Import Policy

Use broad `import Mathlib` in the first scaffold. Narrow imports only after the
module interfaces compile and the API dependencies are known.

## 2026-05-07: Strengthen Legal Schedule Growth

Strengthen `LegalSchedule.growth` from `2 * N_j < k_j` to `4 * N_j < k_j`.
The closure step consumes `OldSmall sigma M k`, and with the stage bound
`sigma ≤ M * N_j` the exact downstream theorem needs `4 * N_j < k_j`.
The concrete ceiling schedule proves this stronger inequality, so this is an
internal interface correction rather than a weakening of the public theorem.

## 2026-05-09: Add Prefixed All-Index Endpoint

Do not strengthen `concreteSchedule.seq` to an all-index gap theorem: its first
gap is `3`, while the zero-indexed bound at `n = 0` is `1`.  Instead add the
separate prefixed construction matching the published note: start from `{1, 2}`,
use initial modulus `4`, append `4 * S.seq m` from the shifted tail schedule,
and prove the bundled endpoint
`AdmissibleCarry.Prefixed.pref_final_construction`.  The trusted
`Challenge.lean` and proof `Solution.lean` now expose the all-index public
statement.
