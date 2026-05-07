# Statement Contract

## Main Target

Formalize the admissible-carry construction from
`docs/reference/admissible_carry_note_erdos875.tex`.

The public mathematical endpoint is:

- There exists an infinite paper-admissible set `A = {a_1 < a_2 < ...} ⊂ ℕ`.
- Its one-based increasing enumeration satisfies
  `a_{n+1} - a_n = o(n^(3 + 2 * sqrt 2))`.
- Consequently `a_{n+1} - a_n ≤ n^(3 + 2 * sqrt 2)` for all sufficiently large `n`.

## Lean-Normalized Route

Use the zero-indexed admissible-carry route documented in
`docs/reference/admissible_carry_note_erdos875.tex`.

The internal construction is an abstract `LegalSchedule` with finite stages `F j`,
scales `M j`, counts `N j`, and block lengths `k j`. The concrete schedule is
instantiated in `AdmissibleCarry.ConcreteCeil`.

## Internal Theorems

Primary internal endpoints:

- `AdmissibleCarry.local_carry_zsmall`
- `AdmissibleCarry.local_carry_range`
- `AdmissibleCarry.closure_step`
- `AdmissibleCarry.LegalSchedule.stage_invariant`
- `AdmissibleCarry.LegalSchedule.uniform_gap`
- `AdmissibleCarry.LegalSchedule.abstract_gap_little_o`
- `AdmissibleCarry.final_gap_tendsto`
- `AdmissibleCarry.final_gap_eventually_le_rpow`
- `AdmissibleCarry.final_construction`

The public set wrappers are `AdmissibleCarry.finalSet_infinite`,
`AdmissibleCarry.finalSet_admissible`, and the bundled endpoint
`AdmissibleCarry.final_construction`.

## Non-Goals

- No small-`n` absolute-gap claim.
- No relative-gap theorem `a_{n+1}/a_n → 1`.
- No optimality claim for exponent `3 + 2 * sqrt 2`.
