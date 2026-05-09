# Statement Contract

## Main Target

Formalize the admissible-carry construction from
`docs/reference/admissible_carry_note_erdos875.tex`.

The public mathematical endpoint is:

- There exists an infinite paper-admissible set `A = {a_1 < a_2 < ...} ⊂ ℕ`.
- Its one-based increasing enumeration satisfies
  `a_{n+1} - a_n = o(n^(3 + 2 * sqrt 2))`.
- For the prefixed construction with initial terms `{1, 2}`, the
  zero-indexed Lean enumeration `a : ℕ → ℕ` satisfies the pointwise bound
  `∀ n, a (n + 1) - a n ≤ (n + 1)^(3 + 2 * sqrt 2)` after casting to `ℝ`.

## Lean-Normalized Route

Use the zero-indexed admissible-carry route documented in
`docs/reference/admissible_carry_note_erdos875.tex`.

The internal construction is an abstract `LegalSchedule` with finite stages `F j`,
scales `M j`, counts `N j`, and block lengths `k j`. The concrete schedule is
instantiated in `AdmissibleCarry.ConcreteCeil`; the all-index endpoint uses the
shifted prefixed tail under `AdmissibleCarry.Prefixed`.

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
- `AdmissibleCarry.Prefixed.pref_gap_tendsto`
- `AdmissibleCarry.Prefixed.pref_all_gap_bound`
- `AdmissibleCarry.Prefixed.pref_final_construction`

The public set wrappers are `AdmissibleCarry.finalSet_infinite`,
`AdmissibleCarry.finalSet_admissible`, and the bundled endpoint
`AdmissibleCarry.final_construction` for the original eventual construction.
The published all-index wrappers are
`AdmissibleCarry.Prefixed.prefFinalSet_infinite`,
`AdmissibleCarry.Prefixed.prefFinalSet_admissible`, and
`AdmissibleCarry.Prefixed.pref_final_construction`.

## Non-Goals

- No all-index theorem for `concreteSchedule.seq`; its first gap is too large.
- No relative-gap theorem `a_{n+1}/a_n → 1`.
- No optimality claim for exponent `3 + 2 * sqrt 2`.
