# Route Status

This file records proof-route state, not detailed progress.

## Active Route

- `v10 admissible carry route`: zero-indexed stages, range-sum local blocks,
  two-sided local carry, cached `CarryState`, block-owner enumeration, and
  max-one scale asymptotics. Status: complete through the bundled
  `final_construction` endpoint. Source:
  `docs/reference/admissible_carry_note_erdos875.tex`.

- `prefixed all-index route`: shifted tail schedule with
  `tailK j = ceil (2 * (tailN j + 3)^theta)`, fixed prefix `{1, 2}`,
  final sequence `1, 2, 4 * S.seq 0, 4 * S.seq 1, ...`, and direct
  pointwise gap proof via `prefR`. Status: complete through
  `AdmissibleCarry.Prefixed.pref_final_construction`.

## Abandoned Routes

- None yet.

## Conditional Escape Hatches

- None yet.
