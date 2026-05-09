# Threshold Ledger

Concrete thresholds and asymptotic constants:

- `theta = 1 + sqrt 2`
- `tau = 2 + sqrt 2`
- `gapExponent = 3 + 2 * sqrt 2`
- `rho = 2 ^ (1 - sqrt 2)` with `0 ≤ rho < 1`
- `scale j = max 1 (N j)`
- concrete `k_j = ceil (2 * (1 + N_j) ^ theta)`
- prefixed tail `tailK j = ceil (2 * (tailN j + 3) ^ theta)`, where
  the total old count is `tailN j + 2`

The first block is intentionally `B_0 = {1, 4}` in zero-indexed Lean notation,
so no small-`n` absolute-gap claim is part of the contract.

Checked asymptotic interfaces:

- lower ceiling bound: `2 * (scale j : ℝ) ^ theta ≤ concreteK j`
- upper ceiling bound: `(concreteK j + 1 : ℝ) ≤ 20 * (scale j : ℝ) ^ theta`
- geometric decay: `P concreteSchedule (j + 1) ≤ rho * P concreteSchedule j`
  with `0 ≤ rho < 1`
- block transfer: normalized `GapAt n` is bounded by a constant multiple of
  `P concreteSchedule (owner n)`, specifically `20 * P concreteSchedule (owner n)`

The concrete asymptotic record `final_analysis_ready` is proved, and
`final_gap_tendsto` follows from the abstract little-oh wrapper.

Prefixed all-index constants:

- `Prefixed.tailK_lower_scale` and `Prefixed.tailK_upper_scale` provide the
  shifted tail estimates used for `Prefixed.tail_gap_ratio_tendsto`.
- `Prefixed.prefR j =
  prefM j * (S.k j + 1) / (S.N j + 3) ^ gapExponent`.
- `Prefixed.pointConst = 3 / 2 ^ theta` with `pointConst < 1`.
- `Prefixed.prefR_zero_lt_one` and
  `Prefixed.prefR_succ_le_const_mul` prove `Prefixed.prefR_lt_one`.
- `Prefixed.pref_all_gap_bound` gives the pointwise bound for every
  zero-indexed `n`.
