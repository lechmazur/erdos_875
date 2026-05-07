# Threshold Ledger

Concrete thresholds and asymptotic constants:

- `theta = 1 + sqrt 2`
- `tau = 2 + sqrt 2`
- `gapExponent = 3 + 2 * sqrt 2`
- `rho = 2 ^ (1 - sqrt 2)` with `0 ≤ rho < 1`
- `scale j = max 1 (N j)`
- concrete `k_j = ceil (2 * (1 + N_j) ^ theta)`

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
