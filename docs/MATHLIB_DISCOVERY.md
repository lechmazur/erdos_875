# Mathlib Discovery

Durable discoveries go here. Do not paste raw search dumps.

## Initial Imports

- `import Mathlib` is used for the first scaffold to reduce bootstrap friction.
  Later milestones should narrow imports after the relevant APIs are stable.

## Known APIs To Check

- `Finset.sum`
- `Finset.image`
- `Nat.find`
- `Nat.ceil`
- `Real.rpow`
- `Filter.Tendsto`

## Natural Ceiling

- `Nat.le_ceil (a : R) : a ≤ (Nat.ceil a : R)`
- `Nat.ceil_le : Nat.ceil a ≤ n ↔ a ≤ (n : α)`
- `Nat.lt_ceil : n < Nat.ceil a ↔ (n : α) < a`
- For `concreteK_ge_two`, combine `Real.one_le_rpow`, `Nat.le_ceil`, and
  `exact_mod_cast`.
- For `concreteK_growth`, `Nat.lt_ceil.mpr`,
  `Real.rpow_le_rpow_of_exponent_le`, and `Real.le_sqrt` prove the stronger
  `4 * N_j < k_j` schedule inequality.
- `Real.sq_sqrt`, `Real.lt_sqrt`, and
  `Real.rpow_lt_one_of_one_lt_of_neg` close the basic parameter algebra for
  `theta`, `tau`, `gapExponent`, and `rho`.

## Real Asymptotics

- `tendsto_pow_atTop_nhds_zero_of_lt_one`, `le_geom`, and `squeeze_zero`
  package geometric decay of the normalized block quantity `P`.
- `Real.rpow_le_rpow_iff_of_neg` is the clean way to use the lower ceiling
  bound with the negative exponent `2 - tau = -sqrt 2`.
- `Real.mul_rpow`, `Real.rpow_mul`, `Real.rpow_add`, and `Real.rpow_neg`
  normalize the identity
  `2 * (2 * scale ^ theta) ^ (2 - tau) = rho / scale ^ tau`.
- `Filter.Tendsto.const_mul`, composition of `Tendsto`, and
  `Filter.Tendsto.eventually_le_const` convert block-owner decay into the final
  little-oh theorem and eventual power-bound corollary.
- `Filter.tendsto_add_atTop_iff_nat 2` converts the shifted prefixed limit
  `(fun m => prefGapRatio (m + 2)) → 0` back to the full zero-indexed
  prefixed sequence.

## Integer Absolute Values

- `Int.natCast_natAbs (n : Int) : (n.natAbs : Int) = |n|`
- `abs_lt.mp : |a| < b → -b < a ∧ a < b`
- `abs_mul` and `abs_of_nonneg` are enough to convert `4 * u.natAbs < m`
  and `2 * w.natAbs < m` into the v10 two-sided predicates
  `ZLtQuarter m u` and `ZLtHalf m w`.

## Local Carry Wrappers

- Once `local_carry_zsmall` is available, the `2 ≤ m` range wrapper is immediate:
  destructure `CDiff`, rewrite the represented local value, and apply the
  NatAbs firewall lemmas.
- The core local-carry proof is now checked via `three_shift_core`, the
  `defectTotal`/`weightedDefectTotal` identities, a positive shifted
  contradiction, and sign negation for the negative shifted case.

## Enumeration

- `Nat.find_eq_iff`, `Nat.find_spec`, and `Nat.find_min` are enough to package
  the block-owner API.
- `ring`, `nlinarith`, and `omega` close the exact uniform-gap arithmetic once
  the owner and offset facts are named.
- `strictMono_nat_of_lt_succ` turns the positive consecutive-gap theorem into
  global injectivity for `seq`.
- `Finset.add_sum_erase` gives a compact finite-bound witness for index sets:
  every `n ∈ U ∪ V` is at most the sum of `U ∪ V`, so stage
  `sum (U ∪ V) + 1` contains both supports.
- `Finset.card_image_of_injOn` and `Finset.sum_image` transport finite index
  sets through the injective sequence before applying `AdmFin`.
- `Finset.sum_sdiff` and `Finset.card_sdiff_add_card_inter` are enough for the
  generic subset-pair bridge from `AdmFin` to cardinal equality.
- `Finset.preimage`, `Finset.sum_preimage`, and `Finset.card_preimage`
  convert finite subsets of `Set.range seq` back to finite index sets for the
  paper-set wrapper.

## Prefixed Pointwise Bound

- `Real.rpow_lt_rpow_of_exponent_lt` proves `2 ^ theta > 3` and
  `3 ^ tau > 27`.
- `Real.mul_rpow`, `Real.rpow_mul`, and `Real.rpow_add` normalize the direct
  contraction estimate for `prefR`.
- `div_lt_one`, `div_le_div_of_nonneg_left`, and
  `div_le_div_of_nonneg_right` are the useful division forms for turning
  `prefR j < 1` into a pointwise gap bound.

## Closure

- `Finset.sum_union` with a named `Disjoint` proof decomposes old and new block
  coefficients in the carry step.
- `Finset.sum_image` with `Set.InjOn` handles both the local cells and the
  dilation map `fun c => M * c`.
- `Finset.sum_range_id_mul_two`, `Nat.div_mul_cancel`, and
  `Nat.eq_of_mul_eq_mul_left` prove
  `sumN (C k) = (k * k * k + k) / 2`.
- `Int.natAbs_mul` and `Int.natAbs_natCast` convert quotient equations
  `D = (M : Int) * q` into natural bounds on `M * q.natAbs`.
