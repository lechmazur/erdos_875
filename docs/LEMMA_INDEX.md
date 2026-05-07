# Lemma Index

## `local_carry_zsmall`

Lemma name: `AdmissibleCarry.local_carry_zsmall`
Source location: v10 blueprint, preferred two-sided local carry theorem.
Purpose: recover local cardinality defect from a small error near a multiple of `Q m`.
Variables: `m : Nat`, `eps : Nat → Sign3`, `u w : Int`.
Hypotheses: `2 ≤ m`, `localValue m eps = (Q m : Int) * w - u`,
`ZLtQuarter m u`, `ZLtHalf m w`.
Lean-ish statement: `localGrade m eps = w - u`.
Dependencies: defect totals, shift arithmetic, positive/negative shift impossibility.
Expected mathlib APIs: finite sums over `Finset.range`, `omega`, `linarith`.
Coercion/domain hazards: `Nat`/`Int` casts and two-sided bounds.
Proof strategy: follow v10 local carry order.
Validation command: `lake build AdmissibleCarry.LocalCarry`.
Status: proved.

## `local_carry_range_of_two_le`

Lemma name: `AdmissibleCarry.local_carry_range_of_two_le`
Source location: v10 local carry wrapper, specialized to block lengths used by closure.
Purpose: convert `CDiff` and NatAbs smallness into the local carry conclusion when `2 ≤ m`.
Variables: `m : Nat`, `t y u w : Int`.
Hypotheses: `2 ≤ m`, `CDiff m t y`, `y = (Q m : Int) * w - u`,
`USmall m u`, `WSmall m w`.
Lean-ish statement: `t = w - u`.
Dependencies: `local_carry_zsmall`, `usmall_zltQuarter`, `wsmall_zltHalf`.
Expected mathlib APIs: existential destructuring and equality rewriting.
Coercion/domain hazards: none beyond the z-small theorem.
Proof strategy: checked wrapper around `local_carry_zsmall`.
Validation command: `lake build AdmissibleCarry.LocalCarry`.
Status: proved.

## `local_carry_range`

Lemma name: `AdmissibleCarry.local_carry_range`
Source location: v10 local carry wrapper.
Purpose: public local carry wrapper for all positive block lengths.
Variables: `m : Nat`, `t y u w : Int`.
Hypotheses: `0 < m`, `CDiff m t y`, `y = (Q m : Int) * w - u`,
`USmall m u`, `WSmall m w`.
Lean-ish statement: `t = w - u`.
Dependencies: `local_carry_range_of_two_le`; direct one-element proof for `m = 1`.
Expected mathlib APIs: `omega`, `Int.natAbs_eq_zero`, finite sums over `Finset.range 1`.
Coercion/domain hazards: proving smallness forces `u = w = 0`.
Proof strategy: split on `2 ≤ m`; the only positive non-`2 ≤` case is `m = 1`.
Validation command: `lake build AdmissibleCarry.LocalCarry`.
Status: proved.

## `closure_step`

Lemma name: `AdmissibleCarry.closure_step`
Source location: v10 blueprint, one-step closure.
Purpose: preserve the cached carry invariant after adjoining a dilated local block.
Variables: `A : Finset Nat`, `M sigma k : Nat`.
Hypotheses: `2 ≤ k`, old `CarryState`, old smallness, new smallness.
Lean-ish statement: `CarryState (stepSet A M k) (M * Q k) ... ∧ NewSmall ...`.
Dependencies: block separation, dilation bridge, local carry.
Expected mathlib APIs: `Finset.image`, `Finset.union`, integer divisibility/casts.
Coercion/domain hazards: decomposing signed differences over a union.
Proof strategy: split old and new block components, extract quotient, apply local carry.
Validation command: `lake build AdmissibleCarry.Closure`.
Status: proved.

## `stage_admissible`

Lemma name: `AdmissibleCarry.LegalSchedule.stage_admissible`
Source location: v10 stage invariant.
Purpose: derive finite admissibility of every stage from the carry invariant.
Variables: `S : LegalSchedule`, `j : Nat`.
Hypotheses: none beyond `stage_invariant`.
Lean-ish statement: `AdmFin (S.F j)`.
Dependencies: `stage_invariant`, `CarryState.carry`.
Expected mathlib APIs: none.
Coercion/domain hazards: quotient `q = 0` for difference value `0`.
Proof strategy: if `Diff (S.F j) t 0`, apply carry with `q = 0` to get `t = 0`.
Validation command: `lake build AdmissibleCarry.Stage`.
Status: proved.

## `two_mul_le_N`

Lemma name: `AdmissibleCarry.LegalSchedule.two_mul_le_N`
Source location: enumeration setup.
Purpose: show the abstract stage counts tend to infinity fast enough for owner existence.
Variables: `S : LegalSchedule`, `j : Nat`.
Hypotheses: `S.k_ge_two`.
Lean-ish statement: `2 * j ≤ S.N j`.
Dependencies: recursive definition of `N`.
Expected mathlib APIs: `omega`.
Coercion/domain hazards: none.
Proof strategy: induction on `j`.
Validation command: `lake build AdmissibleCarry.Enumeration`.
Status: proved.

## `owner` witness

Lemma name: witness inside `AdmissibleCarry.LegalSchedule.owner`
Source location: enumeration setup.
Purpose: provide the `Nat.find` existence proof for the first stage with `n < N j`.
Variables: `S : LegalSchedule`, `n : Nat`.
Hypotheses: `two_mul_le_N`.
Lean-ish statement: `∃ j, n < S.N (j + 1)`.
Dependencies: `two_mul_le_N`.
Expected mathlib APIs: `omega`.
Coercion/domain hazards: none.
Proof strategy: use witness `n + 1`.
Validation command: `lake build AdmissibleCarry.Enumeration`.
Status: proved.

## `owner_spec` / `owner_min`

Lemma name: `AdmissibleCarry.LegalSchedule.owner_spec`,
`AdmissibleCarry.LegalSchedule.owner_min`
Source location: enumeration setup.
Purpose: named `Nat.find` facts for the block owner.
Variables: `S : LegalSchedule`, `n j : Nat`.
Hypotheses: for `owner_min`, `j < S.owner n`.
Lean-ish statement: `n < S.N (S.owner n + 1)` and, for `j < owner n`,
`S.N (j + 1) ≤ n`.
Dependencies: `Nat.find_spec`, `Nat.find_min`.
Expected mathlib APIs: `Nat.le_of_not_gt`.
Coercion/domain hazards: none.
Proof strategy: direct wrappers around `Nat.find`.
Validation command: `lake build AdmissibleCarry.Enumeration`.
Status: proved.

## `exact_block_formula`

Lemma name: `AdmissibleCarry.LegalSchedule.exact_block_formula`
Source location: v10 enumeration layer.
Purpose: rewrite sequence values by block and offset.
Variables: `S : LegalSchedule`, `j i : Nat`.
Hypotheses: `i < S.k j`.
Lean-ish statement: `S.seq (S.N j + i) = S.elem j i`.
Dependencies: `owner_eq_of_lt`, `offset_eq_of_lt`.
Expected mathlib APIs: `Nat.find_eq_iff`, `omega`.
Coercion/domain hazards: owner is the first `j` with `n < N (j + 1)`.
Proof strategy: prove owner and offset separately, then `simp`.
Validation command: `lake build AdmissibleCarry.Enumeration`.
Status: proved.

## `uniform_gap`

Lemma name: `AdmissibleCarry.LegalSchedule.uniform_gap`
Source location: v10 enumeration layer.
Purpose: exact consecutive gap formula inside a block and across the next block boundary.
Variables: `S : LegalSchedule`, `j i : Nat`.
Hypotheses: `i < S.k j`.
Lean-ish statement:
`S.seq (S.N j + i + 1) - S.seq (S.N j + i) = S.M j * (S.k j + 1)`.
Dependencies: `exact_block_formula`, `elem_succ`, `elem_boundary_gap`.
Expected mathlib APIs: `ring`, `nlinarith`, `omega`.
Coercion/domain hazards: natural-number subtraction in the boundary case.
Proof strategy: split on `i + 1 < S.k j` versus `i + 1 = S.k j`.
Validation command: `lake build AdmissibleCarry.Enumeration`.
Status: proved.

## `uniform_gap_at`

Lemma name: `AdmissibleCarry.LegalSchedule.uniform_gap_at`
Source location: enumeration layer.
Purpose: pointwise exact gap formula for every sequence index.
Variables: `S : LegalSchedule`, `n : Nat`.
Hypotheses: none.
Lean-ish statement: `S.seq (n + 1) - S.seq n = S.GapAt n`.
Dependencies: `owner_lower`, `offset_lt`, `uniform_gap`.
Expected mathlib APIs: `Nat.find_min`, `omega`.
Coercion/domain hazards: rewriting `n` as `N (owner n) + offset n`.
Proof strategy: prove `offset n < k (owner n)`, apply block `uniform_gap`, rewrite indices.
Validation command: `lake build AdmissibleCarry.Enumeration`.
Status: proved.

## `admSeq`

Lemma name: `AdmissibleCarry.LegalSchedule.admSeq`
Source location: v10 sequence-level admissibility wrapper.
Purpose: prove admissibility for finite sets of sequence indices.
Variables: `S : LegalSchedule`.
Hypotheses: none beyond the legal schedule.
Lean-ish statement: `AdmSeq S.seq`.
Dependencies: `prefix_range`, `strictMono_seq`, `stage_admissible`,
`AdmFin.card_eq_of_sum_eq`.
Expected mathlib APIs: `Finset.image`, `Finset.sum_image`,
`Finset.card_image_of_injOn`, `Finset.add_sum_erase`.
Coercion/domain hazards: choosing one finite stage containing all index supports.
Proof strategy: map both finite index sets into one finite admissible stage, apply
finite admissibility, and pull cardinals back through injectivity.
Validation command: `lake build AdmissibleCarry.Enumeration`.
Status: proved.

## `finalSet_admissible`

Lemma name: `AdmissibleCarry.finalSet_admissible`
Source location: v10 paper set wrapper.
Purpose: convert sequence-level admissibility for `concreteSchedule.seq` into
paper admissibility of `Set.range concreteSchedule.seq`.
Variables: none beyond the concrete schedule.
Hypotheses: finite subsets of the final range with equal sums.
Lean-ish statement: `PaperAdmSet finalSet`.
Dependencies: `LegalSchedule.admSeq`, `LegalSchedule.strictMono_seq`.
Expected mathlib APIs: `Finset.preimage`, `Finset.sum_preimage`,
`Finset.card_preimage`.
Coercion/domain hazards: finite value sets versus finite index sets.
Proof strategy: pull both value sets back to finite index sets under the
injective concrete sequence, apply `admSeq`, and push cardinals back.
Validation command: `lake build AdmissibleCarry.ConcreteCeil`.
Status: proved.

## `finalSet_infinite`

Lemma name: `AdmissibleCarry.finalSet_infinite`
Source location: public set wrapper.
Purpose: record that the final range set is infinite.
Variables: none beyond the concrete schedule.
Hypotheses: none.
Lean-ish statement: `finalSet.Infinite`.
Dependencies: `concreteSchedule.strictMono_seq`.
Expected mathlib APIs: `Set.infinite_range_of_injective`.
Coercion/domain hazards: none.
Proof strategy: the final set is the range of the injective strict-monotone
sequence.
Validation command: `lake build AdmissibleCarry.ConcreteCeil`.
Status: proved.

## `final_gap_tendsto`

Lemma name: `AdmissibleCarry.final_gap_tendsto`
Source location: v10 final theorem.
Purpose: final concrete little-oh gap endpoint.
Variables: none beyond concrete schedule.
Hypotheses: concrete analysis-ready record.
Lean-ish statement: normalized consecutive gap tends to `0` along `atTop`.
Dependencies: concrete schedule inequalities, abstract asymptotic wrapper.
Expected mathlib APIs: `Filter.Tendsto`, `Real.rpow`, `Nat.ceil`.
Coercion/domain hazards: one-based vs zero-based index and real casts.
Proof strategy: prove `final_analysis_ready` for the concrete schedule, then
instantiate `abstract_gap_little_o`.
Validation command: `lake build AdmissibleCarry.ConcreteCeil`.
Status: proved.

## `final_construction`

Lemma name: `AdmissibleCarry.final_construction`
Source location: public endpoint bundle.
Purpose: package the final infinite admissible set, strict enumeration, little-oh
gap endpoint, and eventual power-bound corollary.
Variables: none beyond concrete schedule.
Hypotheses: none.
Lean-ish statement: `finalSet.Infinite ∧ PaperAdmSet finalSet ∧
StrictMono concreteSchedule.seq ∧ final_gap_tendsto statement ∧
final_gap_eventually_le_rpow statement`.
Dependencies: `finalSet_infinite`, `finalSet_admissible`, `final_gap_tendsto`,
`final_gap_eventually_le_rpow`.
Expected mathlib APIs: conjunction introduction.
Coercion/domain hazards: inherited from final gap statements.
Proof strategy: bundle proved endpoints.
Validation command: `lake build AdmissibleCarry.ConcreteCeil`.
Status: proved.

## `final_gap_eventually_le_rpow`

Lemma name: `AdmissibleCarry.final_gap_eventually_le_rpow`
Source location: v10 final theorem, eventual bound corollary.
Purpose: convert the normalized little-oh endpoint into the paper-style eventual
power bound.
Variables: none beyond concrete schedule.
Hypotheses: none.
Lean-ish statement: eventually,
`seq (n + 1) - seq n ≤ (n + 1) ^ (3 + 2 * sqrt 2)` after casting to `ℝ`.
Dependencies: `final_gap_tendsto`.
Expected mathlib APIs: `Filter.Tendsto.eventually_le_const`, `div_le_iff₀`.
Coercion/domain hazards: the denominator is the one-based index `n + 1`.
Proof strategy: use convergence of the normalized ratio to get the ratio
eventually at most `1`, then multiply by the positive denominator.
Validation command: `lake build AdmissibleCarry.ConcreteCeil`.
Status: proved.
