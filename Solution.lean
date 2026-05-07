import AdmissibleCarry

/-!
`Solution` is the module named in `comparator.json`.

The public theorem checked by comparator is proved from the concrete
`AdmissibleCarry.final_construction` endpoint.
-/

noncomputable section

namespace AdmissibleCarry

open Filter

theorem published_final_construction :
    ∃ A : Set Nat,
      A.Infinite ∧
      (∀ U V : Finset Nat, (∀ u ∈ U, u ∈ A) → (∀ v ∈ V, v ∈ A) →
        U.sum id = V.sum id → U.card = V.card) ∧
      ∃ a : Nat → Nat,
        Set.range a = A ∧
        StrictMono a ∧
        Filter.Tendsto
          (fun n : Nat =>
            ((a (n + 1) - a n : Nat) : ℝ) /
              ((n + 1 : Nat) : ℝ) ^ (3 + 2 * Real.sqrt 2))
          Filter.atTop (nhds 0) ∧
        ∀ᶠ n : Nat in Filter.atTop,
          ((a (n + 1) - a n : Nat) : ℝ) ≤
            ((n + 1 : Nat) : ℝ) ^ (3 + 2 * Real.sqrt 2) := by
  refine ⟨finalSet, finalSet_infinite, finalSet_admissible, concreteSchedule.seq, ?_, ?_, ?_, ?_⟩
  · rfl
  · exact concreteSchedule.strictMono_seq
  · simpa [LegalSchedule.gapExponent] using final_gap_tendsto
  · simpa [LegalSchedule.gapExponent] using final_gap_eventually_le_rpow

end AdmissibleCarry
