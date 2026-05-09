import AdmissibleCarry

/-!
`Solution` is the module named in `comparator.json`.

The public theorem checked by comparator is proved from the concrete
`AdmissibleCarry.Prefixed.pref_final_construction` endpoint.
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
        (∀ n : Nat,
          ((a (n + 1) - a n : Nat) : ℝ) ≤
            ((n + 1 : Nat) : ℝ) ^ (3 + 2 * Real.sqrt 2)) := by
  refine
    ⟨Prefixed.prefFinalSet, Prefixed.prefFinalSet_infinite,
      Prefixed.prefFinalSet_admissible, Prefixed.prefSeq, ?_, ?_, ?_, ?_⟩
  · rfl
  · exact Prefixed.prefSeq_strictMono
  · simpa [LegalSchedule.gapExponent] using Prefixed.pref_gap_tendsto
  · simpa [LegalSchedule.gapExponent] using Prefixed.pref_all_gap_bound

end AdmissibleCarry
