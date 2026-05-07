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
      PaperAdmSet A ∧
      ∃ a : Nat → Nat,
        Set.range a = A ∧
        StrictMono a ∧
        Filter.Tendsto
          (fun n : Nat =>
            ((a (n + 1) - a n : Nat) : ℝ) /
              ((n + 1 : Nat) : ℝ) ^ LegalSchedule.gapExponent)
          Filter.atTop (nhds 0) ∧
        ∀ᶠ n : Nat in Filter.atTop,
          ((a (n + 1) - a n : Nat) : ℝ) ≤
            ((n + 1 : Nat) : ℝ) ^ LegalSchedule.gapExponent := by
  refine ⟨finalSet, finalSet_infinite, finalSet_admissible, concreteSchedule.seq, ?_, ?_, ?_, ?_⟩
  · rfl
  · exact concreteSchedule.strictMono_seq
  · exact final_gap_tendsto
  · exact final_gap_eventually_le_rpow

end AdmissibleCarry
