import AdmissibleCarry.CoeffDiff
import AdmissibleCarry.AsymptoticAbstract

/-!
Trusted public statement for the Erdos 875 admissible-carry formalization.

This file is intentionally statement-only for comparator-style audits. It uses
the public vocabulary from the submitted project and states only the endpoint
that comparator checks.
-/

noncomputable section

namespace AdmissibleCarry

open Filter

/--
Public bundled endpoint.

There is an infinite paper-admissible set `A` with a strict increasing
enumeration `a`; its consecutive gaps satisfy the normalized limit and the
eventual real gap bound with exponent `3 + 2 * sqrt 2`.
-/
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
  sorry

end AdmissibleCarry
