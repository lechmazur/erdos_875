import Mathlib

/-!
Trusted public statement for the Erdos 875 admissible-carry formalization.

This file is intentionally statement-only for comparator-style audits. It
imports only `Mathlib` and states the public endpoint checked against
`Solution.lean`.
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
  sorry

end AdmissibleCarry
