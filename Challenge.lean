import Mathlib

/-!
Trusted statements for the Erdos 875 admissible-carry formalization.

This file is intentionally statement-oriented for comparator-style audits. It
defines the small public vocabulary used by the final theorem statements and
then states the theorem targets checked against `Solution.lean`.
-/

noncomputable section

namespace AdmissibleCarry

open Filter

def PaperAdmSet (A : Set Nat) : Prop :=
  ∀ U V : Finset Nat, (∀ u, u ∈ U → u ∈ A) → (∀ v, v ∈ V → v ∈ A) →
    U.sum id = V.sum id → U.card = V.card

def cell (m i : Nat) : Nat :=
  1 + i * (m + 1)

def Q (m : Nat) : Nat :=
  m * m + m + 1

structure LegalSchedule where
  k : Nat → Nat
  k_ge_two : ∀ j, 2 ≤ k j
  growth : ∀ j, 4 * (Nat.rec 0 (fun i n => n + k i) j) < k j

namespace LegalSchedule

def N (S : LegalSchedule) : Nat → Nat
  | 0 => 0
  | j + 1 => S.N j + S.k j

def M (S : LegalSchedule) : Nat → Nat
  | 0 => 1
  | j + 1 => S.M j * Q (S.k j)

def elem (S : LegalSchedule) (j i : Nat) : Nat :=
  S.M j * cell (S.k j) i

def owner (S : LegalSchedule) (n : Nat) : Nat :=
  Nat.find (p := fun j => n < S.N (j + 1)) (by
    refine ⟨n, ?_⟩
    sorry)

def offset (S : LegalSchedule) (n : Nat) : Nat :=
  n - S.N (S.owner n)

noncomputable def seq (S : LegalSchedule) (n : Nat) : Nat :=
  elem S (S.owner n) (S.offset n)

noncomputable def theta : Real :=
  1 + Real.sqrt 2

noncomputable def gapExponent : Real :=
  3 + 2 * Real.sqrt 2

end LegalSchedule

def concreteKCore (N : Nat) : Nat :=
  Nat.ceil (2 * (1 + (N : Real)) ^ (1 + Real.sqrt 2))

def concreteN : Nat → Nat
  | 0 => 0
  | j + 1 => concreteN j + concreteKCore (concreteN j)

def concreteK (j : Nat) : Nat :=
  concreteKCore (concreteN j)

def concreteSchedule : LegalSchedule where
  k := concreteK
  k_ge_two := by
    intro j
    sorry
  growth := by
    intro j
    sorry

def finalSet : Set Nat :=
  Set.range concreteSchedule.seq

theorem finalSet_infinite :
    finalSet.Infinite := by
  sorry

theorem finalSet_admissible :
    PaperAdmSet finalSet := by
  sorry

theorem final_gap_tendsto :
    Filter.Tendsto
      (fun n : Nat =>
        ((concreteSchedule.seq (n + 1) - concreteSchedule.seq n : Nat) : Real) /
          ((n + 1 : Nat) : Real) ^ LegalSchedule.gapExponent)
      Filter.atTop (nhds 0) := by
  sorry

theorem final_gap_eventually_le_rpow :
    ∀ᶠ n : Nat in Filter.atTop,
      ((concreteSchedule.seq (n + 1) - concreteSchedule.seq n : Nat) : Real) ≤
        ((n + 1 : Nat) : Real) ^ LegalSchedule.gapExponent := by
  sorry

theorem final_construction :
    finalSet.Infinite ∧
      PaperAdmSet finalSet ∧
      StrictMono concreteSchedule.seq ∧
      Filter.Tendsto
        (fun n : Nat =>
          ((concreteSchedule.seq (n + 1) - concreteSchedule.seq n : Nat) : Real) /
            ((n + 1 : Nat) : Real) ^ LegalSchedule.gapExponent)
        Filter.atTop (nhds 0) ∧
      ∀ᶠ n : Nat in Filter.atTop,
        ((concreteSchedule.seq (n + 1) - concreteSchedule.seq n : Nat) : Real) ≤
          ((n + 1 : Nat) : Real) ^ LegalSchedule.gapExponent := by
  sorry

end AdmissibleCarry
