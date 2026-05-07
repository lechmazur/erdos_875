import AdmissibleCarry.Signs

/-!
# Finite coefficient differences

This file defines signed coefficients on a finite set and the global graded
difference relation used by the carry invariant.
-/

namespace AdmissibleCarry

open scoped BigOperators

structure CoeffOn (A : Finset Nat) where
  sign : Nat → Sign3
  zero_of_not_mem : ∀ n, n ∉ A → sign n = Sign3.zero

namespace CoeffOn

def neg {A : Finset Nat} (c : CoeffOn A) : CoeffOn A where
  sign n := Sign3.opp (c.sign n)
  zero_of_not_mem n hn := by simp [c.zero_of_not_mem n hn]

end CoeffOn

def sumN (A : Finset Nat) : Nat :=
  A.sum id

def grade (A : Finset Nat) (c : CoeffOn A) : Int :=
  A.sum fun n => Sign3.sgn (c.sign n)

def value (A : Finset Nat) (c : CoeffOn A) : Int :=
  A.sum fun n => Sign3.sgn (c.sign n) * (n : Int)

def Diff (A : Finset Nat) (t x : Int) : Prop :=
  ∃ c : CoeffOn A, grade A c = t ∧ value A c = x

def AdmFin (A : Finset Nat) : Prop :=
  ∀ ⦃t : Int⦄, t ≠ 0 → ¬ Diff A t 0

def AdmSeq (a : Nat → Nat) : Prop :=
  ∀ U V : Finset Nat, U.sum a = V.sum a → U.card = V.card

def PaperAdmSet (A : Set Nat) : Prop :=
  ∀ U V : Finset Nat, (∀ u ∈ U, u ∈ A) → (∀ v ∈ V, v ∈ A) →
    U.sum id = V.sum id → U.card = V.card

theorem sign_mul_natAbs_le (s : Sign3) (n : Nat) :
    (Sign3.sgn s * (n : Int)).natAbs ≤ n := by
  cases s <;> simp [Sign3.sgn]

theorem value_natAbs_le_sumN (A : Finset Nat) (c : CoeffOn A) :
    (value A c).natAbs ≤ sumN A := by
  dsimp [value, sumN]
  calc
    (∑ n ∈ A, Sign3.sgn (c.sign n) * (n : Int)).natAbs
        ≤ ∑ n ∈ A, (Sign3.sgn (c.sign n) * (n : Int)).natAbs :=
      Int.natAbs_sum_le A _
    _ ≤ ∑ n ∈ A, n := by
      apply Finset.sum_le_sum
      intro n _hn
      exact sign_mul_natAbs_le (c.sign n) n

def pairCoeff (A P N : Finset Nat)
    (hP : ∀ n, n ∈ P → n ∈ A) (hN : ∀ n, n ∈ N → n ∈ A) : CoeffOn A where
  sign n := if n ∈ P then Sign3.pos else if n ∈ N then Sign3.neg else Sign3.zero
  zero_of_not_mem n hn := by
    have hnP : n ∉ P := fun hp => hn (hP n hp)
    have hnN : n ∉ N := fun hp => hn (hN n hp)
    simp [hnP, hnN]

theorem grade_pairCoeff {A P N : Finset Nat}
    (hP : ∀ n, n ∈ P → n ∈ A) (hN : ∀ n, n ∈ N → n ∈ A)
    (hdisj : Disjoint P N) :
    grade A (pairCoeff A P N hP hN) = (P.card : Int) - (N.card : Int) := by
  dsimp [grade]
  have hsubset : P ∪ N ⊆ A := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hP x hx
    · exact hN x hx
  rw [← Finset.sum_subset hsubset]
  · rw [Finset.sum_union hdisj]
    have hPsum :
        (∑ x ∈ P, Sign3.sgn ((pairCoeff A P N hP hN).sign x)) = (P.card : Int) := by
      calc
        (∑ x ∈ P, Sign3.sgn ((pairCoeff A P N hP hN).sign x)) =
            P.card • (1 : Int) := by
          apply Finset.sum_eq_card_nsmul
          intro x hx
          simp [pairCoeff, hx]
        _ = (P.card : Int) := by simp
    have hNsum :
        (∑ x ∈ N, Sign3.sgn ((pairCoeff A P N hP hN).sign x)) = -(N.card : Int) := by
      calc
        (∑ x ∈ N, Sign3.sgn ((pairCoeff A P N hP hN).sign x)) =
            N.card • (-1 : Int) := by
          apply Finset.sum_eq_card_nsmul
          intro x hx
          have hxP : x ∉ P := (Finset.disjoint_left.mp hdisj.symm) hx
          simp [pairCoeff, hx, hxP]
        _ = -(N.card : Int) := by simp
    rw [hPsum, hNsum]
    ring
  · intro x _hxA hxnot
    have hxP : x ∉ P := fun hp => hxnot (Finset.mem_union_left N hp)
    have hxN : x ∉ N := fun hn => hxnot (Finset.mem_union_right P hn)
    simp [pairCoeff, hxP, hxN]

theorem value_pairCoeff {A P N : Finset Nat}
    (hP : ∀ n, n ∈ P → n ∈ A) (hN : ∀ n, n ∈ N → n ∈ A)
    (hdisj : Disjoint P N) :
    value A (pairCoeff A P N hP hN) =
      ((P.sum (fun x : Nat => x) : Nat) : Int) -
        ((N.sum (fun x : Nat => x) : Nat) : Int) := by
  dsimp [value]
  have hsubset : P ∪ N ⊆ A := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hP x hx
    · exact hN x hx
  rw [← Finset.sum_subset hsubset]
  · rw [Finset.sum_union hdisj]
    have hPsum :
        (∑ x ∈ P, Sign3.sgn ((pairCoeff A P N hP hN).sign x) * (x : Int)) =
          ((P.sum (fun x : Nat => x) : Nat) : Int) := by
      calc
        (∑ x ∈ P, Sign3.sgn ((pairCoeff A P N hP hN).sign x) * (x : Int)) =
            ∑ x ∈ P, (x : Int) := by
          apply Finset.sum_congr rfl
          intro x hx
          simp [pairCoeff, hx]
        _ = ((P.sum (fun x : Nat => x) : Nat) : Int) := by simp
    have hNsum :
        (∑ x ∈ N, Sign3.sgn ((pairCoeff A P N hP hN).sign x) * (x : Int)) =
          -((N.sum (fun x : Nat => x) : Nat) : Int) := by
      calc
        (∑ x ∈ N, Sign3.sgn ((pairCoeff A P N hP hN).sign x) * (x : Int)) =
            ∑ x ∈ N, -(x : Int) := by
          apply Finset.sum_congr rfl
          intro x hx
          have hxP : x ∉ P := (Finset.disjoint_left.mp hdisj.symm) hx
          simp [pairCoeff, hx, hxP]
        _ = -((N.sum (fun x : Nat => x) : Nat) : Int) := by
          simp [Finset.sum_neg_distrib]
    rw [hPsum, hNsum]
    ring
  · intro x _hxA hxnot
    have hxP : x ∉ P := fun hp => hxnot (Finset.mem_union_left N hp)
    have hxN : x ∉ N := fun hn => hxnot (Finset.mem_union_right P hn)
    simp [pairCoeff, hxP, hxN]

theorem diff_pairCoeff {A P N : Finset Nat}
    (hP : ∀ n, n ∈ P → n ∈ A) (hN : ∀ n, n ∈ N → n ∈ A)
    (hdisj : Disjoint P N) :
    Diff A ((P.card : Int) - (N.card : Int))
      (((P.sum (fun x : Nat => x) : Nat) : Int) -
        ((N.sum (fun x : Nat => x) : Nat) : Int)) := by
  exact ⟨pairCoeff A P N hP hN, grade_pairCoeff hP hN hdisj, value_pairCoeff hP hN hdisj⟩

theorem AdmFin.card_eq_of_sum_eq {A U V : Finset Nat} (hAdm : AdmFin A)
    (hU : ∀ n, n ∈ U → n ∈ A) (hV : ∀ n, n ∈ V → n ∈ A)
    (hsum : U.sum (fun x : Nat => x) = V.sum (fun x : Nat => x)) :
    U.card = V.card := by
  by_contra hne
  let P := U \ V
  let N := V \ U
  have hP : ∀ n, n ∈ P → n ∈ A := by
    intro n hn
    exact hU n (Finset.mem_sdiff.mp hn).1
  have hN : ∀ n, n ∈ N → n ∈ A := by
    intro n hn
    exact hV n (Finset.mem_sdiff.mp hn).1
  have hdisj : Disjoint P N := by
    rw [Finset.disjoint_left]
    intro n hnP hnN
    exact (Finset.mem_sdiff.mp hnP).2 (Finset.mem_sdiff.mp hnN).1
  have hcardU : (P.card : Int) + ((U ∩ V).card : Int) = (U.card : Int) := by
    dsimp [P]
    exact_mod_cast Finset.card_sdiff_add_card_inter U V
  have hcardV : (N.card : Int) + ((U ∩ V).card : Int) = (V.card : Int) := by
    dsimp [N]
    have h := Finset.card_sdiff_add_card_inter V U
    rw [Finset.inter_comm] at h
    exact_mod_cast h
  have hgrade_ne : ((P.card : Int) - (N.card : Int)) ≠ 0 := by
    intro hzero
    apply hne
    omega
  have hsumU :
      (U \ V).sum (fun x : Nat => x) + (U ∩ V).sum (fun x : Nat => x) =
        U.sum (fun x : Nat => x) := by
    simpa [Finset.sdiff_inter_self_left] using
      (Finset.sum_sdiff (s₁ := U ∩ V) (s₂ := U) (f := fun x : Nat => x)
        (Finset.inter_subset_left))
  have hsumV :
      (V \ U).sum (fun x : Nat => x) + (U ∩ V).sum (fun x : Nat => x) =
        V.sum (fun x : Nat => x) := by
    simpa [Finset.inter_comm, Finset.sdiff_inter_self_left] using
      (Finset.sum_sdiff (s₁ := V ∩ U) (s₂ := V) (f := fun x : Nat => x)
        (Finset.inter_subset_left))
  have hsumU_int :
      ((((U \ V).sum (fun x : Nat => x) + (U ∩ V).sum (fun x : Nat => x) : Nat) : Int) =
        ((U.sum (fun x : Nat => x) : Nat) : Int)) := by
    exact_mod_cast hsumU
  have hsumV_int :
      ((((V \ U).sum (fun x : Nat => x) + (U ∩ V).sum (fun x : Nat => x) : Nat) : Int) =
        ((V.sum (fun x : Nat => x) : Nat) : Int)) := by
    exact_mod_cast hsumV
  have hsum_int :
      ((U.sum (fun x : Nat => x) : Nat) : Int) =
        ((V.sum (fun x : Nat => x) : Nat) : Int) := by
    exact_mod_cast hsum
  norm_num [Nat.cast_add] at hsumU_int hsumV_int
  have hval0 :
      (((P.sum (fun x : Nat => x) : Nat) : Int) -
          ((N.sum (fun x : Nat => x) : Nat) : Int)) = 0 := by
    simp only [Nat.cast_sum]
    dsimp [P, N]
    linarith
  simp only [Nat.cast_sum] at hval0
  have hdiff := diff_pairCoeff hP hN hdisj
  have hdiff0 : Diff A ((P.card : Int) - (N.card : Int)) 0 := by
    simpa [hval0] using hdiff
  exact (hAdm hgrade_ne hdiff0).elim

theorem diff_neg {A : Finset Nat} {t x : Int} (h : Diff A t x) :
    Diff A (-t) (-x) := by
  rcases h with ⟨c, ht, hx⟩
  refine ⟨c.neg, ?_, ?_⟩
  · dsimp [grade, CoeffOn.neg] at ht ⊢
    simp only [Sign3.sgn_opp]
    rw [Finset.sum_neg_distrib]
    simp [ht]
  · dsimp [value, CoeffOn.neg] at hx ⊢
    simp only [Sign3.sgn_opp, neg_mul]
    rw [Finset.sum_neg_distrib]
    simp [hx]

end AdmissibleCarry
