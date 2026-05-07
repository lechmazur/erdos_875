import AdmissibleCarry.LocalCarry

/-!
# Carry-state closure

The cached carry state is the finite invariant used to adjoin one dilated local
block.
-/

namespace AdmissibleCarry

structure CarryState (A : Finset Nat) (M sigma : Nat) where
  Mpos : 0 < M
  sigmaEq : sigma = sumN A
  posMem : ∀ a, a ∈ A → 0 < a
  ltM : ∀ a, a ∈ A → a < M
  carry : ∀ T D q : Int, Diff A T D → D = (M : Int) * q → T = q

def OldSmall (sigma M k : Nat) : Prop :=
  4 * sigma < M * k

def NewSmall (sigma M k : Nat) : Prop :=
  2 * sigma < M * k

def block (M k : Nat) : Finset Nat :=
  (C k).image fun c => M * c

def stepSet (A : Finset Nat) (M k : Nat) : Finset Nat :=
  A ∪ block M k

def stepSigma (sigma M k : Nat) : Nat :=
  sigma + M * ((k * k * k + k) / 2)

theorem block_pos {M k a : Nat} (hM : 0 < M) (ha : a ∈ block M k) :
    0 < a := by
  rcases Finset.mem_image.mp ha with ⟨c, hc, rfl⟩
  exact Nat.mul_pos hM (C_pos hc)

theorem block_lt_nextM {M k a : Nat} (hM : 0 < M) (ha : a ∈ block M k) :
    a < M * Q k := by
  rcases Finset.mem_image.mp ha with ⟨c, hc, rfl⟩
  exact Nat.mul_lt_mul_of_pos_left (C_lt_Q hc) hM

theorem stepSet_posMem {A : Finset Nat} {M sigma k a : Nat}
    (hstate : CarryState A M sigma) (ha : a ∈ stepSet A M k) :
    0 < a := by
  rcases Finset.mem_union.mp ha with ha_old | ha_new
  · exact hstate.posMem a ha_old
  · exact block_pos hstate.Mpos ha_new

theorem stepSet_lt_nextM {A : Finset Nat} {M sigma k a : Nat}
    (hstate : CarryState A M sigma) (ha : a ∈ stepSet A M k) :
    a < M * Q k := by
  rcases Finset.mem_union.mp ha with ha_old | ha_new
  · exact lt_of_lt_of_le (hstate.ltM a ha_old) (Nat.le_mul_of_pos_right M (Q_pos k))
  · exact block_lt_nextM hstate.Mpos ha_new

theorem disjoint_old_block {A : Finset Nat} {M sigma k : Nat}
    (hstate : CarryState A M sigma) :
    Disjoint A (block M k) := by
  rw [Finset.disjoint_iff_ne]
  intro a ha b hb heq
  have ha_lt : a < M := hstate.ltM a ha
  rcases Finset.mem_image.mp hb with ⟨c, hc, rfl⟩
  have hcp : 0 < c := C_pos hc
  have hge : M ≤ M * c := Nat.le_mul_of_pos_right M hcp
  omega

def restrictCoeff (A : Finset Nat) {B : Finset Nat} (c : CoeffOn B) : CoeffOn A where
  sign n := if n ∈ A then c.sign n else Sign3.zero
  zero_of_not_mem n hn := by
    simp [hn]

def localCoeff (M k : Nat) {B : Finset Nat} (c : CoeffOn B) : Nat → Sign3 :=
  fun i => c.sign (M * cell k i)

theorem cell_injOn (k : Nat) :
    Set.InjOn (cell k) (Finset.range k : Set Nat) := by
  intro i _hi j _hj h
  simp [cell] at h
  omega

theorem mul_injOn_C {M k : Nat} (hM : 0 < M) :
    Set.InjOn (fun c => M * c) (C k : Set Nat) := by
  intro a _ha b _hb h
  exact Nat.mul_left_cancel hM h

theorem grade_restrictCoeff (A : Finset Nat) {B : Finset Nat} (c : CoeffOn B) :
    grade A (restrictCoeff A c) = A.sum fun n => Sign3.sgn (c.sign n) := by
  dsimp [grade, restrictCoeff]
  apply Finset.sum_congr rfl
  intro n hn
  simp [hn]

theorem value_restrictCoeff (A : Finset Nat) {B : Finset Nat} (c : CoeffOn B) :
    value A (restrictCoeff A c) = A.sum fun n => Sign3.sgn (c.sign n) * (n : Int) := by
  dsimp [value, restrictCoeff]
  apply Finset.sum_congr rfl
  intro n hn
  simp [hn]

theorem localGrade_localCoeff {M k : Nat} {B : Finset Nat} (c : CoeffOn B) :
    localGrade k (localCoeff M k c) =
      (Finset.range k).sum fun i => Sign3.sgn (c.sign (M * cell k i)) := by
  rfl

theorem grade_step_decompose {A : Finset Nat} {M sigma k : Nat}
    (hstate : CarryState A M sigma) (c : CoeffOn (stepSet A M k)) :
    grade (stepSet A M k) c =
      grade A (restrictCoeff A c) + localGrade k (localCoeff M k c) := by
  unfold stepSet
  dsimp [grade]
  rw [Finset.sum_union (disjoint_old_block hstate)]
  have hold : (∑ x ∈ A, Sign3.sgn (c.sign x)) = grade A (restrictCoeff A c) := by
    rw [grade_restrictCoeff]
  rw [hold]
  congr 1
  dsimp [block]
  rw [Finset.sum_image (mul_injOn_C hstate.Mpos)]
  dsimp [C, localGrade, localCoeff]
  rw [Finset.sum_image (cell_injOn k)]

theorem value_step_decompose {A : Finset Nat} {M sigma k : Nat}
    (hstate : CarryState A M sigma) (c : CoeffOn (stepSet A M k)) :
    value (stepSet A M k) c =
      value A (restrictCoeff A c) + (M : Int) * localValue k (localCoeff M k c) := by
  unfold stepSet
  dsimp [value]
  rw [Finset.sum_union (disjoint_old_block hstate)]
  have hold : (∑ x ∈ A, Sign3.sgn (c.sign x) * (x : Int)) = value A (restrictCoeff A c) := by
    rw [value_restrictCoeff]
  rw [hold]
  congr 1
  dsimp [block]
  rw [Finset.sum_image (mul_injOn_C hstate.Mpos)]
  dsimp [C, localValue, localCoeff]
  rw [Finset.sum_image (cell_injOn k)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

theorem quotient_natAbs_lt {c M sigma k : Nat} {D q : Int}
    (hD : D = (M : Int) * q)
    (habs : D.natAbs ≤ sigma)
    (hsmall : c * sigma < M * k) :
    c * q.natAbs < k := by
  have hmul : M * q.natAbs ≤ sigma := by
    have hDabs : D.natAbs = M * q.natAbs := by
      rw [hD, Int.natAbs_mul]
      simp
    exact hDabs ▸ habs
  by_contra hnot
  have hk : k ≤ c * q.natAbs := Nat.le_of_not_gt hnot
  have hleft : M * k ≤ M * (c * q.natAbs) := Nat.mul_le_mul_left M hk
  have hmid : M * (c * q.natAbs) = c * (M * q.natAbs) := by ring
  have hright : c * (M * q.natAbs) ≤ c * sigma := Nat.mul_le_mul_left c hmul
  nlinarith

theorem quotient_usmall {M sigma k : Nat} {D q : Int}
    (hD : D = (M : Int) * q)
    (habs : D.natAbs ≤ sigma)
    (hold : OldSmall sigma M k) :
    USmall k q := by
  exact quotient_natAbs_lt hD habs hold

theorem quotient_wsmall {M sigma k : Nat} {D q : Int}
    (hD : D = (M : Int) * q)
    (habs : D.natAbs ≤ sigma)
    (hnew : NewSmall sigma M k) :
    WSmall k q := by
  exact quotient_natAbs_lt hD habs hnew

theorem two_mul_sum_cell (k : Nat) :
    2 * ((Finset.range k).sum fun i => cell k i) = k * k * k + k := by
  cases k with
  | zero =>
      simp [cell]
  | succ n =>
      dsimp [cell]
      rw [Finset.sum_add_distrib]
      rw [← Finset.sum_mul]
      simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
      have hsum := Finset.sum_range_id_mul_two (n + 1)
      simp at hsum
      nlinarith

theorem sum_cell (k : Nat) :
    (Finset.range k).sum (fun i => cell k i) = (k * k * k + k) / 2 := by
  have hdouble := two_mul_sum_cell k
  apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2)
  rw [hdouble]
  have hdiv : 2 ∣ k * k * k + k :=
    ⟨(Finset.range k).sum fun i => cell k i, hdouble.symm⟩
  rw [mul_comm 2 ((k * k * k + k) / 2), Nat.div_mul_cancel hdiv]

theorem sumN_C (k : Nat) :
    sumN (C k) = (k * k * k + k) / 2 := by
  dsimp [sumN, C]
  rw [Finset.sum_image (cell_injOn k)]
  exact sum_cell k

theorem sumN_block {M k : Nat} (hM : 0 < M) :
    sumN (block M k) = M * ((k * k * k + k) / 2) := by
  dsimp [sumN, block]
  rw [Finset.sum_image (mul_injOn_C hM)]
  simp only [id_eq]
  rw [← Finset.mul_sum]
  rw [show (∑ x ∈ C k, x) = sumN (C k) by rfl]
  rw [sumN_C]

theorem stepSigma_eq_sumN_stepSet {A : Finset Nat} {M sigma k : Nat}
    (hstate : CarryState A M sigma) :
    stepSigma sigma M k = sumN (stepSet A M k) := by
  calc
    stepSigma sigma M k = sigma + M * ((k * k * k + k) / 2) := rfl
    _ = sumN A + sumN (block M k) := by
      rw [hstate.sigmaEq, sumN_block hstate.Mpos]
    _ = sumN (stepSet A M k) := by
      unfold stepSet sumN
      rw [Finset.sum_union (disjoint_old_block hstate)]

theorem closure_step {A : Finset Nat} {M sigma k : Nat}
    (hk : 2 ≤ k)
    (hstate : CarryState A M sigma)
    (hold : OldSmall sigma M k)
    (hnew : NewSmall (stepSigma sigma M k) (M * Q k) k) :
    CarryState (stepSet A M k) (M * Q k) (stepSigma sigma M k) ∧
      NewSmall (stepSigma sigma M k) (M * Q k) k := by
  constructor
  · refine
      { Mpos := Nat.mul_pos hstate.Mpos (Q_pos k)
        sigmaEq := stepSigma_eq_sumN_stepSet hstate
        posMem := ?_
        ltM := ?_
        carry := ?_ }
    · intro a ha
      exact stepSet_posMem hstate ha
    · intro a ha
      exact stepSet_lt_nextM hstate ha
    · intro T D q hdiff hD
      rcases hdiff with ⟨c, hT, hval⟩
      let cold : CoeffOn A := restrictCoeff A c
      let eps : Nat → Sign3 := localCoeff M k c
      let TA : Int := grade A cold
      let DA : Int := value A cold
      let tB : Int := localGrade k eps
      let y : Int := localValue k eps
      let u : Int := (Q k : Int) * q - y
      have hTdecomp : T = TA + tB := by
        rw [← hT]
        dsimp [TA, tB, cold, eps]
        exact grade_step_decompose hstate c
      have hDdecomp : D = DA + (M : Int) * y := by
        rw [← hval]
        dsimp [DA, y, cold, eps]
        exact value_step_decompose hstate c
      have hdiffOld : Diff A TA DA := by
        exact ⟨cold, rfl, rfl⟩
      have hcd : CDiff k tB y := by
        exact ⟨eps, rfl, rfl⟩
      have hDq : DA + (M : Int) * y = (M : Int) * ((Q k : Int) * q) := by
        calc
          DA + (M : Int) * y = D := hDdecomp.symm
          _ = ((M * Q k : Nat) : Int) * q := hD
          _ = (M : Int) * ((Q k : Int) * q) := by
            rw [Nat.cast_mul]
            ring
      have hDA : DA = (M : Int) * u := by
        dsimp [u]
        nlinarith
      have hTA : TA = u := hstate.carry TA DA u hdiffOld hDA
      have hDAabs : DA.natAbs ≤ sigma := by
        have hbound := value_natAbs_le_sumN A cold
        rw [← hstate.sigmaEq] at hbound
        exact hbound
      have hu : USmall k u := quotient_usmall hDA hDAabs hold
      have hDabs : D.natAbs ≤ stepSigma sigma M k := by
        have hbound := value_natAbs_le_sumN (stepSet A M k) c
        rw [hval] at hbound
        rw [← stepSigma_eq_sumN_stepSet hstate] at hbound
        exact hbound
      have hw : WSmall k q := quotient_wsmall hD hDabs hnew
      have hy : y = (Q k : Int) * q - u := by
        dsimp [u]
        ring
      have htB : tB = q - u := by
        exact local_carry_range (by omega : 0 < k) hcd hy hu hw
      calc
        T = TA + tB := hTdecomp
        _ = u + (q - u) := by rw [hTA, htB]
        _ = q := by ring
  · exact hnew

end AdmissibleCarry
