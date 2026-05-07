import AdmissibleCarry.LocalRange

/-!
# Local carry theorem

This file contains the two-sided smallness predicates and the main local carry
interfaces from the v10 blueprint. Hard arithmetic proofs are intentionally
visible as tracked placeholders during the first scaffold.
-/

namespace AdmissibleCarry

def USmall (m : Nat) (u : Int) : Prop :=
  4 * u.natAbs < m

def WSmall (m : Nat) (w : Int) : Prop :=
  2 * w.natAbs < m

def ZLtQuarter (m : Nat) (x : Int) : Prop :=
  -((m : Int)) < 4 * x ∧ 4 * x < (m : Int)

def ZLtHalf (m : Nat) (x : Int) : Prop :=
  -((m : Int)) < 2 * x ∧ 2 * x < (m : Int)

def Shift (m : Nat) (eps : Nat → Sign3) (w : Int) : Int :=
  (m : Int) * w - localIndex m eps

theorem three_shift_core {m : Nat} {G T s : Int} (hm : 2 ≤ m)
    (hGlo : -((m : Int)) ≤ G) (hGhi : G ≤ (m : Int))
    (hTlo : -3 * (m : Int) < 4 * T)
    (hThi : 4 * T < 3 * (m : Int))
    (hEq : G = T + ((m : Int) + 1) * s) :
    s = -1 ∨ s = 0 ∨ s = 1 := by
  have hm_nonneg : 0 ≤ ((m : Int) + 1) := by positivity
  by_cases hslo : s ≤ -2
  · have hmul : ((m : Int) + 1) * s ≤ ((m : Int) + 1) * (-2) :=
      mul_le_mul_of_nonneg_left hslo hm_nonneg
    nlinarith
  · by_cases hshi : 2 ≤ s
    · have hmul : ((m : Int) + 1) * 2 ≤ ((m : Int) + 1) * s :=
        mul_le_mul_of_nonneg_left hshi hm_nonneg
      nlinarith
    · omega

theorem zsmall_sub_bounds {m : Nat} {u w : Int}
    (hu : ZLtQuarter m u) (hw : ZLtHalf m w) :
    -3 * (m : Int) < 4 * (w - u) ∧
      4 * (w - u) < 3 * (m : Int) := by
  rcases hu with ⟨hu1, hu2⟩
  rcases hw with ⟨hw1, hw2⟩
  constructor <;> linarith

theorem local_carry_shift_identity {m : Nat} (eps : Nat → Sign3) {u w : Int}
    (hy : localValue m eps = (Q m : Int) * w - u) :
    localGrade m eps = (w - u) + ((m : Int) + 1) * Shift m eps w := by
  have hvalue := localValue_eq_grade_add m eps
  dsimp [Shift, Q] at *
  nlinarith

theorem positive_shift_defect {m : Nat} (eps : Nat → Sign3) {u w : Int}
    (hpos : localGrade m eps = w - u + ((m : Int) + 1)) :
    u = w + (defectTotal m eps : Int) + 1 := by
  have hdef := defect_grade m eps
  nlinarith

theorem positive_shift_index {m : Nat} (eps : Nat → Sign3) {u w : Int}
    (hy : localValue m eps = (Q m : Int) * w - u)
    (hpos : localGrade m eps = w - u + ((m : Int) + 1)) :
    localIndex m eps = (m : Int) * w - 1 := by
  have hvalue := localValue_eq_grade_add m eps
  dsimp [Q] at hy
  nlinarith

theorem positive_shift_lower {m : Nat} (hm : 0 < m) (eps : Nat → Sign3) :
    2 * (m : Int) * ((m : Int) - 1) -
        4 * (((m : Int) - 1) * (defectTotal m eps : Int)) ≤
      4 * localIndex m eps := by
  have hd := doubled_index_defect m eps
  have hle_nat := weightedDefect_le hm eps
  have hle_cast :
      (weightedDefectTotal m eps : Int) ≤
        (((m - 1) * defectTotal m eps : Nat) : Int) := by
    exact_mod_cast hle_nat
  have hle :
      (weightedDefectTotal m eps : Int) ≤
        ((m : Int) - 1) * (defectTotal m eps : Int) := by
    simpa [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ m)] using hle_cast
  nlinarith

theorem positive_shift_arith_core {m R : Nat} {I u w : Int} (hm : 0 < m)
    (hI : I = (m : Int) * w - 1)
    (hu_eq : u = w + (R : Int) + 1)
    (hu_lt : 4 * u < (m : Int))
    (hlower :
      2 * (m : Int) * ((m : Int) - 1) -
          4 * (((m : Int) - 1) * (R : Int)) ≤
        4 * I) :
    False := by
  have hmpos : (0 : Int) < (m : Int) := by omega
  have hult' : 4 * (w + (R : Int) + 1) < (m : Int) := by nlinarith
  have hmul := mul_lt_mul_of_pos_left hult' hmpos
  nlinarith

theorem positive_shift_impossible {m : Nat} (hm : 0 < m)
    (eps : Nat → Sign3) {u w : Int}
    (hy : localValue m eps = (Q m : Int) * w - u)
    (hu : ZLtQuarter m u)
    (hpos : localGrade m eps = w - u + ((m : Int) + 1)) :
    False := by
  have hdef := positive_shift_defect eps hpos
  have hidx := positive_shift_index eps hy hpos
  have hlower := positive_shift_lower hm eps
  exact positive_shift_arith_core hm hidx hdef hu.2 hlower

theorem negative_shift_impossible {m : Nat} (hm : 0 < m)
    (eps : Nat → Sign3) {u w : Int}
    (hy : localValue m eps = (Q m : Int) * w - u)
    (hu : ZLtQuarter m u)
    (hneg : localGrade m eps = w - u - ((m : Int) + 1)) :
    False := by
  let eps' : Nat → Sign3 := fun i => Sign3.opp (eps i)
  have hy' : localValue m eps' = (Q m : Int) * (-w) - (-u) := by
    dsimp [eps']
    rw [localValue_opp]
    nlinarith
  have hpos' : localGrade m eps' = (-w) - (-u) + ((m : Int) + 1) := by
    dsimp [eps']
    rw [localGrade_opp]
    nlinarith
  have hu' : ZLtQuarter m (-u) := by
    rcases hu with ⟨hu1, hu2⟩
    constructor <;> linarith
  exact positive_shift_impossible hm eps' hy' hu' hpos'

theorem usmall_zltQuarter {m : Nat} {u : Int} (h : USmall m u) :
    ZLtQuarter m u := by
  have h' : ((4 * u.natAbs : Nat) : Int) < (m : Int) := by
    exact_mod_cast h
  have h_abs : |4 * u| < (m : Int) := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : Int) ≤ 4)]
    simpa [Nat.cast_mul, Int.natCast_natAbs, mul_assoc] using h'
  simpa [ZLtQuarter] using (abs_lt.mp h_abs)

theorem wsmall_zltHalf {m : Nat} {w : Int} (h : WSmall m w) :
    ZLtHalf m w := by
  have h' : ((2 * w.natAbs : Nat) : Int) < (m : Int) := by
    exact_mod_cast h
  have h_abs : |2 * w| < (m : Int) := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : Int) ≤ 2)]
    simpa [Nat.cast_mul, Int.natCast_natAbs, mul_assoc] using h'
  simpa [ZLtHalf] using (abs_lt.mp h_abs)

theorem zltQuarter_neg {m : Nat} {u : Int} :
    ZLtQuarter m (-u) ↔ ZLtQuarter m u := by
  constructor
  · intro h
    rcases h with ⟨hleft, hright⟩
    constructor <;> linarith
  · intro h
    rcases h with ⟨hleft, hright⟩
    constructor <;> linarith

theorem zltHalf_neg {m : Nat} {w : Int} :
    ZLtHalf m (-w) ↔ ZLtHalf m w := by
  constructor
  · intro h
    rcases h with ⟨hleft, hright⟩
    constructor <;> linarith
  · intro h
    rcases h with ⟨hleft, hright⟩
    constructor <;> linarith

theorem local_carry_zsmall {m : Nat} (hm : 2 ≤ m)
    (eps : Nat → Sign3) {u w : Int}
    (hy : localValue m eps = (Q m : Int) * w - u)
    (hu : ZLtQuarter m u)
    (hw : ZLtHalf m w) :
    localGrade m eps = w - u := by
  have hm0 : 0 < m := by omega
  have hshift := local_carry_shift_identity eps hy
  have htbounds := zsmall_sub_bounds hu hw
  have hcases := three_shift_core hm
    (neg_le_localGrade m eps) (localGrade_le m eps)
    htbounds.1 htbounds.2 hshift
  rcases hcases with hs | hs | hs
  · exfalso
    apply negative_shift_impossible hm0 eps hy hu
    rw [hshift, hs]
    ring
  · rw [hshift, hs]
    ring
  · exfalso
    apply positive_shift_impossible hm0 eps hy hu
    rw [hshift, hs]
    ring

theorem local_carry_range_of_two_le {m : Nat} (hm : 2 ≤ m)
    {t y u w : Int}
    (hcd : CDiff m t y)
    (hy : y = (Q m : Int) * w - u)
    (hu : USmall m u)
    (hw : WSmall m w) :
    t = w - u := by
  rcases hcd with ⟨eps, ht, hval⟩
  have hvalue : localValue m eps = (Q m : Int) * w - u := by
    rw [hval, hy]
  exact ht.symm.trans
    (local_carry_zsmall hm eps hvalue (usmall_zltQuarter hu) (wsmall_zltHalf hw))

theorem local_carry_range {m : Nat} (hm : 0 < m)
    {t y u w : Int}
    (hcd : CDiff m t y)
    (hy : y = (Q m : Int) * w - u)
    (hu : USmall m u)
    (hw : WSmall m w) :
    t = w - u := by
  by_cases hm2 : 2 ≤ m
  · exact local_carry_range_of_two_le hm2 hcd hy hu hw
  · have hm1 : m = 1 := by omega
    subst m
    have hu_abs : u.natAbs = 0 := by
      dsimp [USmall] at hu
      omega
    have hw_abs : w.natAbs = 0 := by
      dsimp [WSmall] at hw
      omega
    have hu0 : u = 0 := Int.natAbs_eq_zero.mp hu_abs
    have hw0 : w = 0 := Int.natAbs_eq_zero.mp hw_abs
    have hy0 : y = 0 := by
      simpa [Q, hu0, hw0] using hy
    rcases hcd with ⟨eps, ht, hval⟩
    have hvalue_zero : localValue 1 eps = 0 := by
      rw [hval, hy0]
    have hsgn0 : Sign3.sgn (eps 0) = 0 := by
      simpa [localValue, cell] using hvalue_zero
    have hgrade_zero : localGrade 1 eps = 0 := by
      simp [localGrade, hsgn0]
    have ht0 : t = 0 := ht ▸ hgrade_zero
    simpa [hu0, hw0] using ht0

end AdmissibleCarry
