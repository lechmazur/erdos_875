import AdmissibleCarry.ConcreteCeil

/-!
# Shifted tail schedule for the prefixed construction

The all-index endpoint uses the fixed prefix `{1, 2}` and then appends a
scaled copy of a normal `LegalSchedule`.  This file defines that tail schedule:
the old total count before the next block is `tailN j + 2`, so the concrete
block length is `ceil (2 * (tailN j + 3)^theta)`.
-/

namespace AdmissibleCarry

noncomputable section

namespace Prefixed

def tailKCore (N : Nat) : Nat :=
  Nat.ceil (2 * (((N + 3 : Nat) : ℝ) ^ LegalSchedule.theta))

def tailN : Nat → Nat
  | 0 => 0
  | j + 1 => tailN j + tailKCore (tailN j)

def tailK (j : Nat) : Nat :=
  tailKCore (tailN j)

theorem tailN_eq_rec (j : Nat) :
    tailN j = Nat.rec 0 (fun i n => n + tailK i) j := by
  induction j with
  | zero =>
      rfl
  | succ j ih =>
      simp [tailN, tailK, ih]

theorem tailK_ge_two (j : Nat) : 2 ≤ tailK j := by
  have hbase : (1 : ℝ) ≤ ((tailN j + 3 : Nat) : ℝ) := by
    exact_mod_cast (by omega : 1 ≤ tailN j + 3)
  have hpow : (1 : ℝ) ≤ ((tailN j + 3 : Nat) : ℝ) ^ LegalSchedule.theta :=
    Real.one_le_rpow hbase theta_nonneg
  have htwo :
      (2 : ℝ) ≤ 2 * ((tailN j + 3 : Nat) : ℝ) ^ LegalSchedule.theta := by
    nlinarith
  have hceil :
      (2 : ℝ) ≤
        (Nat.ceil (2 * ((tailN j + 3 : Nat) : ℝ) ^ LegalSchedule.theta) : ℝ) :=
    htwo.trans (Nat.le_ceil _)
  have hceil_nat :
      2 ≤ Nat.ceil (2 * ((tailN j + 3 : Nat) : ℝ) ^ LegalSchedule.theta) := by
    exact_mod_cast hceil
  simpa [tailK, tailKCore] using hceil_nat

theorem two_le_theta : (2 : ℝ) ≤ LegalSchedule.theta := by
  dsimp [LegalSchedule.theta]
  have hs : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  linarith

theorem tailK_growth_prefN (j : Nat) :
    4 * (tailN j + 2) < tailK j := by
  rw [tailK, tailKCore]
  apply Nat.lt_ceil.mpr
  have hbase : (1 : ℝ) ≤ ((tailN j + 3 : Nat) : ℝ) := by
    exact_mod_cast (by omega : 1 ≤ tailN j + 3)
  have hpow2 :
      ((tailN j + 3 : Nat) : ℝ) ^ (2 : ℝ) ≤
        ((tailN j + 3 : Nat) : ℝ) ^ LegalSchedule.theta :=
    Real.rpow_le_rpow_of_exponent_le hbase two_le_theta
  have hpoly :
      ((4 * (tailN j + 2) : Nat) : ℝ) <
        2 * ((tailN j + 3 : Nat) : ℝ) ^ (2 : ℝ) := by
    norm_num [Nat.cast_add, Nat.cast_mul, Real.rpow_natCast]
    nlinarith [sq_nonneg (tailN j : ℝ)]
  nlinarith

theorem tailK_growth (j : Nat) :
    4 * (Nat.rec 0 (fun i n => n + tailK i) j) < tailK j := by
  rw [← tailN_eq_rec j]
  exact lt_of_le_of_lt (by omega : 4 * tailN j ≤ 4 * (tailN j + 2))
    (tailK_growth_prefN j)

def tailSchedule : LegalSchedule where
  k := tailK
  k_ge_two := tailK_ge_two
  growth := tailK_growth

abbrev S : LegalSchedule :=
  tailSchedule

theorem tailSchedule_N (j : Nat) :
    S.N j = tailN j := by
  rw [LegalSchedule.N_eq_rec, tailN_eq_rec]
  simp [tailSchedule]

theorem prefGrowth_N (j : Nat) :
    4 * (S.N j + 2) < S.k j := by
  rw [tailSchedule_N]
  exact tailK_growth_prefN j

theorem tailK_le_succ_scale (j : Nat) :
    (tailK j : ℝ) ≤ (S.scale (j + 1) : ℝ) := by
  have hN : S.N (j + 1) = tailN (j + 1) := tailSchedule_N (j + 1)
  dsimp [LegalSchedule.scale]
  rw [hN]
  exact_mod_cast (by
    change tailK j ≤ max 1 (tailN j + tailK j)
    omega)

theorem scale_le_tailN_add_three (j : Nat) :
    (S.scale j : ℝ) ≤ ((tailN j + 3 : Nat) : ℝ) := by
  have hN : S.N j = tailN j := tailSchedule_N j
  dsimp [LegalSchedule.scale]
  rw [hN]
  exact_mod_cast
    (max_le (by omega : 1 ≤ tailN j + 3) (by omega : tailN j ≤ tailN j + 3))

theorem tailN_add_three_le_four_scale (j : Nat) :
    ((tailN j + 3 : Nat) : ℝ) ≤ 4 * (S.scale j : ℝ) := by
  have hN : S.N j = tailN j := tailSchedule_N j
  dsimp [LegalSchedule.scale]
  rw [hN]
  exact_mod_cast (by
    change tailN j + 3 ≤ 4 * max 1 (tailN j)
    omega)

theorem four_rpow_theta_le_eighty :
    (4 : ℝ) ^ LegalSchedule.theta ≤ 80 := by
  have h :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) theta_le_three
  norm_num [Real.rpow_natCast] at h ⊢
  linarith

theorem tailK_lower_scale (j : Nat) :
    2 * (S.scale j : ℝ) ^ LegalSchedule.theta ≤ (tailK j : ℝ) := by
  have hscale := scale_le_tailN_add_three j
  have hpow :
      (S.scale j : ℝ) ^ LegalSchedule.theta ≤
        ((tailN j + 3 : Nat) : ℝ) ^ LegalSchedule.theta := by
    exact Real.rpow_le_rpow (by positivity) hscale theta_nonneg
  have hmul :
      2 * (S.scale j : ℝ) ^ LegalSchedule.theta ≤
        2 * ((tailN j + 3 : Nat) : ℝ) ^ LegalSchedule.theta := by
    nlinarith
  have hceil :
      2 * ((tailN j + 3 : Nat) : ℝ) ^ LegalSchedule.theta ≤ (tailK j : ℝ) := by
    dsimp [tailK, tailKCore]
    exact Nat.le_ceil _
  exact hmul.trans hceil

theorem tailK_upper_scale (j : Nat) :
    (tailK j + 1 : ℝ) ≤ 200 * (S.scale j : ℝ) ^ LegalSchedule.theta := by
  let x : ℝ := 2 * ((tailN j + 3 : Nat) : ℝ) ^ LegalSchedule.theta
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    positivity
  have hceil_lt : (tailK j : ℝ) < x + 1 := by
    dsimp [tailK, tailKCore, x]
    exact Nat.ceil_lt_add_one hx_nonneg
  have hceil_le : (tailK j + 1 : ℝ) ≤ x + 2 := by
    linarith
  have hscale_nonneg : 0 ≤ (S.scale j : ℝ) := by
    positivity
  have hone_le_scale : (1 : ℝ) ≤ S.scale j := by
    dsimp [LegalSchedule.scale]
    exact_mod_cast le_max_left 1 (S.N j)
  have hx_bound : x ≤ 160 * (S.scale j : ℝ) ^ LegalSchedule.theta := by
    have hbase := tailN_add_three_le_four_scale j
    have hpow :
        ((tailN j + 3 : Nat) : ℝ) ^ LegalSchedule.theta ≤
          (4 * (S.scale j : ℝ)) ^ LegalSchedule.theta := by
      exact Real.rpow_le_rpow (by positivity) hbase theta_nonneg
    have hmulr :
        (4 * (S.scale j : ℝ)) ^ LegalSchedule.theta =
          (4 : ℝ) ^ LegalSchedule.theta * (S.scale j : ℝ) ^ LegalSchedule.theta := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hscale_nonneg]
    have hpow_bound :
        (4 * (S.scale j : ℝ)) ^ LegalSchedule.theta ≤
          80 * (S.scale j : ℝ) ^ LegalSchedule.theta := by
      rw [hmulr]
      exact mul_le_mul_of_nonneg_right four_rpow_theta_le_eighty
        (Real.rpow_nonneg hscale_nonneg _)
    dsimp [x]
    nlinarith
  have htwo_le : (2 : ℝ) ≤ 40 * (S.scale j : ℝ) ^ LegalSchedule.theta := by
    have hp : (1 : ℝ) ≤ (S.scale j : ℝ) ^ LegalSchedule.theta :=
      Real.one_le_rpow hone_le_scale theta_nonneg
    nlinarith
  nlinarith

end Prefixed

end

end AdmissibleCarry
