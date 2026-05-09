import AdmissibleCarry.PrefixedSeq

/-!
# Asymptotics for the prefixed sequence

The tail is a normal `LegalSchedule`, so the existing abstract asymptotic API
applies after proving the shifted concrete estimates.
-/

namespace AdmissibleCarry

noncomputable section

open Filter

namespace Prefixed

theorem tail_decay_factor_le (j : Nat) :
    2 * (tailK j : ℝ) ^ (2 - LegalSchedule.tau) ≤
      LegalSchedule.rho / (S.scale j : ℝ) ^ LegalSchedule.tau := by
  let s : ℝ := S.scale j
  let a : ℝ := 2 * s ^ LegalSchedule.theta
  have hs_pos : 0 < s := by
    dsimp [s]
    exact LegalSchedule.scale_pos S j
  have hs_nonneg : 0 ≤ s := le_of_lt hs_pos
  have ha_pos : 0 < a := by
    dsimp [a]
    positivity
  have hk_pos : 0 < (tailK j : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) (tailK_ge_two j))
  have hexp_neg : 2 - LegalSchedule.tau < 0 := by
    rw [LegalSchedule.two_sub_tau]
    exact neg_neg_of_pos LegalSchedule.sqrt_two_pos
  have hlower : a ≤ (tailK j : ℝ) := by
    dsimp [a, s]
    exact tailK_lower_scale j
  have hpow_le :
      (tailK j : ℝ) ^ (2 - LegalSchedule.tau) ≤ a ^ (2 - LegalSchedule.tau) := by
    exact (Real.rpow_le_rpow_iff_of_neg hk_pos ha_pos hexp_neg).2 hlower
  have ha_eval :
      2 * a ^ (2 - LegalSchedule.tau) =
        LegalSchedule.rho / s ^ LegalSchedule.tau := by
    have htheta_neg : LegalSchedule.theta * (-Real.sqrt 2) = -LegalSchedule.tau := by
      rw [LegalSchedule.tau_eq_theta_mul_sqrt_two]
      ring
    calc
      2 * a ^ (2 - LegalSchedule.tau)
          = 2 * (2 * s ^ LegalSchedule.theta) ^ (-Real.sqrt 2) := by
            rw [LegalSchedule.two_sub_tau]
      _ = 2 * ((2 : ℝ) ^ (-Real.sqrt 2) *
            (s ^ LegalSchedule.theta) ^ (-Real.sqrt 2)) := by
            rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.rpow_nonneg hs_nonneg _)]
      _ = 2 * ((2 : ℝ) ^ (-Real.sqrt 2) * s ^ (-LegalSchedule.tau)) := by
            rw [← Real.rpow_mul hs_nonneg, htheta_neg]
      _ = LegalSchedule.rho / s ^ LegalSchedule.tau := by
            rw [Real.rpow_neg hs_nonneg]
            dsimp [LegalSchedule.rho]
            nth_rewrite 1 [← Real.rpow_one (2 : ℝ)]
            rw [← mul_assoc]
            rw [← Real.rpow_add (by norm_num : 0 < (2 : ℝ))]
            ring_nf
  nlinarith

theorem tail_P_succ_le (j : Nat) :
    S.P (j + 1) ≤ LegalSchedule.rho * S.P j := by
  have hM_nonneg : 0 ≤ (S.M j : ℝ) := by
    positivity
  have hk_pos : 0 < (tailK j : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) (tailK_ge_two j))
  have hQ : (Q (tailK j) : ℝ) ≤ 2 * (tailK j : ℝ) ^ (2 : ℝ) :=
    Q_le_two_mul_sq (tailK_ge_two j)
  have hnum :
      (S.M j : ℝ) * (Q (tailK j) : ℝ) ≤
        (S.M j : ℝ) * (2 * (tailK j : ℝ) ^ (2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hQ hM_nonneg
  have hscale_succ_tau_nonneg :
      0 ≤ (S.scale (j + 1) : ℝ) ^ LegalSchedule.tau := by
    exact Real.rpow_nonneg (le_of_lt (LegalSchedule.scale_pos S (j + 1))) _
  have hden :
      (tailK j : ℝ) ^ LegalSchedule.tau ≤
        (S.scale (j + 1) : ℝ) ^ LegalSchedule.tau := by
    exact Real.rpow_le_rpow (le_of_lt hk_pos) (tailK_le_succ_scale j)
      (le_of_lt LegalSchedule.tau_pos)
  have hk_tau_pos : 0 < (tailK j : ℝ) ^ LegalSchedule.tau :=
    Real.rpow_pos_of_pos hk_pos _
  have hbig_nonneg :
      0 ≤ (S.M j : ℝ) * (2 * (tailK j : ℝ) ^ (2 : ℝ)) := by
    positivity
  calc
    S.P (j + 1)
        = ((S.M j : Nat) * Q (tailK j) : ℝ) /
            (S.scale (j + 1) : ℝ) ^ LegalSchedule.tau := by
          simp [LegalSchedule.P, LegalSchedule.M, S, tailSchedule]
    _ = (S.M j : ℝ) * (Q (tailK j) : ℝ) /
            (S.scale (j + 1) : ℝ) ^ LegalSchedule.tau := by
          norm_num [Nat.cast_mul]
    _ ≤ (S.M j : ℝ) * (2 * (tailK j : ℝ) ^ (2 : ℝ)) /
            (S.scale (j + 1) : ℝ) ^ LegalSchedule.tau := by
          exact div_le_div_of_nonneg_right hnum hscale_succ_tau_nonneg
    _ ≤ (S.M j : ℝ) * (2 * (tailK j : ℝ) ^ (2 : ℝ)) /
            (tailK j : ℝ) ^ LegalSchedule.tau := by
          exact div_le_div_of_nonneg_left hbig_nonneg hk_tau_pos hden
    _ = (S.M j : ℝ) *
          (2 * (tailK j : ℝ) ^ (2 - LegalSchedule.tau)) := by
          rw [Real.rpow_sub hk_pos 2 LegalSchedule.tau]
          ring
    _ ≤ (S.M j : ℝ) *
          (LegalSchedule.rho / (S.scale j : ℝ) ^ LegalSchedule.tau) := by
          exact mul_le_mul_of_nonneg_left (tail_decay_factor_le j) hM_nonneg
    _ = LegalSchedule.rho * S.P j := by
          dsimp [LegalSchedule.P]
          ring

theorem tail_P_tendsto_zero :
    Filter.Tendsto S.P Filter.atTop (nhds 0) :=
  LegalSchedule.P_tendsto_zero_of_geometric S tail_P_succ_le

theorem tail_gap_ratio_le_const_P_owner (n : Nat) :
    (S.GapAt n : ℝ) / ((n + 1 : Nat) : ℝ) ^ LegalSchedule.gapExponent ≤
      200 * S.P (S.owner n) := by
  let j := S.owner n
  have hM_nonneg : 0 ≤ (S.M j : ℝ) := by
    positivity
  have hgap_num :
      (S.GapAt n : ℝ) ≤
        (S.M j : ℝ) *
          (200 * (S.scale j : ℝ) ^ LegalSchedule.theta) := by
    have hk := tailK_upper_scale j
    have hmul := mul_le_mul_of_nonneg_left hk hM_nonneg
    simpa [LegalSchedule.GapAt, S, tailSchedule, j, Nat.cast_mul] using hmul
  have hden_nonneg : 0 ≤ ((n + 1 : Nat) : ℝ) ^ LegalSchedule.gapExponent := by
    positivity
  have hs_pos : 0 < (S.scale j : ℝ) := by
    dsimp [j]
    exact LegalSchedule.scale_pos S (S.owner n)
  have hden_scale_pos :
      0 < (S.scale j : ℝ) ^ LegalSchedule.gapExponent :=
    Real.rpow_pos_of_pos hs_pos _
  have hbase : (S.scale j : ℝ) ≤ ((n + 1 : Nat) : ℝ) := by
    dsimp [j]
    exact LegalSchedule.scale_owner_le_succ S n
  have hden :
      (S.scale j : ℝ) ^ LegalSchedule.gapExponent ≤
        ((n + 1 : Nat) : ℝ) ^ LegalSchedule.gapExponent := by
    exact Real.rpow_le_rpow (le_of_lt hs_pos) hbase LegalSchedule.gapExponent_nonneg
  have hnum_nonneg :
      0 ≤ (S.M j : ℝ) *
        (200 * (S.scale j : ℝ) ^ LegalSchedule.theta) := by
    positivity
  calc
    (S.GapAt n : ℝ) / ((n + 1 : Nat) : ℝ) ^ LegalSchedule.gapExponent
        ≤ ((S.M j : ℝ) *
            (200 * (S.scale j : ℝ) ^ LegalSchedule.theta)) /
            ((n + 1 : Nat) : ℝ) ^ LegalSchedule.gapExponent := by
          exact div_le_div_of_nonneg_right hgap_num hden_nonneg
    _ ≤ ((S.M j : ℝ) *
            (200 * (S.scale j : ℝ) ^ LegalSchedule.theta)) /
            (S.scale j : ℝ) ^ LegalSchedule.gapExponent := by
          exact div_le_div_of_nonneg_left hnum_nonneg hden_scale_pos hden
    _ = 200 * S.P j := by
          dsimp [LegalSchedule.P]
          rw [LegalSchedule.gapExponent_eq_theta_add_tau]
          rw [Real.rpow_add hs_pos LegalSchedule.theta LegalSchedule.tau]
          field_simp [ne_of_gt (Real.rpow_pos_of_pos hs_pos LegalSchedule.theta),
            ne_of_gt (Real.rpow_pos_of_pos hs_pos LegalSchedule.tau)]

theorem tail_gap_ratio_tendsto :
    Filter.Tendsto
      (fun n : Nat =>
        (S.GapAt n : ℝ) / ((n + 1 : Nat) : ℝ) ^ LegalSchedule.gapExponent)
      Filter.atTop (nhds 0) := by
  have howner := LegalSchedule.owner_tendsto_atTop S
  have hPowner :
      Filter.Tendsto (fun n : Nat => S.P (S.owner n)) Filter.atTop (nhds 0) :=
    tail_P_tendsto_zero.comp howner
  have hupper :
      Filter.Tendsto (fun n : Nat => 200 * S.P (S.owner n)) Filter.atTop (nhds 0) := by
    simpa using Filter.Tendsto.const_mul (200 : ℝ) hPowner
  exact squeeze_zero (fun n => by positivity) tail_gap_ratio_le_const_P_owner hupper

theorem pref_gap_shift_le_tail (m : Nat) :
    ((prefSeq (m + 2 + 1) - prefSeq (m + 2) : Nat) : ℝ) /
        ((m + 2 + 1 : Nat) : ℝ) ^ LegalSchedule.gapExponent ≤
      4 * ((S.GapAt m : ℝ) / ((m + 1 : Nat) : ℝ) ^ LegalSchedule.gapExponent) := by
  have hgap := pref_tail_gap m
  have hden_small_pos : 0 < ((m + 1 : Nat) : ℝ) ^ LegalSchedule.gapExponent := by
    positivity
  have hden_le :
      ((m + 1 : Nat) : ℝ) ^ LegalSchedule.gapExponent ≤
        ((m + 2 + 1 : Nat) : ℝ) ^ LegalSchedule.gapExponent := by
    have hbase : ((m + 1 : Nat) : ℝ) ≤ ((m + 2 + 1 : Nat) : ℝ) := by
      exact_mod_cast (by omega : m + 1 ≤ m + 2 + 1)
    exact Real.rpow_le_rpow (by positivity) hbase LegalSchedule.gapExponent_nonneg
  have hnum_nonneg : 0 ≤ (4 * S.GapAt m : ℝ) := by
    positivity
  calc
    ((prefSeq (m + 2 + 1) - prefSeq (m + 2) : Nat) : ℝ) /
        ((m + 2 + 1 : Nat) : ℝ) ^ LegalSchedule.gapExponent
        = (4 * S.GapAt m : ℝ) /
            ((m + 2 + 1 : Nat) : ℝ) ^ LegalSchedule.gapExponent := by
          rw [hgap]
          norm_num [Nat.cast_mul]
    _ ≤ (4 * S.GapAt m : ℝ) /
          ((m + 1 : Nat) : ℝ) ^ LegalSchedule.gapExponent := by
          exact div_le_div_of_nonneg_left hnum_nonneg hden_small_pos hden_le
    _ = 4 * ((S.GapAt m : ℝ) / ((m + 1 : Nat) : ℝ) ^ LegalSchedule.gapExponent) := by
          ring

theorem pref_gap_tendsto :
    Filter.Tendsto
      (fun n : Nat =>
        ((prefSeq (n + 1) - prefSeq n : Nat) : ℝ) /
          ((n + 1 : Nat) : ℝ) ^ LegalSchedule.gapExponent)
      Filter.atTop (nhds 0) := by
  let f : Nat → ℝ := fun n =>
    ((prefSeq (n + 1) - prefSeq n : Nat) : ℝ) /
      ((n + 1 : Nat) : ℝ) ^ LegalSchedule.gapExponent
  have hshift :
      Filter.Tendsto (fun m : Nat => f (m + 2)) Filter.atTop (nhds 0) := by
    have hupper :
        Filter.Tendsto
          (fun m : Nat =>
            4 * ((S.GapAt m : ℝ) / ((m + 1 : Nat) : ℝ) ^ LegalSchedule.gapExponent))
          Filter.atTop (nhds 0) := by
      simpa using Filter.Tendsto.const_mul (4 : ℝ) tail_gap_ratio_tendsto
    exact squeeze_zero (fun m => by dsimp [f]; positivity) pref_gap_shift_le_tail hupper
  exact (Filter.tendsto_add_atTop_iff_nat 2).1 hshift

end Prefixed

end

end AdmissibleCarry
