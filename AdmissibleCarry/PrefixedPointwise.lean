import AdmissibleCarry.PrefixedAsymptotic

/-!
# Pointwise gap bound for the prefixed construction

This file proves the direct all-index estimate.  The main block quantity is
`prefR j = prefM j * (S.k j + 1) / (S.N j + 3)^gapExponent`.
-/

namespace AdmissibleCarry

noncomputable section

namespace Prefixed

noncomputable def prefR (j : Nat) : ℝ :=
  ((prefM j : ℝ) * ((S.k j + 1 : Nat) : ℝ)) /
    (((S.N j + 3 : Nat) : ℝ) ^ LegalSchedule.gapExponent)

theorem prefR_pos (j : Nat) : 0 < prefR j := by
  dsimp [prefR]
  have hnum :
      0 < (prefM j : ℝ) * ((S.k j + 1 : Nat) : ℝ) := by
    exact mul_pos (by exact_mod_cast prefM_pos j) (by positivity)
  have hden :
      0 < (((S.N j + 3 : Nat) : ℝ) ^ LegalSchedule.gapExponent) := by
    positivity
  exact div_pos hnum hden

theorem tau_gt_three : (3 : ℝ) < LegalSchedule.tau := by
  dsimp [LegalSchedule.tau]
  have hs : (1 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)]
    norm_num
  linarith

theorem three_rpow_tau_gt_27 :
    (27 : ℝ) < (3 : ℝ) ^ LegalSchedule.tau := by
  have h :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 3) tau_gt_three
  norm_num [Real.rpow_natCast] at h ⊢
  exact h

theorem twelve_lt_three_rpow_tau :
    (12 : ℝ) < (3 : ℝ) ^ LegalSchedule.tau := by
  linarith [three_rpow_tau_gt_27]

theorem theta_sq_eq_gapExponent :
    LegalSchedule.theta ^ (2 : Nat) = LegalSchedule.gapExponent := by
  dsimp [LegalSchedule.theta, LegalSchedule.gapExponent]
  have hsq : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := by
    rw [← pow_two, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  nlinarith

theorem tau_sub_one_eq_theta :
    LegalSchedule.tau - 1 = LegalSchedule.theta := by
  dsimp [LegalSchedule.tau, LegalSchedule.theta]
  ring

theorem tailK_upper_total (j : Nat) :
    ((S.k j + 1 : Nat) : ℝ) ≤
      3 * (((S.N j + 3 : Nat) : ℝ) ^ LegalSchedule.theta) := by
  have hN : S.N j = tailN j := tailSchedule_N j
  let x : ℝ := 2 * ((tailN j + 3 : Nat) : ℝ) ^ LegalSchedule.theta
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    positivity
  have hceil_lt : (tailK j : ℝ) < x + 1 := by
    dsimp [tailK, tailKCore, x]
    exact Nat.ceil_lt_add_one hx_nonneg
  have hceil_le : (tailK j + 1 : ℝ) ≤ x + 2 := by
    linarith
  have hpow_ge_one : (1 : ℝ) ≤ ((tailN j + 3 : Nat) : ℝ) ^ LegalSchedule.theta := by
    have hbase : (1 : ℝ) ≤ ((tailN j + 3 : Nat) : ℝ) := by
      exact_mod_cast (by omega : 1 ≤ tailN j + 3)
    exact Real.one_le_rpow hbase theta_nonneg
  have htwo_le : (2 : ℝ) ≤
      ((tailN j + 3 : Nat) : ℝ) ^ LegalSchedule.theta := by
    have hbase : (2 : ℝ) ≤ ((tailN j + 3 : Nat) : ℝ) := by
      exact_mod_cast (by omega : 2 ≤ tailN j + 3)
    have hpow2 :
        ((2 : ℝ) ^ LegalSchedule.theta) ≤
          ((tailN j + 3 : Nat) : ℝ) ^ LegalSchedule.theta := by
      exact Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 2) hbase theta_nonneg
    have h2theta : (2 : ℝ) ≤ (2 : ℝ) ^ LegalSchedule.theta := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (by linarith [two_le_theta] : (1 : ℝ) ≤ LegalSchedule.theta)
      simpa using h
    exact h2theta.trans hpow2
  have h :
      (tailK j + 1 : ℝ) ≤
        3 * ((tailN j + 3 : Nat) : ℝ) ^ LegalSchedule.theta := by
    dsimp [x] at hceil_le
    nlinarith
  rw [hN]
  simpa [S, tailSchedule] using h

theorem prefR_zero_lt_one : prefR 0 < 1 := by
  have hk := tailK_upper_total 0
  have hk0 :
      ((S.k 0 + 1 : Nat) : ℝ) ≤ 3 * (3 : ℝ) ^ LegalSchedule.theta := by
    simpa [LegalSchedule.N, S, tailSchedule] using hk
  have hk0_tail :
      ((tailK 0 + 1 : Nat) : ℝ) ≤ 3 * (3 : ℝ) ^ LegalSchedule.theta := by
    simpa [S, tailSchedule] using hk0
  have hk0_tail' :
      (tailK 0 : ℝ) + 1 ≤ 3 * (3 : ℝ) ^ LegalSchedule.theta := by
    simpa [Nat.cast_add] using hk0_tail
  have hnum :
      (prefM 0 : ℝ) * ((S.k 0 + 1 : Nat) : ℝ) ≤
        12 * (((S.N 0 + 3 : Nat) : ℝ) ^ LegalSchedule.theta) := by
    norm_num [prefM_zero, LegalSchedule.N, S, tailSchedule]
    nlinarith [hk0_tail']
  have htheta_pos :
      0 < (((S.N 0 + 3 : Nat) : ℝ) ^ LegalSchedule.theta) := by
    positivity
  have hden_pos :
      0 < (((S.N 0 + 3 : Nat) : ℝ) ^ LegalSchedule.gapExponent) := by
    positivity
  have hnum_lt_den :
      (prefM 0 : ℝ) * ((S.k 0 + 1 : Nat) : ℝ) <
        (((S.N 0 + 3 : Nat) : ℝ) ^ LegalSchedule.gapExponent) := by
    have h12 :
        12 * (((S.N 0 + 3 : Nat) : ℝ) ^ LegalSchedule.theta) <
          (((S.N 0 + 3 : Nat) : ℝ) ^ LegalSchedule.gapExponent) := by
      have hbase : ((S.N 0 + 3 : Nat) : ℝ) = 3 := by
        norm_num [LegalSchedule.N, S, tailSchedule]
      rw [hbase]
      rw [LegalSchedule.gapExponent_eq_theta_add_tau]
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      nlinarith [mul_lt_mul_of_pos_right twelve_lt_three_rpow_tau
        (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) LegalSchedule.theta)]
    exact lt_of_le_of_lt hnum h12
  exact (div_lt_one hden_pos).2 hnum_lt_den

theorem two_lt_theta : (2 : ℝ) < LegalSchedule.theta := by
  dsimp [LegalSchedule.theta]
  have hs : (1 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)]
    norm_num
  linarith

noncomputable def pointConst : ℝ :=
  3 / (2 : ℝ) ^ LegalSchedule.theta

theorem pointConst_nonneg : 0 ≤ pointConst := by
  dsimp [pointConst]
  positivity

theorem pointConst_lt_one : pointConst < 1 := by
  have hpow :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) two_lt_theta
  have hden : (3 : ℝ) < (2 : ℝ) ^ LegalSchedule.theta := by
    norm_num [Real.rpow_natCast] at hpow
    linarith
  have hpos : 0 < (2 : ℝ) ^ LegalSchedule.theta := by
    positivity
  exact (div_lt_one hpos).2 hden

theorem Q_le_sq_succ (k : Nat) :
    (Q k : ℝ) ≤ ((k + 1 : Nat) : ℝ) ^ (2 : ℝ) := by
  simp [Q, Nat.cast_add, Nat.cast_mul]
  nlinarith

theorem tailK_lower_total (j : Nat) :
    2 * (((S.N j + 3 : Nat) : ℝ) ^ LegalSchedule.theta) ≤ (S.k j : ℝ) := by
  have hN : S.N j = tailN j := tailSchedule_N j
  have hceil :
      2 * ((tailN j + 3 : Nat) : ℝ) ^ LegalSchedule.theta ≤ (tailK j : ℝ) := by
    dsimp [tailK, tailKCore]
    exact Nat.le_ceil _
  rw [hN]
  simpa [S, tailSchedule] using hceil

theorem tail_next_base_lower (j : Nat) :
    2 * (((S.N j + 3 : Nat) : ℝ) ^ LegalSchedule.theta) ≤
      ((S.N (j + 1) + 3 : Nat) : ℝ) := by
  have hk := tailK_lower_total j
  have hkle :
      (S.k j : ℝ) ≤ ((S.N (j + 1) + 3 : Nat) : ℝ) := by
    exact_mod_cast (by
      simp [LegalSchedule.N]
      omega)
  exact hk.trans hkle

theorem tail_k_succ_le_next_base (j : Nat) :
    ((S.k j + 1 : Nat) : ℝ) ≤ ((S.N (j + 1) + 3 : Nat) : ℝ) := by
  exact_mod_cast (by
    simp [LegalSchedule.N]
    omega)

theorem tail_next_base_theta_lower (j : Nat) :
    (2 : ℝ) ^ LegalSchedule.theta *
        (((S.N j + 3 : Nat) : ℝ) ^ LegalSchedule.gapExponent) ≤
      (((S.N (j + 1) + 3 : Nat) : ℝ) ^ LegalSchedule.theta) := by
  have hC := tail_next_base_lower j
  have hbase_pos : 0 < ((S.N j + 3 : Nat) : ℝ) := by positivity
  have htwoB_nonneg :
      0 ≤ 2 * (((S.N j + 3 : Nat) : ℝ) ^ LegalSchedule.theta) := by
    positivity
  have hpow :
      (2 * (((S.N j + 3 : Nat) : ℝ) ^ LegalSchedule.theta)) ^
          LegalSchedule.theta ≤
        (((S.N (j + 1) + 3 : Nat) : ℝ) ^ LegalSchedule.theta) := by
    exact Real.rpow_le_rpow htwoB_nonneg hC theta_nonneg
  have heval :
      (2 * (((S.N j + 3 : Nat) : ℝ) ^ LegalSchedule.theta)) ^
          LegalSchedule.theta =
        (2 : ℝ) ^ LegalSchedule.theta *
          (((S.N j + 3 : Nat) : ℝ) ^ LegalSchedule.gapExponent) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
      (Real.rpow_nonneg (le_of_lt hbase_pos) _)]
    rw [← Real.rpow_mul (le_of_lt hbase_pos)]
    have htheta_mul :
        LegalSchedule.theta * LegalSchedule.theta = LegalSchedule.gapExponent := by
      simpa [pow_two] using theta_sq_eq_gapExponent
    rw [htheta_mul]
  rw [← heval]
  exact hpow

theorem prefR_succ_le_const_mul (j : Nat) :
    prefR (j + 1) ≤ pointConst * prefR j := by
  let B : ℝ := ((S.N j + 3 : Nat) : ℝ)
  let C : ℝ := ((S.N (j + 1) + 3 : Nat) : ℝ)
  let K : ℝ := ((S.k j + 1 : Nat) : ℝ)
  let M : ℝ := (prefM j : ℝ)
  have hB_pos : 0 < B := by
    dsimp [B]
    positivity
  have hC_pos : 0 < C := by
    dsimp [C]
    positivity
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    positivity
  have hdenC_nonneg : 0 ≤ C ^ LegalSchedule.gapExponent := by
    positivity
  have hkup :
      ((S.k (j + 1) + 1 : Nat) : ℝ) ≤
        3 * C ^ LegalSchedule.theta := by
    simpa [C] using tailK_upper_total (j + 1)
  have hQ :
      (Q (S.k j) : ℝ) ≤ K * K := by
    have h := Q_le_sq_succ (S.k j)
    simpa [K, Real.rpow_natCast, pow_two] using h
  have hnum1 :
      (prefM (j + 1) : ℝ) * ((S.k (j + 1) + 1 : Nat) : ℝ) ≤
        ((prefM j : ℝ) * (Q (S.k j) : ℝ)) * (3 * C ^ LegalSchedule.theta) := by
    calc
      (prefM (j + 1) : ℝ) * ((S.k (j + 1) + 1 : Nat) : ℝ)
          = ((prefM j : ℝ) * (Q (S.k j) : ℝ)) *
              ((S.k (j + 1) + 1 : Nat) : ℝ) := by
            simp [prefM_succ, Nat.cast_mul]
      _ ≤ ((prefM j : ℝ) * (Q (S.k j) : ℝ)) *
            (3 * C ^ LegalSchedule.theta) := by
            exact mul_le_mul_of_nonneg_left hkup (by positivity)
  have hnum2 :
      ((prefM j : ℝ) * (Q (S.k j) : ℝ)) * (3 * C ^ LegalSchedule.theta) ≤
        (M * (K * K)) * (3 * C ^ LegalSchedule.theta) := by
    have hMQ : (prefM j : ℝ) * (Q (S.k j) : ℝ) ≤ M * (K * K) := by
      dsimp [M]
      exact mul_le_mul_of_nonneg_left hQ (by positivity)
    exact mul_le_mul_of_nonneg_right hMQ (by positivity)
  have hK_le_C : K ≤ C := by
    simpa [K, C] using tail_k_succ_le_next_base j
  have hden_lower :
      (2 : ℝ) ^ LegalSchedule.theta * B ^ LegalSchedule.gapExponent ≤
        C ^ LegalSchedule.theta := by
    simpa [B, C] using tail_next_base_theta_lower j
  have hden_lower_pos :
      0 < (2 : ℝ) ^ LegalSchedule.theta * B ^ LegalSchedule.gapExponent := by
    positivity
  calc
    prefR (j + 1)
        = ((prefM (j + 1) : ℝ) * ((S.k (j + 1) + 1 : Nat) : ℝ)) /
            C ^ LegalSchedule.gapExponent := by
          dsimp [prefR, C]
    _ ≤ (M * (K * K)) * (3 * C ^ LegalSchedule.theta) /
            C ^ LegalSchedule.gapExponent := by
          exact div_le_div_of_nonneg_right (hnum1.trans hnum2) hdenC_nonneg
    _ = 3 * M * (K * K) / C ^ LegalSchedule.tau := by
          rw [LegalSchedule.gapExponent_eq_theta_add_tau]
          rw [Real.rpow_add hC_pos LegalSchedule.theta LegalSchedule.tau]
          field_simp [ne_of_gt (Real.rpow_pos_of_pos hC_pos LegalSchedule.theta),
            ne_of_gt (Real.rpow_pos_of_pos hC_pos LegalSchedule.tau)]
    _ ≤ 3 * M * (K * C) / C ^ LegalSchedule.tau := by
          have hKK : K * K ≤ K * C :=
            mul_le_mul_of_nonneg_left hK_le_C hK_nonneg
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hKK (by positivity))
            (by positivity)
    _ = 3 * M * K / C ^ LegalSchedule.theta := by
          have htau : LegalSchedule.tau = LegalSchedule.theta + 1 := by
            linarith [tau_sub_one_eq_theta]
          rw [htau]
          rw [Real.rpow_add hC_pos LegalSchedule.theta 1, Real.rpow_one]
          field_simp [ne_of_gt hC_pos,
            ne_of_gt (Real.rpow_pos_of_pos hC_pos LegalSchedule.theta)]
    _ ≤ 3 * M * K /
          ((2 : ℝ) ^ LegalSchedule.theta * B ^ LegalSchedule.gapExponent) := by
          exact div_le_div_of_nonneg_left (by positivity) hden_lower_pos hden_lower
    _ = pointConst * prefR j := by
          dsimp [pointConst, prefR, B, K, M]
          field_simp [ne_of_gt hB_pos,
            ne_of_gt (Real.rpow_pos_of_pos hB_pos LegalSchedule.gapExponent),
            ne_of_gt (by positivity : 0 < (2 : ℝ) ^ LegalSchedule.theta)]

theorem prefR_lt_one (j : Nat) : prefR j < 1 := by
  induction j with
  | zero =>
      exact prefR_zero_lt_one
  | succ j ih =>
      have hle := prefR_succ_le_const_mul j
      have hmul_lt : pointConst * prefR j < 1 := by
        have hltR : pointConst * prefR j < 1 * prefR j :=
          mul_lt_mul_of_pos_right pointConst_lt_one (prefR_pos j)
        nlinarith
      exact lt_of_le_of_lt hle hmul_lt

theorem two_le_two_rpow_gapExponent :
    (2 : ℝ) ≤ (2 : ℝ) ^ LegalSchedule.gapExponent := by
  have hf : (1 : ℝ) ≤ LegalSchedule.gapExponent := by
    dsimp [LegalSchedule.gapExponent]
    nlinarith [Real.sqrt_nonneg 2]
  have h :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hf
  simpa using h

theorem pref_all_gap_bound :
    ∀ n : Nat,
      ((prefSeq (n + 1) - prefSeq n : Nat) : ℝ) ≤
        ((n + 1 : Nat) : ℝ) ^ LegalSchedule.gapExponent := by
  intro n
  cases n with
  | zero =>
      norm_num [pref_gap_zero]
  | succ n1 =>
      cases n1 with
      | zero =>
          rw [pref_gap_one]
          exact two_le_two_rpow_gapExponent
      | succ m =>
          let j := S.owner m
          have howner_lower : S.N j ≤ m := by
            dsimp [j]
            exact S.owner_lower m
          have hbase_le :
              ((S.N j + 3 : Nat) : ℝ) ≤ ((m + 3 : Nat) : ℝ) := by
            exact_mod_cast (by omega : S.N j + 3 ≤ m + 3)
          have hden_le :
              ((S.N j + 3 : Nat) : ℝ) ^ LegalSchedule.gapExponent ≤
                ((m + 3 : Nat) : ℝ) ^ LegalSchedule.gapExponent := by
            exact Real.rpow_le_rpow (by positivity) hbase_le LegalSchedule.gapExponent_nonneg
          have hR := prefR_lt_one j
          have hden_pos :
              0 < ((S.N j + 3 : Nat) : ℝ) ^ LegalSchedule.gapExponent := by
            positivity
          have hnum_lt :
              (prefM j : ℝ) * ((S.k j + 1 : Nat) : ℝ) <
                ((S.N j + 3 : Nat) : ℝ) ^ LegalSchedule.gapExponent := by
            exact (div_lt_one hden_pos).1 (by simpa [prefR, j] using hR)
          have hgapNat : 4 * S.GapAt m = prefM j * (S.k j + 1) := by
            dsimp [LegalSchedule.GapAt, prefM, j]
            ring
          calc
            ((prefSeq (m + 2 + 1) - prefSeq (m + 2) : Nat) : ℝ)
                = (prefM j : ℝ) * ((S.k j + 1 : Nat) : ℝ) := by
                  rw [pref_tail_gap m, hgapNat]
                  norm_num [Nat.cast_mul]
            _ ≤ ((S.N j + 3 : Nat) : ℝ) ^ LegalSchedule.gapExponent :=
                  le_of_lt hnum_lt
            _ ≤ ((m + 3 : Nat) : ℝ) ^ LegalSchedule.gapExponent := hden_le

end Prefixed

end

end AdmissibleCarry
