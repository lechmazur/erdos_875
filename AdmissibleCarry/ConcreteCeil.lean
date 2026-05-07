import AdmissibleCarry.AsymptoticAbstract

/-!
# Concrete ceiling schedule

The final Erdős 875 construction with
`k_j = ceil (2 * (1 + N_j) ^ (1 + sqrt 2))`.
-/

namespace AdmissibleCarry

noncomputable section

open Filter

def concreteKCore (N : Nat) : Nat :=
  Nat.ceil (2 * (1 + (N : ℝ)) ^ (1 + Real.sqrt 2))

def concreteN : Nat → Nat
  | 0 => 0
  | j + 1 => concreteN j + concreteKCore (concreteN j)

def concreteK (j : Nat) : Nat :=
  concreteKCore (concreteN j)

theorem concreteN_eq_rec (j : Nat) :
    concreteN j = Nat.rec 0 (fun i n => n + concreteK i) j := by
  induction j with
  | zero =>
      rfl
  | succ j ih =>
      simp [concreteN, concreteK, ih]

theorem concreteK_ge_two (j : Nat) : 2 ≤ concreteK j := by
  have hbase : (1 : ℝ) ≤ 1 + (concreteN j : ℝ) := by
    norm_num
  have hexp : (0 : ℝ) ≤ 1 + Real.sqrt 2 := by
    positivity
  have hpow : (1 : ℝ) ≤ (1 + (concreteN j : ℝ)) ^ (1 + Real.sqrt 2) :=
    Real.one_le_rpow hbase hexp
  have htwo :
      (2 : ℝ) ≤ 2 * (1 + (concreteN j : ℝ)) ^ (1 + Real.sqrt 2) := by
    nlinarith
  have hceil :
      (2 : ℝ) ≤
        (Nat.ceil (2 * (1 + (concreteN j : ℝ)) ^ (1 + Real.sqrt 2)) : ℝ) :=
    htwo.trans (Nat.le_ceil _)
  have hceil_nat :
      2 ≤ Nat.ceil (2 * (1 + (concreteN j : ℝ)) ^ (1 + Real.sqrt 2)) := by
    exact_mod_cast hceil
  simpa [concreteK, concreteKCore] using hceil_nat

theorem Q_le_two_mul_sq {k : Nat} (hk : 2 ≤ k) :
    (Q k : ℝ) ≤ 2 * (k : ℝ) ^ (2 : ℝ) := by
  have hnat : Q k ≤ 2 * k * k := by
    simp [Q]
    nlinarith
  have hcast : (Q k : ℝ) ≤ (2 * k * k : Nat) := by
    exact_mod_cast hnat
  norm_num [Nat.cast_mul, Real.rpow_natCast] at hcast ⊢
  nlinarith

theorem concreteK_growth (j : Nat) :
    4 * (Nat.rec 0 (fun i n => n + concreteK i) j) < concreteK j := by
  rw [← concreteN_eq_rec j, concreteK, concreteKCore]
  apply Nat.lt_ceil.mpr
  by_cases hN : concreteN j = 0
  · rw [hN]
    norm_num
  · have hbase : (1 : ℝ) ≤ 1 + (concreteN j : ℝ) := by
      norm_num
    have htheta2 : (2 : ℝ) ≤ 1 + Real.sqrt 2 := by
      have hs : (1 : ℝ) ≤ Real.sqrt 2 := by
        rw [Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      linarith
    have hpow2 :
        (1 + (concreteN j : ℝ)) ^ (2 : ℝ) ≤
          (1 + (concreteN j : ℝ)) ^ (1 + Real.sqrt 2) :=
      Real.rpow_le_rpow_of_exponent_le hbase htheta2
    norm_num [Nat.cast_mul, Real.rpow_natCast] at hpow2 ⊢
    nlinarith [sq_nonneg ((concreteN j : ℝ) - 1)]

def concreteSchedule : LegalSchedule where
  k := concreteK
  k_ge_two := concreteK_ge_two
  growth := concreteK_growth

theorem concreteSchedule_N (j : Nat) :
    concreteSchedule.N j = concreteN j := by
  rw [LegalSchedule.N_eq_rec, concreteN_eq_rec]
  simp [concreteSchedule]

theorem concreteK_le_succ_scale (j : Nat) :
    (concreteK j : ℝ) ≤ (concreteSchedule.scale (j + 1) : ℝ) := by
  have hN : concreteSchedule.N (j + 1) = concreteN (j + 1) := concreteSchedule_N (j + 1)
  dsimp [LegalSchedule.scale]
  rw [hN]
  exact_mod_cast (by
    change concreteK j ≤ max 1 (concreteN j + concreteK j)
    omega)

theorem scale_le_one_add_concreteN (j : Nat) :
    (concreteSchedule.scale j : ℝ) ≤ 1 + (concreteN j : ℝ) := by
  have hN : concreteSchedule.N j = concreteN j := concreteSchedule_N j
  dsimp [LegalSchedule.scale]
  rw [hN]
  exact_mod_cast
    (max_le (by omega : 1 ≤ 1 + concreteN j) (by omega : concreteN j ≤ 1 + concreteN j))

theorem one_add_concreteN_le_two_scale (j : Nat) :
    1 + (concreteN j : ℝ) ≤ 2 * (concreteSchedule.scale j : ℝ) := by
  have hN : concreteSchedule.N j = concreteN j := concreteSchedule_N j
  dsimp [LegalSchedule.scale]
  rw [hN]
  exact_mod_cast (by
    change 1 + concreteN j ≤ 2 * max 1 (concreteN j)
    omega)

theorem theta_nonneg : (0 : ℝ) ≤ LegalSchedule.theta := by
  dsimp [LegalSchedule.theta]
  positivity

theorem theta_le_three : LegalSchedule.theta ≤ (3 : ℝ) := by
  dsimp [LegalSchedule.theta]
  have hsq : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := by
    rw [← pow_two, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hsnonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  nlinarith

theorem two_rpow_theta_le_eight :
    (2 : ℝ) ^ LegalSchedule.theta ≤ 8 := by
  have h :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) theta_le_three
  norm_num [Real.rpow_natCast] at h ⊢
  exact h

theorem concreteK_lower_scale (j : Nat) :
    2 * (concreteSchedule.scale j : ℝ) ^ LegalSchedule.theta ≤ (concreteK j : ℝ) := by
  have hscale := scale_le_one_add_concreteN j
  have hpow :
      (concreteSchedule.scale j : ℝ) ^ LegalSchedule.theta ≤
        (1 + (concreteN j : ℝ)) ^ LegalSchedule.theta := by
    exact Real.rpow_le_rpow (by positivity) hscale theta_nonneg
  have hmul :
      2 * (concreteSchedule.scale j : ℝ) ^ LegalSchedule.theta ≤
        2 * (1 + (concreteN j : ℝ)) ^ LegalSchedule.theta := by
    nlinarith
  have hceil :
      2 * (1 + (concreteN j : ℝ)) ^ LegalSchedule.theta ≤ (concreteK j : ℝ) := by
    dsimp [concreteK, concreteKCore, LegalSchedule.theta]
    exact Nat.le_ceil _
  exact hmul.trans hceil

theorem concreteK_upper_scale (j : Nat) :
    (concreteK j + 1 : ℝ) ≤ 20 * (concreteSchedule.scale j : ℝ) ^ LegalSchedule.theta := by
  let x : ℝ := 2 * (1 + (concreteN j : ℝ)) ^ LegalSchedule.theta
  have hx_nonneg : 0 ≤ x := by
    dsimp [x, LegalSchedule.theta]
    positivity
  have hceil_lt : (concreteK j : ℝ) < x + 1 := by
    dsimp [concreteK, concreteKCore, x, LegalSchedule.theta]
    exact Nat.ceil_lt_add_one hx_nonneg
  have hceil_le : (concreteK j + 1 : ℝ) ≤ x + 2 := by
    linarith
  have hscale_nonneg : 0 ≤ (concreteSchedule.scale j : ℝ) := by
    positivity
  have hone_le_scale : (1 : ℝ) ≤ concreteSchedule.scale j := by
    dsimp [LegalSchedule.scale]
    exact_mod_cast le_max_left 1 (concreteSchedule.N j)
  have hx_bound : x ≤ 16 * (concreteSchedule.scale j : ℝ) ^ LegalSchedule.theta := by
    have hbase := one_add_concreteN_le_two_scale j
    have hpow :
        (1 + (concreteN j : ℝ)) ^ LegalSchedule.theta ≤
          (2 * (concreteSchedule.scale j : ℝ)) ^ LegalSchedule.theta := by
      exact Real.rpow_le_rpow (by positivity) hbase theta_nonneg
    have hmulr :
        (2 * (concreteSchedule.scale j : ℝ)) ^ LegalSchedule.theta =
          (2 : ℝ) ^ LegalSchedule.theta * (concreteSchedule.scale j : ℝ) ^
            LegalSchedule.theta := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hscale_nonneg]
    have hpow_bound :
        (2 * (concreteSchedule.scale j : ℝ)) ^ LegalSchedule.theta ≤
          8 * (concreteSchedule.scale j : ℝ) ^ LegalSchedule.theta := by
      rw [hmulr]
      exact mul_le_mul_of_nonneg_right two_rpow_theta_le_eight
        (Real.rpow_nonneg hscale_nonneg _)
    dsimp [x]
    nlinarith
  have htwo_le : (2 : ℝ) ≤ 4 * (concreteSchedule.scale j : ℝ) ^ LegalSchedule.theta := by
    have hp : (1 : ℝ) ≤ (concreteSchedule.scale j : ℝ) ^ LegalSchedule.theta :=
      Real.one_le_rpow hone_le_scale theta_nonneg
    nlinarith
  nlinarith

theorem concrete_decay_factor_le (j : Nat) :
    2 * (concreteK j : ℝ) ^ (2 - LegalSchedule.tau) ≤
      LegalSchedule.rho / (concreteSchedule.scale j : ℝ) ^ LegalSchedule.tau := by
  let s : ℝ := concreteSchedule.scale j
  let a : ℝ := 2 * s ^ LegalSchedule.theta
  have hs_pos : 0 < s := by
    dsimp [s]
    exact LegalSchedule.scale_pos concreteSchedule j
  have hs_nonneg : 0 ≤ s := le_of_lt hs_pos
  have ha_pos : 0 < a := by
    dsimp [a]
    positivity
  have hk_pos : 0 < (concreteK j : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) (concreteK_ge_two j))
  have hexp_neg : 2 - LegalSchedule.tau < 0 := by
    rw [LegalSchedule.two_sub_tau]
    exact neg_neg_of_pos LegalSchedule.sqrt_two_pos
  have hlower : a ≤ (concreteK j : ℝ) := by
    dsimp [a, s]
    exact concreteK_lower_scale j
  have hpow_le :
      (concreteK j : ℝ) ^ (2 - LegalSchedule.tau) ≤ a ^ (2 - LegalSchedule.tau) := by
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

theorem concrete_P_succ_le (j : Nat) :
    concreteSchedule.P (j + 1) ≤ LegalSchedule.rho * concreteSchedule.P j := by
  have hM_nonneg : 0 ≤ (concreteSchedule.M j : ℝ) := by
    positivity
  have hk_pos : 0 < (concreteK j : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) (concreteK_ge_two j))
  have hQ : (Q (concreteK j) : ℝ) ≤ 2 * (concreteK j : ℝ) ^ (2 : ℝ) :=
    Q_le_two_mul_sq (concreteK_ge_two j)
  have hnum :
      (concreteSchedule.M j : ℝ) * (Q (concreteK j) : ℝ) ≤
        (concreteSchedule.M j : ℝ) * (2 * (concreteK j : ℝ) ^ (2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hQ hM_nonneg
  have hscale_succ_tau_nonneg :
      0 ≤ (concreteSchedule.scale (j + 1) : ℝ) ^ LegalSchedule.tau := by
    exact Real.rpow_nonneg (le_of_lt (LegalSchedule.scale_pos concreteSchedule (j + 1))) _
  have hden :
      (concreteK j : ℝ) ^ LegalSchedule.tau ≤
        (concreteSchedule.scale (j + 1) : ℝ) ^ LegalSchedule.tau := by
    exact Real.rpow_le_rpow (le_of_lt hk_pos) (concreteK_le_succ_scale j)
      (le_of_lt LegalSchedule.tau_pos)
  have hk_tau_pos : 0 < (concreteK j : ℝ) ^ LegalSchedule.tau :=
    Real.rpow_pos_of_pos hk_pos _
  have hbig_nonneg :
      0 ≤ (concreteSchedule.M j : ℝ) * (2 * (concreteK j : ℝ) ^ (2 : ℝ)) := by
    positivity
  calc
    concreteSchedule.P (j + 1)
        = ((concreteSchedule.M j : Nat) * Q (concreteK j) : ℝ) /
            (concreteSchedule.scale (j + 1) : ℝ) ^ LegalSchedule.tau := by
          simp [LegalSchedule.P, LegalSchedule.M, concreteSchedule]
    _ = (concreteSchedule.M j : ℝ) * (Q (concreteK j) : ℝ) /
            (concreteSchedule.scale (j + 1) : ℝ) ^ LegalSchedule.tau := by
          norm_num [Nat.cast_mul]
    _ ≤ (concreteSchedule.M j : ℝ) * (2 * (concreteK j : ℝ) ^ (2 : ℝ)) /
            (concreteSchedule.scale (j + 1) : ℝ) ^ LegalSchedule.tau := by
          exact div_le_div_of_nonneg_right hnum hscale_succ_tau_nonneg
    _ ≤ (concreteSchedule.M j : ℝ) * (2 * (concreteK j : ℝ) ^ (2 : ℝ)) /
            (concreteK j : ℝ) ^ LegalSchedule.tau := by
          exact div_le_div_of_nonneg_left hbig_nonneg hk_tau_pos hden
    _ = (concreteSchedule.M j : ℝ) *
          (2 * (concreteK j : ℝ) ^ (2 - LegalSchedule.tau)) := by
          rw [Real.rpow_sub hk_pos 2 LegalSchedule.tau]
          ring
    _ ≤ (concreteSchedule.M j : ℝ) *
          (LegalSchedule.rho / (concreteSchedule.scale j : ℝ) ^ LegalSchedule.tau) := by
          exact mul_le_mul_of_nonneg_left (concrete_decay_factor_le j) hM_nonneg
    _ = LegalSchedule.rho * concreteSchedule.P j := by
          dsimp [LegalSchedule.P]
          ring

theorem concrete_P_tendsto_zero :
    Filter.Tendsto concreteSchedule.P Filter.atTop (nhds 0) :=
  LegalSchedule.P_tendsto_zero_of_geometric concreteSchedule concrete_P_succ_le

theorem concrete_gap_ratio_le_twenty_P_owner (n : Nat) :
    (concreteSchedule.GapAt n : ℝ) / ((n + 1 : Nat) : ℝ) ^ LegalSchedule.gapExponent ≤
      20 * concreteSchedule.P (concreteSchedule.owner n) := by
  let j := concreteSchedule.owner n
  have hM_nonneg : 0 ≤ (concreteSchedule.M j : ℝ) := by
    positivity
  have hgap_num :
      (concreteSchedule.GapAt n : ℝ) ≤
        (concreteSchedule.M j : ℝ) *
          (20 * (concreteSchedule.scale j : ℝ) ^ LegalSchedule.theta) := by
    have hk := concreteK_upper_scale j
    have hmul := mul_le_mul_of_nonneg_left hk hM_nonneg
    simpa [LegalSchedule.GapAt, concreteSchedule, j, Nat.cast_mul] using hmul
  have hden_nonneg : 0 ≤ ((n + 1 : Nat) : ℝ) ^ LegalSchedule.gapExponent := by
    positivity
  have hs_pos : 0 < (concreteSchedule.scale j : ℝ) := by
    dsimp [j]
    exact LegalSchedule.scale_pos concreteSchedule (concreteSchedule.owner n)
  have hden_scale_pos :
      0 < (concreteSchedule.scale j : ℝ) ^ LegalSchedule.gapExponent :=
    Real.rpow_pos_of_pos hs_pos _
  have hbase : (concreteSchedule.scale j : ℝ) ≤ ((n + 1 : Nat) : ℝ) := by
    dsimp [j]
    exact LegalSchedule.scale_owner_le_succ concreteSchedule n
  have hden :
      (concreteSchedule.scale j : ℝ) ^ LegalSchedule.gapExponent ≤
        ((n + 1 : Nat) : ℝ) ^ LegalSchedule.gapExponent := by
    exact Real.rpow_le_rpow (le_of_lt hs_pos) hbase LegalSchedule.gapExponent_nonneg
  have hnum_nonneg :
      0 ≤ (concreteSchedule.M j : ℝ) *
        (20 * (concreteSchedule.scale j : ℝ) ^ LegalSchedule.theta) := by
    positivity
  calc
    (concreteSchedule.GapAt n : ℝ) / ((n + 1 : Nat) : ℝ) ^ LegalSchedule.gapExponent
        ≤ ((concreteSchedule.M j : ℝ) *
            (20 * (concreteSchedule.scale j : ℝ) ^ LegalSchedule.theta)) /
            ((n + 1 : Nat) : ℝ) ^ LegalSchedule.gapExponent := by
          exact div_le_div_of_nonneg_right hgap_num hden_nonneg
    _ ≤ ((concreteSchedule.M j : ℝ) *
            (20 * (concreteSchedule.scale j : ℝ) ^ LegalSchedule.theta)) /
            (concreteSchedule.scale j : ℝ) ^ LegalSchedule.gapExponent := by
          exact div_le_div_of_nonneg_left hnum_nonneg hden_scale_pos hden
    _ = 20 * concreteSchedule.P j := by
          dsimp [LegalSchedule.P]
          rw [LegalSchedule.gapExponent_eq_theta_add_tau]
          rw [Real.rpow_add hs_pos LegalSchedule.theta LegalSchedule.tau]
          field_simp [ne_of_gt (Real.rpow_pos_of_pos hs_pos LegalSchedule.theta),
            ne_of_gt (Real.rpow_pos_of_pos hs_pos LegalSchedule.tau)]

theorem concrete_gap_ratio_tendsto :
    Filter.Tendsto
      (fun n : Nat =>
        (concreteSchedule.GapAt n : ℝ) / ((n + 1 : Nat) : ℝ) ^ LegalSchedule.gapExponent)
      Filter.atTop (nhds 0) := by
  have howner := LegalSchedule.owner_tendsto_atTop concreteSchedule
  have hPowner :
      Filter.Tendsto (fun n : Nat => concreteSchedule.P (concreteSchedule.owner n))
        Filter.atTop (nhds 0) :=
    concrete_P_tendsto_zero.comp howner
  have hupper :
      Filter.Tendsto (fun n : Nat => 20 * concreteSchedule.P (concreteSchedule.owner n))
        Filter.atTop (nhds 0) := by
    simpa using Filter.Tendsto.const_mul (20 : ℝ) hPowner
  exact squeeze_zero (fun n => by positivity) concrete_gap_ratio_le_twenty_P_owner hupper

def finalSet : Set Nat :=
  Set.range concreteSchedule.seq

theorem finalSet_infinite :
    finalSet.Infinite := by
  simpa [finalSet] using
    Set.infinite_range_of_injective concreteSchedule.strictMono_seq.injective

theorem finalSet_admissible :
    PaperAdmSet finalSet := by
  classical
  intro U V hU hV hsum
  let a := concreteSchedule.seq
  have hinj : Function.Injective a := concreteSchedule.strictMono_seq.injective
  have hpreInjU : Set.InjOn a (a ⁻¹' (U : Set Nat)) := fun _ _ _ _ h => hinj h
  have hpreInjV : Set.InjOn a (a ⁻¹' (V : Set Nat)) := fun _ _ _ _ h => hinj h
  let Uidx := U.preimage a hpreInjU
  let Vidx := V.preimage a hpreInjV
  have hsumUidx : Uidx.sum a = U.sum (fun x : Nat => x) := by
    dsimp [Uidx]
    simpa using
      (Finset.sum_preimage a U hpreInjU (fun x : Nat => x) (by
        intro x hx hxrange
        exact (hxrange (by simpa [finalSet, a] using hU x hx)).elim))
  have hsumVidx : Vidx.sum a = V.sum (fun x : Nat => x) := by
    dsimp [Vidx]
    simpa using
      (Finset.sum_preimage a V hpreInjV (fun x : Nat => x) (by
        intro x hx hxrange
        exact (hxrange (by simpa [finalSet, a] using hV x hx)).elim))
  have hsumIdx : Uidx.sum a = Vidx.sum a := by
    rw [hsumUidx, hsumVidx]
    exact hsum
  have hcardIdx : Uidx.card = Vidx.card :=
    concreteSchedule.admSeq Uidx Vidx hsumIdx
  have hfilterU : {x ∈ U | x ∈ Set.range a} = U := by
    ext x
    constructor
    · intro hx
      exact (Finset.mem_filter.mp hx).1
    · intro hx
      exact Finset.mem_filter.mpr ⟨hx, by simpa [finalSet, a] using hU x hx⟩
  have hfilterV : {x ∈ V | x ∈ Set.range a} = V := by
    ext x
    constructor
    · intro hx
      exact (Finset.mem_filter.mp hx).1
    · intro hx
      exact Finset.mem_filter.mpr ⟨hx, by simpa [finalSet, a] using hV x hx⟩
  have hcardU : Uidx.card = U.card := by
    dsimp [Uidx]
    rw [Finset.card_preimage, hfilterU]
  have hcardV : Vidx.card = V.card := by
    dsimp [Vidx]
    rw [Finset.card_preimage, hfilterV]
  omega

theorem final_analysis_ready :
    LegalSchedule.AnalysisReady concreteSchedule := by
  refine
    { strictMono_seq := concreteSchedule.strictMono_seq
      uniform_gap' := concreteSchedule.uniform_gap_at
      gap_ratio_tendsto := concrete_gap_ratio_tendsto }

theorem final_gap_tendsto :
    Filter.Tendsto
      (fun n : Nat =>
        ((concreteSchedule.seq (n + 1) - concreteSchedule.seq n : Nat) : ℝ) /
          ((n + 1 : Nat) : ℝ) ^ LegalSchedule.gapExponent)
      Filter.atTop (nhds 0) :=
  LegalSchedule.abstract_gap_little_o concreteSchedule final_analysis_ready

theorem final_gap_eventually_le_rpow :
    ∀ᶠ n : Nat in Filter.atTop,
      ((concreteSchedule.seq (n + 1) - concreteSchedule.seq n : Nat) : ℝ) ≤
        ((n + 1 : Nat) : ℝ) ^ LegalSchedule.gapExponent := by
  have hratio :
      ∀ᶠ n : Nat in Filter.atTop,
        ((concreteSchedule.seq (n + 1) - concreteSchedule.seq n : Nat) : ℝ) /
            ((n + 1 : Nat) : ℝ) ^ LegalSchedule.gapExponent ≤ 1 :=
    Filter.Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1) final_gap_tendsto
  filter_upwards [hratio] with n hn
  have hden_pos : 0 < ((n + 1 : Nat) : ℝ) ^ LegalSchedule.gapExponent := by
    positivity
  have h := (div_le_iff₀ hden_pos).mp hn
  simpa using h

theorem final_construction :
    finalSet.Infinite ∧
      PaperAdmSet finalSet ∧
      StrictMono concreteSchedule.seq ∧
      Filter.Tendsto
        (fun n : Nat =>
          ((concreteSchedule.seq (n + 1) - concreteSchedule.seq n : Nat) : ℝ) /
            ((n + 1 : Nat) : ℝ) ^ LegalSchedule.gapExponent)
        Filter.atTop (nhds 0) ∧
      ∀ᶠ n : Nat in Filter.atTop,
        ((concreteSchedule.seq (n + 1) - concreteSchedule.seq n : Nat) : ℝ) ≤
          ((n + 1 : Nat) : ℝ) ^ LegalSchedule.gapExponent := by
  exact
    ⟨finalSet_infinite, finalSet_admissible, concreteSchedule.strictMono_seq,
      final_gap_tendsto, final_gap_eventually_le_rpow⟩

end

end AdmissibleCarry
