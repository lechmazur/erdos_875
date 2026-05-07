import AdmissibleCarry.Enumeration

/-!
# Abstract asymptotic wrapper

This is the first layer that may use filters and real powers.
-/

namespace AdmissibleCarry

open Filter

namespace LegalSchedule

noncomputable def theta : ℝ :=
  1 + Real.sqrt 2

noncomputable def tau : ℝ :=
  2 + Real.sqrt 2

noncomputable def gapExponent : ℝ :=
  3 + 2 * Real.sqrt 2

noncomputable def rho : ℝ :=
  (2 : ℝ) ^ (1 - Real.sqrt 2)

theorem gapExponent_eq_theta_add_tau :
    gapExponent = theta + tau := by
  dsimp [gapExponent, theta, tau]
  ring

theorem gapExponent_nonneg : 0 ≤ gapExponent := by
  dsimp [gapExponent]
  positivity

theorem two_sub_tau :
    2 - tau = -Real.sqrt 2 := by
  dsimp [tau]
  ring

theorem tau_eq_theta_mul_sqrt_two :
    tau = theta * Real.sqrt 2 := by
  dsimp [theta, tau]
  have hsq : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := by
    rw [← pow_two, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  nlinarith

theorem sqrt_two_pos : 0 < Real.sqrt 2 := by
  rw [Real.sqrt_pos]
  norm_num

theorem tau_pos : 0 < tau := by
  dsimp [tau]
  positivity

theorem rho_nonneg : 0 ≤ rho := by
  dsimp [rho]
  positivity

theorem rho_lt_one : rho < 1 := by
  dsimp [rho]
  have hlt : (1 - Real.sqrt 2 : ℝ) < 0 := by
    have hs : (1 : ℝ) < Real.sqrt 2 := by
      rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)]
      norm_num
    linarith
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2) hlt

def scale (S : LegalSchedule) (j : Nat) : Nat :=
  max 1 (S.N j)

noncomputable def P (S : LegalSchedule) (j : Nat) : ℝ :=
  (S.M j : ℝ) / (S.scale j : ℝ) ^ tau

theorem scale_pos (S : LegalSchedule) (j : Nat) :
    0 < (S.scale j : ℝ) := by
  dsimp [scale]
  positivity

theorem scale_owner_le_succ (S : LegalSchedule) (n : Nat) :
    (S.scale (S.owner n) : ℝ) ≤ ((n + 1 : Nat) : ℝ) := by
  have hlower : S.N (S.owner n) ≤ n := S.owner_lower n
  dsimp [scale]
  exact_mod_cast (max_le (by omega : 1 ≤ n + 1) (by omega : S.N (S.owner n) ≤ n + 1))

theorem owner_tendsto_atTop (S : LegalSchedule) :
    Tendsto S.owner atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro J
  refine ⟨S.N J, ?_⟩
  intro n hn
  by_contra hnot
  have hlt : S.owner n < J := Nat.lt_of_not_ge hnot
  have hsucc : S.owner n + 1 ≤ J := by omega
  have hNle : S.N (S.owner n + 1) ≤ S.N J := S.N_mono hsucc
  have hspec := S.owner_spec n
  omega

theorem P_nonneg (S : LegalSchedule) (j : Nat) :
    0 ≤ S.P j := by
  dsimp [P]
  positivity

theorem P_tendsto_zero_of_geometric (S : LegalSchedule)
    (hgeom : ∀ j, S.P (j + 1) ≤ rho * S.P j) :
    Tendsto S.P atTop (nhds 0) := by
  have hle : ∀ j, S.P j ≤ rho ^ j * S.P 0 := by
    intro j
    exact le_geom rho_nonneg j (fun k _hk => hgeom k)
  have hupper : Tendsto (fun j : Nat => rho ^ j * S.P 0) atTop (nhds 0) := by
    have hrho0 : Tendsto (fun j : Nat => rho ^ j) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one rho_nonneg rho_lt_one
    simpa using Filter.Tendsto.mul_const (S.P 0) hrho0
  exact squeeze_zero (fun j => S.P_nonneg j) hle hupper

structure AnalysisReady (S : LegalSchedule) : Prop where
  strictMono_seq : StrictMono S.seq
  uniform_gap' : ∀ n, S.seq (n + 1) - S.seq n = S.GapAt n
  gap_ratio_tendsto :
    Tendsto (fun n : Nat => (S.GapAt n : ℝ) / ((n + 1 : Nat) : ℝ) ^ gapExponent)
      atTop (nhds 0)

theorem abstract_gap_little_o (S : LegalSchedule) (h : AnalysisReady S) :
    Tendsto
      (fun n : Nat => ((S.seq (n + 1) - S.seq n : Nat) : ℝ) /
        ((n + 1 : Nat) : ℝ) ^ gapExponent)
      atTop (nhds 0) := by
  simpa [h.uniform_gap'] using h.gap_ratio_tendsto

end LegalSchedule

end AdmissibleCarry
