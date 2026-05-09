import AdmissibleCarry.PrefixedTail

/-!
# Prefixed finite stages

This file starts the construction from the finite prefix `{1, 2}` with modulus
`4`, then appends the blocks prescribed by the shifted tail schedule.
-/

namespace AdmissibleCarry

noncomputable section

namespace Prefixed

def prefPrefix : Finset Nat :=
  ({1, 2} : Finset Nat)

def prefN (j : Nat) : Nat :=
  2 + S.N j

def prefM (j : Nat) : Nat :=
  4 * S.M j

def prefSigma (j : Nat) : Nat :=
  3 + 4 * S.Sigma j

def prefF : Nat → Finset Nat
  | 0 => prefPrefix
  | j + 1 => stepSet (prefF j) (prefM j) (S.k j)

@[simp] theorem prefN_zero : prefN 0 = 2 := by
  simp [prefN, LegalSchedule.N]

@[simp] theorem prefM_zero : prefM 0 = 4 := by
  simp [prefM, LegalSchedule.M]

@[simp] theorem prefSigma_zero : prefSigma 0 = 3 := by
  simp [prefSigma, LegalSchedule.Sigma]

@[simp] theorem prefF_zero : prefF 0 = prefPrefix := rfl

theorem prefM_pos (j : Nat) : 0 < prefM j := by
  dsimp [prefM]
  exact Nat.mul_pos (by norm_num) (S.M_pos j)

theorem prefM_succ (j : Nat) :
    prefM (j + 1) = prefM j * Q (S.k j) := by
  simp [prefM, LegalSchedule.M]
  ring

theorem prefSigma_succ (j : Nat) :
    prefSigma (j + 1) = stepSigma (prefSigma j) (prefM j) (S.k j) := by
  simp [prefSigma, LegalSchedule.Sigma, stepSigma, prefM]
  ring

theorem prefix_sumN : sumN prefPrefix = 3 := by
  simp [prefPrefix, sumN]

theorem prefix_value_zero_grade_zero {c : CoeffOn prefPrefix}
    (hval : value prefPrefix c = 0) :
  grade prefPrefix c = 0 := by
  cases h1 : c.sign 1 <;> cases h2 : c.sign 2 <;>
    simp [prefPrefix, value, grade, h1, h2] at hval ⊢

theorem prefix_carryState : CarryState prefPrefix 4 3 := by
  refine { Mpos := ?_, sigmaEq := ?_, posMem := ?_, ltM := ?_, carry := ?_ }
  · norm_num
  · simp [prefix_sumN]
  · intro a ha
    simp [prefPrefix] at ha
    omega
  · intro a ha
    simp [prefPrefix] at ha
    omega
  · intro T D q hdiff hD
    rcases hdiff with ⟨c, hT, hval⟩
    have hbound : D.natAbs ≤ 3 := by
      have h := value_natAbs_le_sumN prefPrefix c
      rw [prefix_sumN] at h
      rw [hval] at h
      exact h
    have hq0 : q = 0 := by
      have hDabs : D.natAbs = 4 * q.natAbs := by
        rw [hD, Int.natAbs_mul]
        simp
      rw [hDabs] at hbound
      have hqabs : q.natAbs = 0 := by omega
      exact Int.natAbs_eq_zero.mp hqabs
    subst q
    have hD0 : D = 0 := by
      simpa using hD
    have hval0 : value prefPrefix c = 0 := by
      rw [hval, hD0]
    have hgrade0 := prefix_value_zero_grade_zero hval0
    omega

theorem prefSigma_le_prefM_mul_prefN (j : Nat) :
    prefSigma j ≤ prefM j * prefN j := by
  have hsigma := S.Sigma_le_M_mul_N j
  have hM := S.M_pos j
  dsimp [prefSigma, prefM, prefN]
  nlinarith

theorem prefGrowth_count (j : Nat) :
    4 * prefN j < S.k j := by
  have h := prefGrowth_N j
  dsimp [prefN]
  nlinarith

theorem prefOldSmall_stage (j : Nat) :
    OldSmall (prefSigma j) (prefM j) (S.k j) := by
  dsimp [OldSmall]
  have hsigma := prefSigma_le_prefM_mul_prefN j
  have hg := prefGrowth_count j
  have hM := prefM_pos j
  nlinarith [Nat.mul_lt_mul_of_pos_left hg hM, Nat.mul_le_mul_left 4 hsigma]

theorem prefNewSmall_step (j : Nat) :
    NewSmall (stepSigma (prefSigma j) (prefM j) (S.k j)) (prefM j * Q (S.k j)) (S.k j) := by
  dsimp [NewSmall, stepSigma]
  have hsigma := prefSigma_le_prefM_mul_prefN j
  have hg := prefGrowth_count j
  have hM := prefM_pos j
  have hk2 : 2 ≤ S.k j := S.k_ge_two j
  have hblock_bound :
      2 * (prefM j * ((S.k j * S.k j * S.k j + S.k j) / 2)) ≤
        prefM j * (S.k j * S.k j * S.k j + S.k j) := by
    have h :=
      Nat.mul_le_mul_left (prefM j) (Nat.mul_div_le (S.k j * S.k j * S.k j + S.k j) 2)
    nlinarith
  have hsig2 : 2 * prefSigma j ≤ 2 * (prefM j * prefN j) :=
    Nat.mul_le_mul_left 2 hsigma
  have hmn : 2 * (prefM j * prefN j) < prefM j * S.k j := by
    nlinarith [Nat.mul_lt_mul_of_pos_left hg hM]
  simp [Q]
  nlinarith

theorem prefStage_invariant (j : Nat) :
    CarryState (prefF j) (prefM j) (prefSigma j) := by
  induction j with
  | zero =>
      exact prefix_carryState
  | succ j ih =>
      have hclosed := closure_step (S.k_ge_two j) ih
        (prefOldSmall_stage j) (prefNewSmall_step j)
      simpa [prefF, prefM_succ, prefSigma_succ] using hclosed.1

theorem prefStage_admissible (j : Nat) :
    AdmFin (prefF j) := by
  intro t ht hdiff
  exact ht ((prefStage_invariant j).carry t 0 0 hdiff (by simp))

end Prefixed

end

end AdmissibleCarry
