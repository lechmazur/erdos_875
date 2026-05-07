import AdmissibleCarry.Closure

/-!
# Abstract stages

Zero-indexed block stages from an abstract block-length schedule.
-/

namespace AdmissibleCarry

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

def F (S : LegalSchedule) : Nat → Finset Nat
  | 0 => ∅
  | j + 1 => stepSet (S.F j) (S.M j) (S.k j)

def Sigma (S : LegalSchedule) : Nat → Nat
  | 0 => 0
  | j + 1 => stepSigma (S.Sigma j) (S.M j) (S.k j)

theorem N_eq_rec (S : LegalSchedule) (j : Nat) :
    S.N j = Nat.rec 0 (fun i n => n + S.k i) j := by
  induction j with
  | zero =>
      rfl
  | succ j ih =>
      simp [N, ih]

theorem growth_N (S : LegalSchedule) (j : Nat) :
    4 * S.N j < S.k j := by
  rw [S.N_eq_rec j]
  exact S.growth j

theorem M_pos (S : LegalSchedule) (j : Nat) : 0 < S.M j := by
  induction j with
  | zero =>
      simp [M]
  | succ j ih =>
      exact Nat.mul_pos ih (Q_pos (S.k j))

theorem blockSigma_le (k : Nat) :
    (k * k * k + k) / 2 ≤ Q k * k := by
  have h : (k * k * k + k) / 2 ≤ k * k * k + k := Nat.div_le_self _ _
  simp [Q]
  nlinarith

theorem Sigma_le_M_mul_N (S : LegalSchedule) (j : Nat) :
    S.Sigma j ≤ S.M j * S.N j := by
  induction j with
  | zero =>
      simp [Sigma, N]
  | succ j ih =>
      have hblock : (S.k j * S.k j * S.k j + S.k j) / 2 ≤ Q (S.k j) * S.k j :=
        blockSigma_le (S.k j)
      have hblockM :
          S.M j * ((S.k j * S.k j * S.k j + S.k j) / 2) ≤
            S.M j * (Q (S.k j) * S.k j) :=
        Nat.mul_le_mul_left (S.M j) hblock
      have ihQ : S.Sigma j ≤ Q (S.k j) * (S.M j * S.N j) :=
        ih.trans (Nat.le_mul_of_pos_left (S.M j * S.N j) (Q_pos (S.k j)))
      simp [Sigma, M, N, stepSigma]
      nlinarith

theorem OldSmall_stage (S : LegalSchedule) (j : Nat) :
    OldSmall (S.Sigma j) (S.M j) (S.k j) := by
  dsimp [OldSmall]
  have hsigma := S.Sigma_le_M_mul_N j
  have hg := S.growth_N j
  have hM := S.M_pos j
  nlinarith [Nat.mul_lt_mul_of_pos_left hg hM, Nat.mul_le_mul_left 4 hsigma]

theorem NewSmall_step (S : LegalSchedule) (j : Nat) :
    NewSmall (stepSigma (S.Sigma j) (S.M j) (S.k j)) (S.M j * Q (S.k j)) (S.k j) := by
  dsimp [NewSmall, stepSigma]
  have hsigma := S.Sigma_le_M_mul_N j
  have hg := S.growth_N j
  have hM := S.M_pos j
  have hk2 : 2 ≤ S.k j := S.k_ge_two j
  have hblock_bound :
      2 * (S.M j * ((S.k j * S.k j * S.k j + S.k j) / 2)) ≤
        S.M j * (S.k j * S.k j * S.k j + S.k j) := by
    have h :=
      Nat.mul_le_mul_left (S.M j) (Nat.mul_div_le (S.k j * S.k j * S.k j + S.k j) 2)
    nlinarith
  have hsig2 : 2 * S.Sigma j ≤ 2 * (S.M j * S.N j) :=
    Nat.mul_le_mul_left 2 hsigma
  have hmn : 2 * (S.M j * S.N j) < S.M j * S.k j := by
    nlinarith [Nat.mul_lt_mul_of_pos_left hg hM]
  simp [Q]
  nlinarith

theorem stage_invariant (S : LegalSchedule) (j : Nat) :
    CarryState (S.F j) (S.M j) (S.Sigma j) := by
  induction j with
  | zero =>
      refine { Mpos := ?_, sigmaEq := ?_, posMem := ?_, ltM := ?_, carry := ?_ }
      · simp [M]
      · simp [Sigma, F, sumN]
      · intro a ha
        simp [F] at ha
      · intro a ha
        simp [F] at ha
      · intro T D q hdiff hD
        rcases hdiff with ⟨c, hT, hval⟩
        simp [F, grade] at hT
        simp [F, value] at hval
        simp [M] at hD
        omega
  | succ j ih =>
      have hclosed := closure_step (S.k_ge_two j) ih (S.OldSmall_stage j) (S.NewSmall_step j)
      simpa [F, M, Sigma] using hclosed.1

theorem stage_admissible (S : LegalSchedule) (j : Nat) :
    AdmFin (S.F j) := by
  intro t ht hdiff
  exact ht ((stage_invariant S j).carry t 0 0 hdiff (by simp))

end LegalSchedule

end AdmissibleCarry
