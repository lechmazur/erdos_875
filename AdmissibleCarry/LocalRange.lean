import AdmissibleCarry.CoeffDiff

/-!
# Local range blocks

Definitions for the block `C_m = {1 + i * (m + 1) | 0 ≤ i < m}` and its
range-sum signed difference predicates.
-/

namespace AdmissibleCarry

open scoped BigOperators

def cell (m i : Nat) : Nat :=
  1 + i * (m + 1)

def C (m : Nat) : Finset Nat :=
  (Finset.range m).image (cell m)

def Q (m : Nat) : Nat :=
  m * m + m + 1

def localGrade (m : Nat) (eps : Nat → Sign3) : Int :=
  (Finset.range m).sum fun i => Sign3.sgn (eps i)

def localIndex (m : Nat) (eps : Nat → Sign3) : Int :=
  (Finset.range m).sum fun i => Sign3.sgn (eps i) * (i : Int)

def localValue (m : Nat) (eps : Nat → Sign3) : Int :=
  (Finset.range m).sum fun i => Sign3.sgn (eps i) * (cell m i : Int)

def CDiff (m : Nat) (t y : Int) : Prop :=
  ∃ eps : Nat → Sign3, localGrade m eps = t ∧ localValue m eps = y

def defectTotal (m : Nat) (eps : Nat → Sign3) : Nat :=
  (Finset.range m).sum fun i => Sign3.defect (eps i)

def weightedDefectTotal (m : Nat) (eps : Nat → Sign3) : Nat :=
  (Finset.range m).sum fun i => i * Sign3.defect (eps i)

theorem cell_pos (m i : Nat) : 0 < cell m i := by
  simp [cell]

theorem Q_pos (m : Nat) : 0 < Q m := by
  simp [Q]

theorem cell_lt_Q {k i : Nat} (hi : i < k) :
    cell k i < Q k := by
  simp [cell, Q]
  nlinarith

theorem C_pos {k c : Nat} (hc : c ∈ C k) : 0 < c := by
  rcases Finset.mem_image.mp hc with ⟨i, _hi, rfl⟩
  exact cell_pos k i

theorem C_lt_Q {k c : Nat} (hc : c ∈ C k) : c < Q k := by
  rcases Finset.mem_image.mp hc with ⟨i, hi, rfl⟩
  exact cell_lt_Q (by simpa using hi)

theorem localValue_eq_grade_add (m : Nat) (eps : Nat → Sign3) :
    localValue m eps =
      localGrade m eps + ((m : Int) + 1) * localIndex m eps := by
  calc
    localValue m eps =
        (Finset.range m).sum
          (fun i => Sign3.sgn (eps i) + ((m : Int) + 1) * (Sign3.sgn (eps i) * (i : Int))) := by
      simp only [localValue, cell, Nat.cast_add, Nat.cast_one, Nat.cast_mul]
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ = localGrade m eps + ((m : Int) + 1) * localIndex m eps := by
      simp [localGrade, localIndex, Finset.sum_add_distrib, Finset.mul_sum]

theorem localGrade_le (m : Nat) (eps : Nat → Sign3) :
    localGrade m eps ≤ (m : Int) := by
  calc
    localGrade m eps ≤ (Finset.range m).sum (fun _ => (1 : Int)) := by
      dsimp [localGrade]
      apply Finset.sum_le_sum
      intro i _hi
      cases eps i <;> norm_num [Sign3.sgn]
    _ = (m : Int) := by simp

theorem neg_le_localGrade (m : Nat) (eps : Nat → Sign3) :
    -((m : Int)) ≤ localGrade m eps := by
  calc
    -((m : Int)) = (Finset.range m).sum (fun _ => (-1 : Int)) := by simp
    _ ≤ localGrade m eps := by
      dsimp [localGrade]
      apply Finset.sum_le_sum
      intro i _hi
      cases eps i <;> norm_num [Sign3.sgn]

theorem defect_grade (m : Nat) (eps : Nat → Sign3) :
    (defectTotal m eps : Int) = (m : Int) - localGrade m eps := by
  calc
    (defectTotal m eps : Int) =
        (Finset.range m).sum (fun i => (Sign3.defect (eps i) : Int)) := by
      simp [defectTotal]
    _ = (Finset.range m).sum (fun i => (1 : Int) - Sign3.sgn (eps i)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      simp
    _ = (m : Int) - localGrade m eps := by
      simp [localGrade, Finset.sum_sub_distrib]

theorem sum_range_int_id_mul_two (m : Nat) :
    2 * ((Finset.range m).sum (fun i => (i : Int))) =
      (m : Int) * ((m : Int) - 1) := by
  cases m with
  | zero =>
      simp
  | succ n =>
      have hnat := Finset.sum_range_id_mul_two (n + 1)
      have hcast :
          ((((Finset.range (n + 1)).sum fun i => i) * 2 : Nat) : Int) =
            (((n + 1) * ((n + 1) - 1) : Nat) : Int) := by
        exact_mod_cast hnat
      simpa [Nat.cast_sum, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ n + 1),
        mul_comm, mul_left_comm, mul_assoc] using hcast

theorem doubled_index_defect (m : Nat) (eps : Nat → Sign3) :
    2 * localIndex m eps + 2 * (weightedDefectTotal m eps : Int) =
      (m : Int) * ((m : Int) - 1) := by
  have hsum : localIndex m eps + (weightedDefectTotal m eps : Int) =
      (Finset.range m).sum (fun i => (i : Int)) := by
    calc
      localIndex m eps + (weightedDefectTotal m eps : Int)
          = (Finset.range m).sum (fun i => Sign3.sgn (eps i) * (i : Int)) +
              (Finset.range m).sum (fun i => ((i * Sign3.defect (eps i) : Nat) : Int)) := by
              simp [localIndex, weightedDefectTotal]
      _ = (Finset.range m).sum (fun i => (i : Int)) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _hi
        simp [Nat.cast_mul]
        ring
  calc
    2 * localIndex m eps + 2 * (weightedDefectTotal m eps : Int)
        = 2 * (localIndex m eps + (weightedDefectTotal m eps : Int)) := by ring
    _ = 2 * ((Finset.range m).sum (fun i => (i : Int))) := by rw [hsum]
    _ = (m : Int) * ((m : Int) - 1) := sum_range_int_id_mul_two m

theorem weightedDefect_le (hm : 0 < m) (eps : Nat → Sign3) :
    weightedDefectTotal m eps ≤ (m - 1) * defectTotal m eps := by
  dsimp [weightedDefectTotal, defectTotal]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i ≤ m - 1 := by
    have : i < m := by simpa using hi
    omega
  exact Nat.mul_le_mul_right (Sign3.defect (eps i)) hi'

theorem localGrade_opp (m : Nat) (eps : Nat → Sign3) :
    localGrade m (fun i => Sign3.opp (eps i)) = -localGrade m eps := by
  simp [localGrade, Finset.sum_neg_distrib]

theorem localIndex_opp (m : Nat) (eps : Nat → Sign3) :
    localIndex m (fun i => Sign3.opp (eps i)) = -localIndex m eps := by
  simp [localIndex, Finset.sum_neg_distrib, neg_mul]

theorem localValue_opp (m : Nat) (eps : Nat → Sign3) :
    localValue m (fun i => Sign3.opp (eps i)) = -localValue m eps := by
  simp [localValue, Finset.sum_neg_distrib, neg_mul]

end AdmissibleCarry
