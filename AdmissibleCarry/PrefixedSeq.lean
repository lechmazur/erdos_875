import AdmissibleCarry.PrefixedStage

/-!
# The prefixed sequence

The final enumeration is `1, 2` followed by four times the ordinary enumeration
of the shifted tail schedule.
-/

namespace AdmissibleCarry

noncomputable section

namespace Prefixed

def prefSeq : Nat → Nat
  | 0 => 1
  | 1 => 2
  | n + 2 => 4 * S.seq n

@[simp] theorem prefSeq_zero : prefSeq 0 = 1 := rfl

@[simp] theorem prefSeq_one : prefSeq 1 = 2 := rfl

theorem tail_seq_zero : S.seq 0 = 1 := by
  have hk : 0 < S.k 0 := S.k_pos 0
  have h := S.exact_block_formula (j := 0) (i := 0) hk
  simpa [LegalSchedule.N, LegalSchedule.elem, LegalSchedule.M, cell] using h

theorem prefSeq_two : prefSeq 2 = 4 := by
  simp [prefSeq, tail_seq_zero]

theorem prefSeq_tail (m : Nat) :
    prefSeq (m + 2) = 4 * S.seq m := by
  rfl

theorem prefSeq_strictMono : StrictMono prefSeq := by
  refine strictMono_nat_of_lt_succ ?_
  intro n
  cases n with
  | zero =>
      norm_num [prefSeq]
  | succ n1 =>
      cases n1 with
      | zero =>
          norm_num [prefSeq_two]
      | succ m =>
          have h := S.seq_lt_succ m
          simpa [prefSeq, Nat.add_assoc] using
            Nat.mul_lt_mul_of_pos_left h (by norm_num : 0 < 4)

theorem pref_gap_zero : prefSeq 1 - prefSeq 0 = 1 := by
  norm_num [prefSeq]

theorem pref_gap_one : prefSeq 2 - prefSeq 1 = 2 := by
  norm_num [prefSeq_two]

theorem pref_tail_gap (m : Nat) :
    prefSeq (m + 3) - prefSeq (m + 2) = 4 * S.GapAt m := by
  have hgap := S.uniform_gap_at m
  calc
    prefSeq (m + 3) - prefSeq (m + 2)
        = 4 * S.seq (m + 1) - 4 * S.seq m := by
          rfl
    _ = 4 * (S.seq (m + 1) - S.seq m) := by
          rw [← Nat.mul_sub_left_distrib]
    _ = 4 * S.GapAt m := by
          rw [hgap]

def scale4 (x : Nat) : Nat :=
  4 * x

theorem image_scale4_block (j : Nat) :
    (block (S.M j) (S.k j)).image scale4 = block (prefM j) (S.k j) := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨c, hc, rfl⟩
    refine Finset.mem_image.mpr ⟨c, hc, ?_⟩
    simp [scale4, prefM]
    ring
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨c, hc, rfl⟩
    refine Finset.mem_image.mpr ⟨S.M j * c, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨c, hc, rfl⟩
    · simp [scale4, prefM]
      ring

theorem prefF_eq_prefix_union_scaled_tail (j : Nat) :
    prefF j = prefPrefix ∪ ((S.F j).image scale4) := by
  induction j with
  | zero =>
      simp [prefF, prefPrefix, LegalSchedule.F]
  | succ j ih =>
      simp [prefF, LegalSchedule.F, stepSet, ih, image_scale4_block, Finset.image_union,
        Finset.union_assoc]

theorem pref_range_image_eq (j : Nat) :
    (Finset.range (prefN j)).image prefSeq =
      prefPrefix ∪ ((S.F j).image scale4) := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨n, hn, rfl⟩
    have hnlt : n < prefN j := by simpa using hn
    cases n with
    | zero =>
        exact Finset.mem_union_left _ (by simp [prefPrefix])
    | succ n1 =>
        cases n1 with
        | zero =>
            exact Finset.mem_union_left _ (by simp [prefPrefix])
        | succ m =>
            have hm : m < S.N j := by
              dsimp [prefN] at hnlt
              omega
            have hseq_mem : S.seq m ∈ S.F j := by
              rw [S.prefix_range j]
              exact Finset.mem_image.mpr ⟨m, by simpa using hm, rfl⟩
            exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨S.seq m, hseq_mem, rfl⟩)
  · intro hx
    rcases Finset.mem_union.mp hx with hxprefix | hxtail
    · have hxprefix' : x = 1 ∨ x = 2 := by
        simpa [prefPrefix] using hxprefix
      rcases hxprefix' with rfl | rfl
      · exact Finset.mem_image.mpr ⟨0, by simp [prefN], by simp [prefSeq]⟩
      · exact Finset.mem_image.mpr ⟨1, by simp [prefN]; omega, by simp [prefSeq]⟩
    · rcases Finset.mem_image.mp hxtail with ⟨y, hy, rfl⟩
      have hy' : y ∈ (Finset.range (S.N j)).image S.seq := by
        simpa [S.prefix_range j] using hy
      rcases Finset.mem_image.mp hy' with ⟨m, hm, rfl⟩
      refine Finset.mem_image.mpr ⟨m + 2, ?_, ?_⟩
      · have hmlt : m < S.N j := by simpa using hm
        simp [prefN]
        omega
      · simp [prefSeq, scale4]

theorem pref_prefix_range (j : Nat) :
    prefF j = (Finset.range (prefN j)).image prefSeq := by
  rw [prefF_eq_prefix_union_scaled_tail, pref_range_image_eq]

theorem prefAdmSeq : AdmSeq prefSeq := by
  intro U V hsum
  let J := (U ∪ V).sum (fun x : Nat => x) + 1
  have hprefix := pref_prefix_range J
  have hinj : Function.Injective prefSeq := prefSeq_strictMono.injective
  have hinjU : Set.InjOn prefSeq (U : Set Nat) := fun _ _ _ _ h => hinj h
  have hinjV : Set.InjOn prefSeq (V : Set Nat) := fun _ _ _ _ h => hinj h
  have hindex_lt {n : Nat} (hn : n ∈ U ∪ V) : n < prefN J := by
    have hsum_erase := Finset.add_sum_erase (U ∪ V) (fun x : Nat => x) hn
    have hsum_erase' :
        n + ((U ∪ V).erase n).sum (fun x : Nat => x) =
          (U ∪ V).sum (fun x : Nat => x) := by
      simpa using hsum_erase
    have hn_le : n ≤ (U ∪ V).sum (fun x : Nat => x) := by omega
    have hN := S.two_mul_le_N J
    have hn_lt_twoJ : n < 2 * J := by
      dsimp [J]
      omega
    dsimp [prefN]
    omega
  have hUsub : ∀ n, n ∈ U.image prefSeq → n ∈ prefF J := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨i, hi, rfl⟩
    rw [hprefix]
    exact Finset.mem_image.mpr
      ⟨i, by simpa using hindex_lt (Finset.mem_union_left V hi), rfl⟩
  have hVsub : ∀ n, n ∈ V.image prefSeq → n ∈ prefF J := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨i, hi, rfl⟩
    rw [hprefix]
    exact Finset.mem_image.mpr
      ⟨i, by simpa using hindex_lt (Finset.mem_union_right U hi), rfl⟩
  have hsumUimg :
      (U.image prefSeq).sum (fun x : Nat => x) = U.sum prefSeq := by
    simpa using
      (Finset.sum_image (s := U) (g := prefSeq) (f := fun x : Nat => x) hinjU)
  have hsumVimg :
      (V.image prefSeq).sum (fun x : Nat => x) = V.sum prefSeq := by
    simpa using
      (Finset.sum_image (s := V) (g := prefSeq) (f := fun x : Nat => x) hinjV)
  have hsumImg :
      (U.image prefSeq).sum (fun x : Nat => x) =
        (V.image prefSeq).sum (fun x : Nat => x) := by
    rw [hsumUimg, hsumVimg]
    exact hsum
  have hcardImg :
      (U.image prefSeq).card = (V.image prefSeq).card :=
    AdmFin.card_eq_of_sum_eq (prefStage_admissible J) hUsub hVsub hsumImg
  have hcardU : (U.image prefSeq).card = U.card := Finset.card_image_of_injOn hinjU
  have hcardV : (V.image prefSeq).card = V.card := Finset.card_image_of_injOn hinjV
  omega

end Prefixed

end

end AdmissibleCarry
