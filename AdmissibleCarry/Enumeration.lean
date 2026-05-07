import AdmissibleCarry.Stage

/-!
# Increasing enumeration

Block-owner enumeration for the abstract construction.
-/

namespace AdmissibleCarry

namespace LegalSchedule

def elem (S : LegalSchedule) (j i : Nat) : Nat :=
  S.M j * cell (S.k j) i

theorem cell_succ (m i : Nat) :
    cell m (i + 1) = cell m i + (m + 1) := by
  simp [cell]
  ring

theorem elem_succ (S : LegalSchedule) (j i : Nat) :
    S.elem j (i + 1) = S.elem j i + S.M j * (S.k j + 1) := by
  calc
    S.elem j (i + 1) = S.M j * cell (S.k j) (i + 1) := rfl
    _ = S.M j * (cell (S.k j) i + (S.k j + 1)) := by rw [cell_succ]
    _ = S.elem j i + S.M j * (S.k j + 1) := by
      change S.M j * (cell (S.k j) i + (S.k j + 1)) =
        S.M j * cell (S.k j) i + S.M j * (S.k j + 1)
      ring

theorem cell_eq_square_of_succ_eq {m i : Nat} (hi : i < m) (hlast : i + 1 = m) :
    cell m i = m * m := by
  simp [cell]
  nlinarith

theorem elem_boundary_gap (S : LegalSchedule) {j i : Nat}
    (hi : i < S.k j) (hlast : i + 1 = S.k j) :
    S.elem (j + 1) 0 - S.elem j i = S.M j * (S.k j + 1) := by
  have hc : cell (S.k j) i = S.k j * S.k j :=
    cell_eq_square_of_succ_eq hi hlast
  have hleft : S.elem (j + 1) 0 = S.M j * Q (S.k j) := by
    simp only [elem, M, cell, zero_mul, add_zero, mul_one]
  have hcurrent : S.elem j i = S.M j * (S.k j * S.k j) := by
    simp only [elem]
    rw [hc]
  have hsum : S.elem (j + 1) 0 = S.elem j i + S.M j * (S.k j + 1) := by
    rw [hleft, hcurrent]
    simp only [Q]
    ring
  rw [hsum]
  simp

theorem two_mul_le_N (S : LegalSchedule) (j : Nat) :
    2 * j ≤ S.N j := by
  induction j with
  | zero =>
      simp [N]
  | succ j ih =>
      have hk : 2 ≤ S.k j := S.k_ge_two j
      simp [N]
      omega

theorem k_pos (S : LegalSchedule) (j : Nat) : 0 < S.k j :=
  lt_of_lt_of_le (by norm_num) (S.k_ge_two j)

theorem N_mono (S : LegalSchedule) : Monotone S.N := by
  intro a b h
  exact Nat.le_induction (show S.N a ≤ S.N a by rfl)
    (fun n _ ih => ih.trans (by simp [N])) b h

def owner (S : LegalSchedule) (n : Nat) : Nat :=
  Nat.find (p := fun j => n < S.N (j + 1)) (by
    refine ⟨n, ?_⟩
    have hN : 2 * (n + 1) ≤ S.N (n + 1) := S.two_mul_le_N (n + 1)
    omega)

theorem owner_spec (S : LegalSchedule) (n : Nat) :
    n < S.N (S.owner n + 1) := by
  exact Nat.find_spec (p := fun j => n < S.N (j + 1)) _

theorem owner_min (S : LegalSchedule) {n j : Nat} (hj : j < S.owner n) :
    S.N (j + 1) ≤ n := by
  exact Nat.le_of_not_gt (Nat.find_min (p := fun j => n < S.N (j + 1)) _ hj)

theorem owner_lower (S : LegalSchedule) (n : Nat) :
    S.N (S.owner n) ≤ n := by
  cases howner : S.owner n with
  | zero =>
      simp [N]
  | succ j =>
      have hj : j < S.owner n := by
        rw [howner]
        omega
      simpa [howner] using S.owner_min hj

theorem owner_eq_of_lt (S : LegalSchedule) {j i : Nat} (hi : i < S.k j) :
    S.owner (S.N j + i) = j := by
  rw [owner, Nat.find_eq_iff]
  constructor
  · simp [N]
    omega
  · intro l hlj hbad
    have hle : S.N (l + 1) ≤ S.N j := S.N_mono (by omega)
    omega

def offset (S : LegalSchedule) (n : Nat) : Nat :=
  n - S.N (S.owner n)

theorem offset_eq_of_lt (S : LegalSchedule) {j i : Nat} (hi : i < S.k j) :
    S.offset (S.N j + i) = i := by
  simp [offset, owner_eq_of_lt S hi]

theorem offset_lt (S : LegalSchedule) (n : Nat) :
    S.offset n < S.k (S.owner n) := by
  have hlower : S.N (S.owner n) ≤ n := S.owner_lower n
  have hupper : n < S.N (S.owner n) + S.k (S.owner n) := by
    simpa [N] using S.owner_spec n
  simp [offset]
  omega

noncomputable def seq (S : LegalSchedule) (n : Nat) : Nat :=
  elem S (S.owner n) (S.offset n)

def GapAt (S : LegalSchedule) (n : Nat) : Nat :=
  S.M (S.owner n) * (S.k (S.owner n) + 1)

theorem exact_block_formula (S : LegalSchedule) {j i : Nat} (hi : i < S.k j) :
    S.seq (S.N j + i) = S.elem j i := by
  simp [seq, owner_eq_of_lt S hi, offset_eq_of_lt S hi]

theorem uniform_gap (S : LegalSchedule) {j i : Nat} (hi : i < S.k j) :
    S.seq (S.N j + i + 1) - S.seq (S.N j + i) =
      S.M j * (S.k j + 1) := by
  have hle : i + 1 ≤ S.k j := Nat.succ_le_of_lt hi
  rcases lt_or_eq_of_le hle with hnext | hlast
  · have hidx : S.N j + i + 1 = S.N j + (i + 1) := by omega
    rw [hidx, exact_block_formula S hnext, exact_block_formula S hi]
    rw [elem_succ]
    simp
  · have hidx : S.N j + i + 1 = S.N (j + 1) + 0 := by
      simp [N]
      omega
    rw [hidx, exact_block_formula S (S.k_pos (j + 1)), exact_block_formula S hi]
    exact elem_boundary_gap S hi hlast

theorem uniform_gap_at (S : LegalSchedule) (n : Nat) :
    S.seq (n + 1) - S.seq n = S.GapAt n := by
  let j := S.owner n
  let i := S.offset n
  have hi : i < S.k j := by
    simpa [j, i] using S.offset_lt n
  have hbase : S.N j + i = n := by
    have hlower : S.N (S.owner n) ≤ n := S.owner_lower n
    simp [j, i, offset]
    omega
  have hgap := S.uniform_gap (j := j) (i := i) hi
  rw [hbase] at hgap
  simpa [GapAt, j] using hgap

theorem GapAt_pos (S : LegalSchedule) (n : Nat) :
    0 < S.GapAt n := by
  exact Nat.mul_pos (S.M_pos (S.owner n)) (Nat.succ_pos (S.k (S.owner n)))

theorem seq_lt_succ (S : LegalSchedule) (n : Nat) :
    S.seq n < S.seq (n + 1) := by
  have hgap := S.uniform_gap_at n
  have hpos := S.GapAt_pos n
  by_contra hnot
  have hle : S.seq (n + 1) ≤ S.seq n := Nat.le_of_not_gt hnot
  have hsub : S.seq (n + 1) - S.seq n = 0 := Nat.sub_eq_zero_of_le hle
  rw [hsub] at hgap
  omega

theorem strictMono_seq (S : LegalSchedule) :
    StrictMono S.seq := by
  exact strictMono_nat_of_lt_succ (S.seq_lt_succ)

theorem prefix_range (S : LegalSchedule) (j : Nat) :
    S.F j = (Finset.range (S.N j)).image S.seq := by
  induction j with
  | zero =>
      simp [F, N]
  | succ j ih =>
      ext x
      constructor
      · intro hx
        have hx' : x ∈ stepSet (S.F j) (S.M j) (S.k j) := by
          simpa [F] using hx
        rcases Finset.mem_union.mp hx' with hxold | hxblock
        · have hximg : x ∈ (Finset.range (S.N j)).image S.seq := by
            simpa [ih] using hxold
          rcases Finset.mem_image.mp hximg with ⟨n, hn, rfl⟩
          refine Finset.mem_image.mpr ⟨n, ?_, rfl⟩
          have hnlt : n < S.N j := by simpa using hn
          simp [N]
          omega
        · rcases Finset.mem_image.mp hxblock with ⟨c, hc, rfl⟩
          rcases Finset.mem_image.mp hc with ⟨i, hi, rfl⟩
          have hi' : i < S.k j := by simpa using hi
          refine Finset.mem_image.mpr ⟨S.N j + i, ?_, ?_⟩
          · simp [N]
            omega
          · simpa [elem] using (S.exact_block_formula (j := j) (i := i) hi')
      · intro hx
        rcases Finset.mem_image.mp hx with ⟨n, hn, rfl⟩
        have hnlt : n < S.N (j + 1) := by simpa using hn
        by_cases hOld : n < S.N j
        · have hxold : S.seq n ∈ S.F j := by
            have hximg : S.seq n ∈ (Finset.range (S.N j)).image S.seq :=
              Finset.mem_image.mpr ⟨n, by simpa using hOld, rfl⟩
            simpa [ih] using hximg
          have hxstep : S.seq n ∈ stepSet (S.F j) (S.M j) (S.k j) :=
            Finset.mem_union_left _ hxold
          simpa [F] using hxstep
        · have hNj_le : S.N j ≤ n := Nat.le_of_not_gt hOld
          let i := n - S.N j
          have hi : i < S.k j := by
            have hnupper : n < S.N j + S.k j := by
              simpa [N] using hnlt
            dsimp [i]
            omega
          have hn_eq : S.N j + i = n := by
            dsimp [i]
            omega
          have hxblock : S.seq n ∈ block (S.M j) (S.k j) := by
            rw [← hn_eq]
            rw [S.exact_block_formula (j := j) (i := i) hi]
            dsimp [elem, block, C]
            refine Finset.mem_image.mpr ⟨cell (S.k j) i, ?_, rfl⟩
            exact Finset.mem_image.mpr ⟨i, by simpa using hi, rfl⟩
          have hxstep : S.seq n ∈ stepSet (S.F j) (S.M j) (S.k j) :=
            Finset.mem_union_right _ hxblock
          simpa [F] using hxstep

theorem admSeq (S : LegalSchedule) :
    AdmSeq S.seq := by
  intro U V hsum
  let J := (U ∪ V).sum (fun x : Nat => x) + 1
  have hprefix := S.prefix_range J
  have hinj : Function.Injective S.seq := S.strictMono_seq.injective
  have hinjU : Set.InjOn S.seq (U : Set Nat) := fun _ _ _ _ h => hinj h
  have hinjV : Set.InjOn S.seq (V : Set Nat) := fun _ _ _ _ h => hinj h
  have hindex_lt {n : Nat} (hn : n ∈ U ∪ V) : n < S.N J := by
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
    exact lt_of_lt_of_le hn_lt_twoJ hN
  have hUsub : ∀ n, n ∈ U.image S.seq → n ∈ S.F J := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨i, hi, rfl⟩
    rw [hprefix]
    exact Finset.mem_image.mpr
      ⟨i, by simpa using hindex_lt (Finset.mem_union_left V hi), rfl⟩
  have hVsub : ∀ n, n ∈ V.image S.seq → n ∈ S.F J := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨i, hi, rfl⟩
    rw [hprefix]
    exact Finset.mem_image.mpr
      ⟨i, by simpa using hindex_lt (Finset.mem_union_right U hi), rfl⟩
  have hsumUimg :
      (U.image S.seq).sum (fun x : Nat => x) = U.sum S.seq := by
    simpa using
      (Finset.sum_image (s := U) (g := S.seq) (f := fun x : Nat => x) hinjU)
  have hsumVimg :
      (V.image S.seq).sum (fun x : Nat => x) = V.sum S.seq := by
    simpa using
      (Finset.sum_image (s := V) (g := S.seq) (f := fun x : Nat => x) hinjV)
  have hsumImg :
      (U.image S.seq).sum (fun x : Nat => x) =
        (V.image S.seq).sum (fun x : Nat => x) := by
    rw [hsumUimg, hsumVimg]
    exact hsum
  have hcardImg :
      (U.image S.seq).card = (V.image S.seq).card :=
    AdmFin.card_eq_of_sum_eq (S.stage_admissible J) hUsub hVsub hsumImg
  have hcardU : (U.image S.seq).card = U.card := Finset.card_image_of_injOn hinjU
  have hcardV : (V.image S.seq).card = V.card := Finset.card_image_of_injOn hinjV
  omega

end LegalSchedule

end AdmissibleCarry
