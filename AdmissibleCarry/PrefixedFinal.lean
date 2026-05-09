import AdmissibleCarry.PrefixedPointwise

/-!
# Bundled prefixed endpoint
-/

namespace AdmissibleCarry

noncomputable section

open Filter

namespace Prefixed

def prefFinalSet : Set Nat :=
  Set.range prefSeq

theorem prefFinalSet_infinite :
    prefFinalSet.Infinite := by
  simpa [prefFinalSet] using
    Set.infinite_range_of_injective prefSeq_strictMono.injective

theorem prefFinalSet_admissible :
    PaperAdmSet prefFinalSet := by
  classical
  intro U V hU hV hsum
  let a := prefSeq
  have hinj : Function.Injective a := prefSeq_strictMono.injective
  have hpreInjU : Set.InjOn a (a ⁻¹' (U : Set Nat)) := fun _ _ _ _ h => hinj h
  have hpreInjV : Set.InjOn a (a ⁻¹' (V : Set Nat)) := fun _ _ _ _ h => hinj h
  let Uidx := U.preimage a hpreInjU
  let Vidx := V.preimage a hpreInjV
  have hsumUidx : Uidx.sum a = U.sum (fun x : Nat => x) := by
    dsimp [Uidx]
    simpa using
      (Finset.sum_preimage a U hpreInjU (fun x : Nat => x) (by
        intro x hx hxrange
        exact (hxrange (by simpa [prefFinalSet, a] using hU x hx)).elim))
  have hsumVidx : Vidx.sum a = V.sum (fun x : Nat => x) := by
    dsimp [Vidx]
    simpa using
      (Finset.sum_preimage a V hpreInjV (fun x : Nat => x) (by
        intro x hx hxrange
        exact (hxrange (by simpa [prefFinalSet, a] using hV x hx)).elim))
  have hsumIdx : Uidx.sum a = Vidx.sum a := by
    rw [hsumUidx, hsumVidx]
    exact hsum
  have hcardIdx : Uidx.card = Vidx.card :=
    prefAdmSeq Uidx Vidx hsumIdx
  have hfilterU : {x ∈ U | x ∈ Set.range a} = U := by
    ext x
    constructor
    · intro hx
      exact (Finset.mem_filter.mp hx).1
    · intro hx
      exact Finset.mem_filter.mpr ⟨hx, by simpa [prefFinalSet, a] using hU x hx⟩
  have hfilterV : {x ∈ V | x ∈ Set.range a} = V := by
    ext x
    constructor
    · intro hx
      exact (Finset.mem_filter.mp hx).1
    · intro hx
      exact Finset.mem_filter.mpr ⟨hx, by simpa [prefFinalSet, a] using hV x hx⟩
  have hcardU : Uidx.card = U.card := by
    dsimp [Uidx]
    rw [Finset.card_preimage, hfilterU]
  have hcardV : Vidx.card = V.card := by
    dsimp [Vidx]
    rw [Finset.card_preimage, hfilterV]
  omega

theorem pref_final_construction :
    prefFinalSet.Infinite ∧
      PaperAdmSet prefFinalSet ∧
      StrictMono prefSeq ∧
      Filter.Tendsto
        (fun n : Nat =>
          ((prefSeq (n + 1) - prefSeq n : Nat) : ℝ) /
            ((n + 1 : Nat) : ℝ) ^ LegalSchedule.gapExponent)
        Filter.atTop (nhds 0) ∧
      (∀ n : Nat,
        ((prefSeq (n + 1) - prefSeq n : Nat) : ℝ) ≤
          ((n + 1 : Nat) : ℝ) ^ LegalSchedule.gapExponent) := by
  exact
    ⟨prefFinalSet_infinite, prefFinalSet_admissible, prefSeq_strictMono,
      pref_gap_tendsto, pref_all_gap_bound⟩

end Prefixed

end

end AdmissibleCarry
