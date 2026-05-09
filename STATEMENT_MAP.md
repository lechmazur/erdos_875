# Statement Map

This map connects the final theorem content to the Lean declarations in the
published bundle.

| Content | Lean declaration | File | Status |
| --- | --- | --- | --- |
| Trusted comparator statement | `AdmissibleCarry.published_final_construction` | `Challenge.lean` | Imports only `Mathlib`; statement-only, intentionally uses `sorry` |
| Comparator solution module | `AdmissibleCarry.published_final_construction` | `Solution.lean` | Proved from the checked proof library; comparator target configured |
| Paper-admissible finite-subset wrapper | `AdmissibleCarry.PaperAdmSet` | `AdmissibleCarry/CoeffDiff.lean` | Defined |
| Abstract legal schedule | `AdmissibleCarry.LegalSchedule` | `AdmissibleCarry/Stage.lean` | Defined |
| Sequence-level admissibility | `AdmissibleCarry.LegalSchedule.admSeq` | `AdmissibleCarry/Enumeration.lean` | Proved |
| Abstract gap little-oh wrapper | `AdmissibleCarry.LegalSchedule.abstract_gap_little_o` | `AdmissibleCarry/AsymptoticAbstract.lean` | Proved |
| Concrete schedule | `AdmissibleCarry.concreteSchedule` | `AdmissibleCarry/ConcreteCeil.lean` | Defined |
| Infinite final set | `AdmissibleCarry.finalSet_infinite` | `AdmissibleCarry/ConcreteCeil.lean` | Proved |
| Public admissibility wrapper | `AdmissibleCarry.finalSet_admissible` | `AdmissibleCarry/ConcreteCeil.lean` | Proved |
| Original concrete normalized gap limit | `AdmissibleCarry.final_gap_tendsto` | `AdmissibleCarry/ConcreteCeil.lean` | Proved |
| Original eventual real gap bound | `AdmissibleCarry.final_gap_eventually_le_rpow` | `AdmissibleCarry/ConcreteCeil.lean` | Proved |
| Prefixed tail schedule | `AdmissibleCarry.Prefixed.tailSchedule` | `AdmissibleCarry/PrefixedTail.lean` | Defined and proved legal |
| Prefixed finite-stage carry invariant | `AdmissibleCarry.Prefixed.prefStage_invariant` | `AdmissibleCarry/PrefixedStage.lean` | Proved |
| Prefixed sequence admissibility | `AdmissibleCarry.Prefixed.prefAdmSeq` | `AdmissibleCarry/PrefixedSeq.lean` | Proved |
| Prefixed normalized gap limit | `AdmissibleCarry.Prefixed.pref_gap_tendsto` | `AdmissibleCarry/PrefixedAsymptotic.lean` | Proved |
| Prefixed all-index real gap bound | `AdmissibleCarry.Prefixed.pref_all_gap_bound` | `AdmissibleCarry/PrefixedPointwise.lean` | Proved |
| Bundled all-index endpoint | `AdmissibleCarry.Prefixed.pref_final_construction` | `AdmissibleCarry/PrefixedFinal.lean` | Proved |
| Published comparator endpoint | `AdmissibleCarry.published_final_construction` | `Solution.lean` | Proved from prefixed final endpoint declarations |

## Comparator Targets

The declaration listed in `comparator.json` is:

```text
AdmissibleCarry.published_final_construction
```

The comparator statement writes the paper-admissibility condition and exponent
directly. `Solution.lean` proves that statement from `PaperAdmSet` and
`LegalSchedule.gapExponent` by definitional unfolding.

## Scope Notes

The endpoint is a Lean-normalized version of the admissible-carry construction
for Erdos problem #875. The bundled theorem states an infinite paper-admissible
set, a strict increasing enumeration, the normalized consecutive-gap limit, and
the pointwise all-index real gap bound.

The theorem is zero-indexed in Lean. The denominator in the checked limit and
pointwise bound is `(n + 1) ^ (3 + 2 * sqrt 2)`, matching the zero-indexed
enumeration used by the formalization.  The all-index bound is proved for the
prefixed sequence `1, 2, 4 * S.seq 0, 4 * S.seq 1, ...`; it is not asserted for
the original unprefixed `concreteSchedule.seq`.
