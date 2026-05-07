# Statement Map

This map connects the final theorem content to the Lean declarations in the
published bundle.

| Content | Lean declaration | File | Status |
| --- | --- | --- | --- |
| Trusted comparator statement | `AdmissibleCarry.published_final_construction` | `Challenge.lean` | Imports only `Mathlib`; statement-only, intentionally uses `sorry` |
| Comparator solution module | `AdmissibleCarry.published_final_construction` | `Solution.lean` | Proved from the checked proof library and accepted by comparator |
| Paper-admissible finite-subset wrapper | `AdmissibleCarry.PaperAdmSet` | `AdmissibleCarry/CoeffDiff.lean` | Defined |
| Abstract legal schedule | `AdmissibleCarry.LegalSchedule` | `AdmissibleCarry/Stage.lean` | Defined |
| Sequence-level admissibility | `AdmissibleCarry.LegalSchedule.admSeq` | `AdmissibleCarry/Enumeration.lean` | Proved |
| Abstract gap little-oh wrapper | `AdmissibleCarry.LegalSchedule.abstract_gap_little_o` | `AdmissibleCarry/AsymptoticAbstract.lean` | Proved |
| Concrete schedule | `AdmissibleCarry.concreteSchedule` | `AdmissibleCarry/ConcreteCeil.lean` | Defined |
| Infinite final set | `AdmissibleCarry.finalSet_infinite` | `AdmissibleCarry/ConcreteCeil.lean` | Proved |
| Public admissibility wrapper | `AdmissibleCarry.finalSet_admissible` | `AdmissibleCarry/ConcreteCeil.lean` | Proved |
| Concrete normalized gap limit | `AdmissibleCarry.final_gap_tendsto` | `AdmissibleCarry/ConcreteCeil.lean` | Proved |
| Eventual real gap bound | `AdmissibleCarry.final_gap_eventually_le_rpow` | `AdmissibleCarry/ConcreteCeil.lean` | Proved |
| Bundled final endpoint | `AdmissibleCarry.final_construction` | `AdmissibleCarry/ConcreteCeil.lean` | Proved |
| Published comparator endpoint | `AdmissibleCarry.published_final_construction` | `Solution.lean` | Proved from final endpoint declarations |

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
the eventual real gap bound.

The theorem is zero-indexed in Lean. The denominator in the checked limit and
eventual bound is `(n + 1) ^ (3 + 2 * sqrt 2)`, matching the zero-indexed
enumeration used by the formalization.
