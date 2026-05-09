# A Lean Formalization of the Admissible-Carry Construction for Erdos Problem #875

This repository contains a Lean 4/mathlib formalization of the admissible-carry
construction for Erdos problem #875.

The final bundled theorem proves the existence of a concrete infinite
paper-admissible set of natural numbers, a strict increasing enumeration, the
normalized consecutive-gap limit:

<p>
  <img src="docs/assets/readme-normalized-gap-limit-light.png#gh-light-mode-only" alt="The normalized consecutive-gap quotient tends to zero." width="420">
  <img src="docs/assets/readme-normalized-gap-limit-dark.png#gh-dark-mode-only" alt="The normalized consecutive-gap quotient tends to zero." width="420">
</p>

and the pointwise all-index real gap bound:

<p>
  <img src="docs/assets/readme-all-index-gap-bound-light.png#gh-light-mode-only" alt="The pointwise all-index real gap bound." width="680">
  <img src="docs/assets/readme-all-index-gap-bound-dark.png#gh-dark-mode-only" alt="The pointwise all-index real gap bound." width="680">
</p>

## Trusted Statement

Read [`Challenge.lean`](Challenge.lean) first. It imports only `Mathlib` and
contains the public comparator target:

- `AdmissibleCarry.published_final_construction`

[`Solution.lean`](Solution.lean) imports the proved `AdmissibleCarry` library
and proves this public target from the final checked endpoint declarations.

## Proof Layout

The proof is organized as a finite/combinatorial core, the original eventual
concrete schedule, and a prefixed all-index endpoint:

- [`AdmissibleCarry/Signs.lean`](AdmissibleCarry/Signs.lean)
- [`AdmissibleCarry/CoeffDiff.lean`](AdmissibleCarry/CoeffDiff.lean)
- [`AdmissibleCarry/LocalRange.lean`](AdmissibleCarry/LocalRange.lean)
- [`AdmissibleCarry/LocalCarry.lean`](AdmissibleCarry/LocalCarry.lean)
- [`AdmissibleCarry/Closure.lean`](AdmissibleCarry/Closure.lean)
- [`AdmissibleCarry/Stage.lean`](AdmissibleCarry/Stage.lean)
- [`AdmissibleCarry/Enumeration.lean`](AdmissibleCarry/Enumeration.lean)
- [`AdmissibleCarry/AsymptoticAbstract.lean`](AdmissibleCarry/AsymptoticAbstract.lean)
- [`AdmissibleCarry/ConcreteCeil.lean`](AdmissibleCarry/ConcreteCeil.lean)
- [`AdmissibleCarry/PrefixedTail.lean`](AdmissibleCarry/PrefixedTail.lean)
- [`AdmissibleCarry/PrefixedStage.lean`](AdmissibleCarry/PrefixedStage.lean)
- [`AdmissibleCarry/PrefixedSeq.lean`](AdmissibleCarry/PrefixedSeq.lean)
- [`AdmissibleCarry/PrefixedAsymptotic.lean`](AdmissibleCarry/PrefixedAsymptotic.lean)
- [`AdmissibleCarry/PrefixedPointwise.lean`](AdmissibleCarry/PrefixedPointwise.lean)
- [`AdmissibleCarry/PrefixedFinal.lean`](AdmissibleCarry/PrefixedFinal.lean)

The final all-index endpoint is
[`AdmissibleCarry.Prefixed.pref_final_construction`](AdmissibleCarry/PrefixedFinal.lean).

## Checking

This project uses Lean `4.30.0-rc2` and mathlib, pinned by:

- [`lean-toolchain`](lean-toolchain)
- [`lakefile.toml`](lakefile.toml)
- [`lake-manifest.json`](lake-manifest.json)

To check the Lean proof:

```bash
lake exe cache get
lake build AdmissibleCarry Challenge Solution
scripts/audit_sorries.sh .
tools/check_no_sorry.sh
scripts/audit_imports.sh .
```

`Challenge.lean` intentionally has statement placeholders for comparator. The
no-sorry check is scoped to the proof library.

For an independent statement/proof comparison, use
[`comparator.json`](comparator.json):

```bash
lake env comparator comparator.json
```

This requires `landrun`, `lean4export`, and `comparator` on `PATH`, with
versions compatible with Lean `v4.30.0-rc2`. See [`AUDIT.md`](AUDIT.md) for the
current audit status and comparator workflow.

Audit metadata:

- [Assumptions audit](ASSUMPTIONS.md)
- [Statement map](STATEMENT_MAP.md)
- [Version data](VERSION.txt)
- [Comparator/audit workflow](AUDIT.md)
- [Checksums](SHA256SUMS.txt)

## Reference Note

The reference note is explanatory source material, not a trusted proof artifact:

- [`docs/reference/admissible_carry_note_erdos875.pdf`](docs/reference/admissible_carry_note_erdos875.pdf)
- [`docs/reference/admissible_carry_note_erdos875.tex`](docs/reference/admissible_carry_note_erdos875.tex)

## Notes

Generative AI tools assisted with development and drafting. The proof artifact
is the Lean code checked by Lake, with `comparator.json` providing the
statement-matching harness when comparator tooling is installed.
