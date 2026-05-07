# A Lean Formalization of the Admissible-Carry Construction for Erdos Problem #875

This repository contains a Lean 4/mathlib formalization of the admissible-carry
construction for Erdos problem #875.

The final bundled theorem proves the existence of a concrete infinite
paper-admissible set of natural numbers, a strict increasing enumeration, the
normalized consecutive-gap limit

```text
(a (n + 1) - a n) / (n + 1)^(3 + 2 * sqrt 2) -> 0,
```

and the resulting eventual real gap bound.

## Trusted Statement

Read [`Challenge.lean`](Challenge.lean) first. It imports the source vocabulary
modules used in the public theorem statement and contains the comparator
target:

- `AdmissibleCarry.published_final_construction`

[`Solution.lean`](Solution.lean) imports the proved `AdmissibleCarry` library
and proves this public target from the final checked endpoint declarations.

## Proof Layout

The proof is organized as a finite/combinatorial core followed by an asymptotic
wrapper:

- [`AdmissibleCarry/Signs.lean`](AdmissibleCarry/Signs.lean)
- [`AdmissibleCarry/CoeffDiff.lean`](AdmissibleCarry/CoeffDiff.lean)
- [`AdmissibleCarry/LocalRange.lean`](AdmissibleCarry/LocalRange.lean)
- [`AdmissibleCarry/LocalCarry.lean`](AdmissibleCarry/LocalCarry.lean)
- [`AdmissibleCarry/Closure.lean`](AdmissibleCarry/Closure.lean)
- [`AdmissibleCarry/Stage.lean`](AdmissibleCarry/Stage.lean)
- [`AdmissibleCarry/Enumeration.lean`](AdmissibleCarry/Enumeration.lean)
- [`AdmissibleCarry/AsymptoticAbstract.lean`](AdmissibleCarry/AsymptoticAbstract.lean)
- [`AdmissibleCarry/ConcreteCeil.lean`](AdmissibleCarry/ConcreteCeil.lean)

The final endpoint is [`AdmissibleCarry.final_construction`](AdmissibleCarry/ConcreteCeil.lean).

## Checking

This project uses Lean `4.30.0-rc2` and mathlib, pinned by:

- [`lean-toolchain`](lean-toolchain)
- [`lakefile.toml`](lakefile.toml)
- [`lake-manifest.json`](lake-manifest.json)

To check the Lean proof:

```bash
lake exe cache get
lake build AdmissibleCarry
lake env lean Challenge.lean
lake env lean Solution.lean
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
successful comparator audit and tool versions used for this bundle.

Audit metadata:

- [Assumptions audit](ASSUMPTIONS.md)
- [Statement map](STATEMENT_MAP.md)
- [Version data](VERSION.txt)
- [Comparator/audit workflow](AUDIT.md)
- [Checksums](SHA256SUMS.txt)

## Reference Notes

The reference TeX files are explanatory source material, not trusted proof
artifacts:

- [`docs/reference/admissible_carry_note_lean_formalization_v10.tex`](docs/reference/admissible_carry_note_lean_formalization_v10.tex)
- [`docs/reference/admissible_carry_note_erdos875_new_version.tex`](docs/reference/admissible_carry_note_erdos875_new_version.tex)

## Notes

Generative AI tools assisted with development and drafting. The proof artifact
is the Lean code checked by Lake and, for statement matching, comparator.
