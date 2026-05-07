# Assumptions Audit

This file records the proof boundary for the published Lean artifact.

## Trusted Base

The checked proof is a Lean 4/mathlib development. Its trusted base is:

- Lean kernel `4.30.0-rc2`.
- The mathlib dependency pinned in `lake-manifest.json`.
- Standard Lean axioms permitted by `comparator.json`:
  `propext`, `Quot.sound`, and `Classical.choice`.

The proof library does not introduce project axioms, `unsafe` definitions,
`admit`, or unproved `sorry` placeholders.

## Statement/Proof Split

`Challenge.lean` is the trusted statement file for comparator. It imports only
`Mathlib`, states the public endpoint directly, and intentionally contains a
`sorry` proof for the theorem being checked.

`Solution.lean` imports the proved `AdmissibleCarry` library. Comparator checks
that the theorem proved in `Solution.lean` has the same statement as
`Challenge.lean`, uses only the permitted axioms above, and is accepted by the
Lean kernel.

The no-placeholder audit excludes `Challenge.lean` by design and checks the
proof library.

## External Mathematical Inputs

No external mathematical theorem is imported as a project axiom. The published
Lean route is self-contained apart from mathlib.

The TeX reference notes under `docs/reference/` are explanatory sources for the
formalization route. They are not part of the trusted proof artifact.

## Not Part Of The Checked Proof

README text, planning notes, reference TeX files, bibliographic context, and
informal discussion are explanatory. The checked artifact is the Lean code plus
the comparator statement/proof comparison.

## Audit Commands

The proof-library placeholder audit is:

```bash
scripts/audit_sorries.sh .
tools/check_no_sorry.sh
```

The standard Lean build is:

```bash
lake build AdmissibleCarry
lake env lean Challenge.lean
lake env lean Solution.lean
```

The statement/proof comparison is:

```bash
lake env comparator comparator.json
```
