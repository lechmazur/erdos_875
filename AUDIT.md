# Auditing This Lean Proof

The trusted statement is [`Challenge.lean`](Challenge.lean). It imports only
`Mathlib` and states the public comparator target directly, with the
paper-admissibility condition and exponent written inline:

- `AdmissibleCarry.published_final_construction`

The proof is the `AdmissibleCarry` library. [`Solution.lean`](Solution.lean)
imports that library and proves the public target from the checked concrete
endpoint declarations.

## Standard Lean Check

```bash
lake build AdmissibleCarry Challenge Solution
scripts/audit_sorries.sh .
tools/check_no_sorry.sh
scripts/audit_imports.sh .
```

`Challenge.lean` intentionally contains statement placeholders for comparator.
The no-sorry check is therefore scoped to the proof library, not the trusted
challenge file.

The source proof copied into this published bundle was validated in
`/home/lech/erdos_875` with:

```text
lake build AdmissibleCarry
scripts/audit_sorries.sh .
scripts/audit_imports.sh .
```

The published bundle itself was then validated with:

```text
lake build AdmissibleCarry Challenge Solution
scripts/audit_sorries.sh .
tools/check_no_sorry.sh
scripts/audit_imports.sh .
```

The no-placeholder and import audit commands completed successfully.

## Comparator Check

Comparator is an external Lean proof checker harness. It compares a trusted
challenge module against a solution module, checks permitted axioms, and replays
the solution through the Lean kernel.

Install `landrun`, `lean4export`, and `comparator` so their binaries are on
`PATH`. Use versions compatible with the pinned Lean toolchain
`leanprover/lean4:v4.30.0-rc2`; the corresponding tags are available for
`lean4export` and `comparator`.

Then run from the repository root:

```bash
lake env comparator comparator.json
```

This bundle was audited on 2026-05-07 with locally installed comparator tools:

```text
comparator v4.30.0-rc2, commit 95e46e658f5955ba1b01596d4ac668630476008c
lean4export v4.30.0-rc2, commit 12581a6b680d8478175596338eb2d53383a323e3
landrun v0.1.15
```

The successful comparator run ended with:

```text
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
```

See also:

- [`ASSUMPTIONS.md`](ASSUMPTIONS.md) for the proof boundary.
- [`STATEMENT_MAP.md`](STATEMENT_MAP.md) for the theorem map.
- [`VERSION.txt`](VERSION.txt) for toolchain and source metadata.
