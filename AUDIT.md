# Auditing This Lean Proof

The trusted statement is [`Challenge.lean`](Challenge.lean). It imports only
`Mathlib` and states the public comparator target directly, with the
paper-admissibility condition, exponent, normalized gap limit, and pointwise
all-index gap bound written inline:

- `AdmissibleCarry.published_final_construction`

The proof is the `AdmissibleCarry` library. [`Solution.lean`](Solution.lean)
imports that library and proves the public target from the checked prefixed
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

The prefixed source proof copied into this published bundle was validated in
`/home/lech/erdos_875` at source commit `340ac57` with:

```text
lake build AdmissibleCarry
scripts/audit_sorries.sh .
scripts/audit_imports.sh .
lake env lean Challenge.lean
lake env lean Solution.lean
```

The published bundle itself was then validated with:

```text
lake build AdmissibleCarry Challenge Solution
scripts/audit_sorries.sh .
tools/check_no_sorry.sh
scripts/audit_imports.sh .
```

The no-placeholder and import audit commands completed successfully.

For this 2026-05-09 refresh, this local machine did not have `comparator`,
`lean4export`, or `landrun` on `PATH`.  The comparator target remains set up in
`comparator.json`; run `lake env comparator comparator.json` on a machine with
those binaries installed before calling this refresh comparator-audited.

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

The previous eventual-bound bundle was audited on 2026-05-07 with locally
installed comparator tools:

```text
comparator v4.30.0-rc2, commit 95e46e658f5955ba1b01596d4ac668630476008c
lean4export v4.30.0-rc2, commit 12581a6b680d8478175596338eb2d53383a323e3
landrun v0.1.15
```

That successful comparator run ended with:

```text
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
```

See also:

- [`ASSUMPTIONS.md`](ASSUMPTIONS.md) for the proof boundary.
- [`STATEMENT_MAP.md`](STATEMENT_MAP.md) for the theorem map.
- [`VERSION.txt`](VERSION.txt) for toolchain and source metadata.
