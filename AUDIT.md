# Auditing This Lean Proof

The trusted statement is [`Challenge.lean`](Challenge.lean). It imports only
`Mathlib`, defines the public vocabulary used in the theorem statements, and
states the five comparator targets:

- `AdmissibleCarry.finalSet_infinite`
- `AdmissibleCarry.finalSet_admissible`
- `AdmissibleCarry.final_gap_tendsto`
- `AdmissibleCarry.final_gap_eventually_le_rpow`
- `AdmissibleCarry.final_construction`

The proof is the `AdmissibleCarry` library. [`Solution.lean`](Solution.lean)
imports that library so comparator can verify that the proved declarations
match the trusted statements in `Challenge.lean`.

## Standard Lean Check

```bash
lake build AdmissibleCarry
lake env lean Challenge.lean
lake env lean Solution.lean
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
diff -qr /home/lech/erdos_875/AdmissibleCarry /mnt/r/published/erdos_875/AdmissibleCarry
diff -q /home/lech/erdos_875/AdmissibleCarry.lean /mnt/r/published/erdos_875/AdmissibleCarry.lean
diff -q /home/lech/erdos_875/lakefile.toml /mnt/r/published/erdos_875/lakefile.toml
diff -q /home/lech/erdos_875/lean-toolchain /mnt/r/published/erdos_875/lean-toolchain
diff -q /home/lech/erdos_875/lake-manifest.json /mnt/r/published/erdos_875/lake-manifest.json
scripts/audit_sorries.sh .
tools/check_no_sorry.sh
scripts/audit_imports.sh .
lean Challenge.lean
lean Solution.lean
lean AdmissibleCarry.lean
lean AdmissibleCarry/ConcreteCeil.lean
```

For the direct `lean` checks above, `LEAN_PATH` was pointed at the already-built
dependency artifacts from `/home/lech/erdos_875`, with the published bundle's
own `.lake/build/lib/lean` replacing the source project build path. This avoids
rebuilding all of mathlib on the mounted publication directory while still
checking the published wrapper files and top-level proof modules.

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

The comparator configuration is included in this bundle. Comparator binaries
were not available in the local environment used to create this publication
bundle, so the recorded local audit is the source Lean build, the direct Lean
wrapper checks, and the no-placeholder/import audits above.

See also:

- [`ASSUMPTIONS.md`](ASSUMPTIONS.md) for the proof boundary.
- [`STATEMENT_MAP.md`](STATEMENT_MAP.md) for the theorem map.
- [`VERSION.txt`](VERSION.txt) for toolchain and source metadata.
