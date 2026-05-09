# Master Plan

Status: M0-M9 are complete for the admissible-carry route and prefixed
all-index publication endpoint.

## M0 Project Skeleton

Set up `AdmissibleCarry` with the same Lean/mathlib conventions as
`/home/lech/erdos_1032` and `/home/lech/erdos_1194`.

## M1 Finite Definitions

Implement and prove the basic `Sign3`, `CoeffOn`, `Diff`, local range block, and
finite model facts.

## M2 Local Range Contracts

Stabilize `C`, `Q`, `localGrade`, `localIndex`, `localValue`, `CDiff`, and the
bridge to global finite differences.

## M3 Local Carry

Prove the NatAbs firewall, two-sided local-carry theorem, and range wrapper.

## M4 Closure

Prove `closure_step` for adjoining `M • C_k`.

## M5 Stage Invariant

Prove every abstract stage satisfies `CarryState` and hence `AdmFin`.

## M6 Enumeration

Prove block-owner enumeration, exact block formula, and uniform gap formula.

## M7 Abstract Asymptotics

Prove the abstract little-oh wrapper from the analysis-ready record.

## M8 Concrete Ceiling Schedule

Instantiate the concrete schedule and prove the final Erdős 875 theorem.

## M9 Prefixed All-Index Endpoint

Define the shifted tail schedule, start from the prefix `{1, 2}` with modulus
`4`, transfer the tail enumeration through `prefSeq 0 = 1`,
`prefSeq 1 = 2`, `prefSeq (m + 2) = 4 * S.seq m`, and prove the bundled
endpoint `AdmissibleCarry.Prefixed.pref_final_construction` with a pointwise
gap bound for every zero-indexed `n`.  Expose this theorem through root
`Challenge.lean` and `Solution.lean`.
