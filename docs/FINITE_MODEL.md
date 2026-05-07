# Finite Model

The finite core uses:

- `Sign3` for coefficients in `{-1, 0, 1}`.
- `CoeffOn A` for signed differences supported on a finite set `A`.
- `Diff A t x` for cardinality-graded subset-sum differences.
- `CarryState A M sigma` for the cached invariant.
- `C k = {1 + i * (k + 1) | 0 ≤ i < k}` and `Q k = k^2 + k + 1`.

The core finite endpoint is `closure_step`, which adjoins `block M k = M • C k`
while preserving the carry invariant.
