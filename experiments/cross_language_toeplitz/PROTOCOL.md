# Cross-language Toeplitz-minor experiment protocol

## Research question

For the repository's stored decimal enclosures of the first 121 signed Xi
coefficients, do any order-3 or order-4 arbitrary-row, initial-column Toeplitz
minors have a certified negative sign in a bounded row box? The original
baseline is `0..30`; the same protocol is rerun at `0..48` as an extended scan.

This is a bounded falsification question. A negative interval would refute the
corresponding positivity target on the stored coefficient box. Absence of a
negative interval does not prove the infinite target or RH.

## Pre-specified design

- Input: `research/figures/coeffs_M120.txt`, hashed byte-for-byte with SHA-256.
- Rows: every strictly increasing row selection from the declared maximum row
  (baseline `0..30`; extended run `0..48`).
- Columns: `0, ..., k-1` for `k = 3, 4`.
- Uncertainty model: each stored decimal is enclosed by half a unit in its last
  displayed decimal place.
- Python reference: exact common-scale integer interval arithmetic and a
  Leibniz determinant; the scale conversion is exact and avoids floating point.
- TypeScript replication: exact `BigInt` interval arithmetic after conversion
  to one common denominator, with an independently written Leibniz determinant.
- JavaScript replication: exact midpoint `BigInt` arithmetic with a
  fraction-free Bareiss determinant. This implementation is not an interval
  certificate; it is an algorithmically independent differential check.

## Controls and failure rules

Every implementation must classify the following order-3 determinants:

- `(1, 2, 5, 13, 33)` as positive;
- `(1, 2, 4, 8, 16)` as zero;
- `(1, 1, 2, 6, 24)` as negative.

The Python regression suite and both Node implementations also check a
scientific-notation token with a known scaled integer value. This specifically
guards the exponent-sensitive half-ULP model used by the coefficient cache.

The experiment fails if any control fails, input hashes differ, Python and
TypeScript interval counts or sign-stream hashes differ, or a JavaScript
midpoint sign differs from a certified Python/TypeScript sign. Certified
negative Xi intervals are reported as falsifiers; intervals containing zero
are reported as inconclusive, not negative.

## Reproduction

```sh
bash scripts/run_cross_language_toeplitz.sh
```

The runner uses only Python's standard library, Node.js built-ins, and the
installed TypeScript compiler. It writes machine-readable outputs and a short
report under `research/cross_language_toeplitz/`.
