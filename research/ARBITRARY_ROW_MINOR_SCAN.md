# Arbitrary-Row Initial-Column Minor Scan

**Status:** falsification evidence only; not an RH proof.

- Coefficient cache: `research/figures/coeffs_M120.txt`
- Cache cross-precision metadata: `235.92527516266202`
- Decimal enclosure: half a unit in the last stored decimal place
- Maximum row scanned: `40`
- Columns: the initial interval `0, ..., k-1`

The interval signs are certified for the stored decimal enclosures. The
cross-precision metadata is provenance, not a formal interval proof of
the Cauchy extraction or of the Xi function itself.

| order | certified + | certified - | exact zero | inconclusive | tightest positive |
|---:|---:|---:|---:|---:|---|
| 3 | 8367 | 0 | 0 | 2293 | `rows=[34, 35, 36], lo=3.467762177670661E-312` |
| 4 | 72033 | 0 | 0 | 29237 | `rows=[32, 33, 34, 35], lo=9.169031201888276E-390` |

A certified negative count would falsify the corresponding discrete
PF target for the scanned row box and should stop that route. A zero
or inconclusive count is not evidence of failure.
