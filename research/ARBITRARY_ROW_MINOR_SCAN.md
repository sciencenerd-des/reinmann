# Arbitrary-Row Initial-Column Minor Scan

**Status:** falsification evidence only; not an RH proof.

- Coefficient cache: `research/figures/coeffs_M120.txt`
- Cache cross-precision metadata: `235.92527516266202`
- Decimal enclosure: half a unit in the last stored decimal place
- Maximum row scanned: `48`
- Columns: the initial interval `0, ..., k-1`

The interval signs are certified for the stored decimal enclosures. The
cross-precision metadata is provenance, not a formal interval proof of
the Cauchy extraction or of the Xi function itself.

| order | certified + | certified - | exact zero | inconclusive | tightest positive |
|---:|---:|---:|---:|---:|---|
| 3 | 18424 | 0 | 0 | 0 | `rows=[46, 47, 48], lo=1.080011084146537E-443` |
| 4 | 211876 | 0 | 0 | 0 | `rows=[45, 46, 47, 48], lo=9.465570600920423E-579` |

A certified negative count would falsify the corresponding discrete
PF target for the scanned row box and should stop that route. A zero
or inconclusive count is not evidence of failure.
