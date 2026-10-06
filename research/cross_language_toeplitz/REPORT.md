# Cross-Language Toeplitz-Minor Replication

**Status:** bounded falsification evidence only; not an RH proof.

- Differential check: **passed**
- Input SHA-256: `b35913c17dca981359ea8cce5e5e5af5aae3d0a82da4714ca3880d37a6d9fd44`
- Row box: `0..30`
- Controls: positive, geometric-zero, and negative determinants all classified as expected

| order | selections | certified + | certified - | zero | inconclusive | JS midpoint + |
|---:|---:|---:|---:|---:|---:|---:|
| 3 | 4495 | 4495 | 0 | 0 | 0 | 4495 |
| 4 | 31465 | 31465 | 0 | 0 | 0 | 31465 |

Python and TypeScript used exact interval arithmetic but independent implementations;
JavaScript used an exact midpoint Bareiss determinant as an algorithmically distinct
differential check. Agreement rules were specified before examining these outputs.

No certified negative in this finite box means only that the tested data did not
falsify the order-3 or order-4 target. It does not certify the upstream Xi coefficient
extraction, any untested row, any higher order, total positivity, or RH.
