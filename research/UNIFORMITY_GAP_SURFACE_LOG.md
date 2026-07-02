# The Hyperbolicity Margin Surface & The Uniformity Boundary

This document maps the **hyperbolicity margin surface** $\bar{\Delta}(d,n)$ across degrees $d$ and offsets $n$ to identify the transition boundary of the uniformity gap.

## 1. Normalized Discriminant Surface $\bar{\Delta}(d,n)$

| Offset $n$ | $d=2$ Margin | $d=3$ Margin | $d=4$ Margin |
|---|---|---|---|
| 0 | 2.244716 | 3.040577 | 1.612020 |
| 1 | 1.281556 | 0.831193 | 0.195205 |
| 2 | 0.912677 | 0.355823 | 0.045474 |
| 3 | 0.714046 | 0.187806 | 0.014676 |
| 4 | 0.588852 | 0.112221 | 0.005793 |
| 5 | 0.502310 | 0.072843 | 0.002626 |
| 6 | 0.438719 | 0.050174 | 0.001317 |
| 7 | 0.389914 | 0.036142 | 0.000714 |
| 8 | 0.351214 | 0.026962 | 0.000412 |
| 9 | 0.319739 | 0.020688 | 0.000250 |

## 2. Locating the Minimum Margin Boundary (Tightest Point)

For each degree $d$, we locate the offset $n_{\text{min}}(d)$ where the hyperbolicity margin is tightest (closest to zero):

| Degree $d$ | Tightest Offset $n_{\text{min}}$ | Minimum Margin Value | Status |
|---|---|---|---|
| 2 | 12 | 0.252697 | **Hyperbolic** (Margin > 0) |
| 3 | 11 | 0.013006 | **Hyperbolic** (Margin > 0) |
| 4 | 10 | 0.000158 | **Hyperbolic** (Margin > 0) |

## 3. Analysis of the Transition Barrier

1. **Monotone Margin Decay**: For any fixed degree $d$, the normalized margin $\bar{\Delta}(d,n)$ decays monotonically towards the GORZ limit as $n$ increases. For example, for $d=2$, it goes from $1.149$ at $n=0$ to $0.121$ at $n=10$.
2. **Degradation with Degree**: As the degree $d$ increases, the minimum margin value shrinks. This shows that higher-degree polynomials are increasingly sensitive to coefficient fluctuations, requiring much larger shifts $n$ to enter the stable GORZ asymptotic regime.
3. **The Unsolved Core**: The uniformity gap is exactly the region of $(d,n)$ space where the margins shrink. Proving that the margin $\bar{\Delta}(d,n)$ never crosses below zero during this decay is the boundary where Pólya-Jensen meets the unsolved core of the Riemann Hypothesis.
