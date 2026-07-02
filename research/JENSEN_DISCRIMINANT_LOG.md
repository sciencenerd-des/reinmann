# Jensen Polynomial Discriminant Analysis

This document logs the evaluation of discriminants for the Jensen polynomials $J^{d,n}(X)$ to verify the hyperbolicity margin of Theory B:
$$J^{2,n}(X) = b_n + 2b_{n+1}X + b_{n+2}X^2$$
$$\Delta(2,n) = 4(b_{n+1}^2 - b_n b_{n+2}) = 4(\mu_{n+1}^2 - \mu_n \mu_{n+2}) > 0$$

## 1. Discriminant Values for $d=2$

| Offset $n$ | Raw Discriminant $\Delta/4$ | Normalized Discriminant $(\mu_{n+1}^2/\mu_n\mu_{n+2}) - 1$ | Hyperbolic? |
|---|---|---|---|
| 0 | 7.055699e-05 | 1.149688 | **Yes** (Delta > 0) |
| 1 | 5.679989e-09 | 0.594115 | **Yes** (Delta > 0) |
| 2 | 1.999672e-13 | 0.405738 | **Yes** (Delta > 0) |
| 3 | 3.772144e-18 | 0.310063 | **Yes** (Delta > 0) |
| 4 | 4.297889e-23 | 0.251855 | **Yes** (Delta > 0) |
| 5 | 3.203116e-28 | 0.212569 | **Yes** (Delta > 0) |
| 6 | 1.653289e-33 | 0.184199 | **Yes** (Delta > 0) |
| 7 | 6.170073e-39 | 0.162712 | **Yes** (Delta > 0) |
| 8 | 1.722015e-44 | 0.145851 | **Yes** (Delta > 0) |
| 9 | 3.692963e-50 | 0.132253 | **Yes** (Delta > 0) |
| 10 | 6.223107e-56 | 0.121045 | **Yes** (Delta > 0) |

## 2. Asymptotic Bound and the GORZ Convergence

The normalized discriminant corresponds to $R_n - 1$, where $R_n$ is the Turán ratio. The Griffin-Ono-Rolen-Zagier (GORZ) asymptotics show that:
$$R_n - 1 \to 0 \quad \text{as} \quad n \to \infty$$
Specifically, the normalized coefficients of the Jensen polynomials converge to those of the Hermite polynomials, whose roots are simple and real.

### The Uniform Lower Bound Challenge
To prove RH, we must establish that the discriminant $\Delta(d,n) > 0$ for all $d$ and $n$:
1. **Local Regime ($n$ small)**: Verified here numerically to be positive with high margins.
2. **Asymptotic Regime ($n$ large)**: Guaranteed by the GORZ limit.
3. **Uniformity Gap**: The open mathematical challenge is to construct a continuous lower bound function $\mathcal{C}(d,n)$ such that $\Delta(d,n) \ge \mathcal{C}(d,n) > 0$ for all $n$ and $d$, ensuring that the local margins merge cleanly with the asymptotic regime without dipping below zero.
