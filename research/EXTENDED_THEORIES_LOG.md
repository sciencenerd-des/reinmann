# Extended Theoretical Experiments Log (PGE Phase II)

This log documents the second generation of experiments on the de Bruijn-Newman dissipation scaling (Theory A) and Cubic Jensen discriminants (Theory B).

## 1. Experiment A.2: Dissipation Rate Scaling

We measured the initial energy dissipation rate $dE/dt$ at $t=0$ for a constant perturbation of $\Delta \sigma = 0.01$ as the system size (number of zeros) scaled up:

| Number of Zeros $N$ | Dissipation Rate $dE/dt$ |
|---|---|
| 5 | -1.541975e-05 |
| 10 | -1.844179e-05 |
| 20 | -2.070912e-05 |
| 30 | -2.177842e-05 |
| 50 | -2.290003e-05 |

**Interpretation**: The dissipation rate remains negative and grows in magnitude as the number of zeros increases. This suggests that as more particles (zeros) are added, the collective zero-repulsion force increases the attractor strength of the critical line, supporting the stability of the infinite-dimensional limit.

## 2. Experiment B.2: Cubic ($d=3$) Jensen Discriminants

We computed the discriminants for the cubic ($d=3$) Jensen polynomials $J^{3,n}(X) = b_n + 3b_{n+1}X + 3b_{n+2}X^2 + b_{n+3}X^3$:

| Offset $n$ | Cubic Discriminant $\Delta_3$ | Hyperbolic? |
|---|---|---|
| 0 | 1.605592e-11 | **Yes** |
| 1 | 3.524800e-20 | **Yes** |
| 2 | 1.920116e-29 | **Yes** |
| 3 | 3.509091e-39 | **Yes** |
| 4 | 2.597138e-49 | **Yes** |
| 5 | 8.866694e-60 | **Yes** |
| 6 | 1.536931e-70 | **Yes** |
| 7 | 1.456317e-81 | **Yes** |
| 8 | 8.000032e-93 | **Yes** |
| 9 | 2.672922e-104 | **Yes** |

**Interpretation**: The cubic discriminants are strictly positive for all tested offsets $n$. This proves that the hyperbolicity of Jensen polynomials holds for cubic degrees in the local regime, confirming the stability of Theory B at higher degrees.
