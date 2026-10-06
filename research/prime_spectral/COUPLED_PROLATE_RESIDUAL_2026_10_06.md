# Residual-centered audit of the prolate candidate

The [new audit](../../experiments/prime_spectral/coupled_prolate_residual.py)
replays the exact prolate construction in the same finite Fourier space
as the Weil matrix. It sharpens error propagation by centering at the
candidate's Rayleigh quotient. The tested canonical candidates still
fail the necessary positive-clearance gate; none supplies the missing
input to the conditional strip theorem.

## Normalization and projection checked

The source construction is
[Connes–Consani–Moscovici, equations (7.5)–(7.9)](https://arxiv.org/html/2511.22755v1#S7).
Put `C=lambda^2`, `L=log C`, and `z=x/lambda`. The prolate operator becomes

```
-d/dz[(1-z^2)d/dz] + (2*pi*C)^2*z^2.
```

In the normalized Legendre basis
`phi_(2k)=sqrt[(4k+1)/2]*P_(2k)`, only the degree-zero coordinate has
nonzero integral. Thus `h=h_4-(h_4)_0/(h_0)_0*h_0` has integral zero.
The common factor needed to normalize h in physical x rather than z
cancels when its projected Fourier vector is normalized.

Writing `k(exp t)=exp(t/2)*sum_n h(n exp(t)/sqrt C)` on
`-L/2<=t<=L/2`, the orthonormal even basis is

```
e_0(t)=1/sqrt L,
e_j(t)=sqrt(2/L)*cos[2*pi*j*(t+L/2)/L], j>=1.
```

This is precisely the parity basis of the certified Weil matrix, with
full coefficients `c_0=v_0`, `c_(+/-j)=v_j/sqrt 2`.
Projection onto this basis takes the even part of k; it does not presume
that the compact prolate sum is exactly inversion-even.

For `h(z)=sum_r a_r*z^(2r)`, let `tau=t+L/2`, `T_n=log(C/n)`,
`omega=2*pi*j/L`, and `a=2r+1/2`. The n-th summand contributes the exact
primitive

```
C^(-1/4)*a_r *
 [sqrt(C/n)*(a*cos(omega*T_n)+omega*sin(omega*T_n))
  -(n/C)^(2r)*a] / (a^2+omega^2)
```

before the basis factor. Summing `1<=n<C` gives the implemented closed
formula. The term n=C has zero integration interval. This derivation
accounts for the moving integer thresholds and logarithmic measure;
there is no quadrature over an unresolved jump. Existing tests check
Legendre algebra and independent piecewise integrals, including multiple
thresholds. Infinite-Jacobi eigenfunction-error certificates are replayed
before transferring the error to the exact projected unit vector.

## A sharper exact perturbation lemma

Let A be real symmetric, w a unit trial, `mu=w^T A w`,
`rho=||(A-mu I)w||`, and `||v-w||<=eta` for another unit vector v.
Choose `M_shift>=||A-mu I||`. Set `e=v-w`. Since w and v are unit,

```
v^T A v-mu = 2*e^T(A-mu I)w + e^T(A-mu I)e.
```

Therefore

```
|mu(v)-mu| <= 2*rho*eta + M_shift*eta^2 = epsilon_mu.    (1)
```

This retains the small trial residual in the first-order term. It
replaces the earlier generic bound `2*||A||*eta`.
The Rayleigh quotient minimizes the residual over real shifts, so

```
rho(v) <= ||(A-mu I)v|| <= rho + M_shift*eta.            (2)
rho(v) >= max(0, rho-M_shift*eta-epsilon_mu).            (3)
```

For (3), subtract the two residual vectors and use
`r(v)-r(w)=(A-mu I)e-(mu(v)-mu)v`.
All scalar and vector operations in the audit use outward Arb bounds.
The shifted operator norm is bounded by its maximum absolute row sum.
This is an exact elementary lemma, not a claim of new spectral theory.

If the resulting exact Rayleigh upper bound lies below the second even
eigenvalue, the existing residual-to-ground distance and origin-protection
gate applies. An above-second result supplies no such distance bound.

## Certified result

| C, N | Trial Rayleigh, approximate | Exact residual upper, approximate | Second even eigenvalue, approximate | Reduction of Rayleigh error bound |
|---|---:|---:|---:|---:|
| 13, 4 | 4.332624e-5 | 0.004301942 | 8.649159e-10 | >132 times |
| 13, 8 | 8.199283e-10 | 0.00002376130 | 9.623681e-18 | >181,000 times |
| 17, 8 | 8.986376e-9 | 0.00007371574 | 1.518421e-19 | >72,000 times |

Every exact Rayleigh interval is strictly above the second even
eigenvalue. Certificates:
[13,4](coupled_prolate_residual_13_4.json),
[13,8](coupled_prolate_residual_13_8.json),
[17,8](coupled_prolate_residual_17_8.json).
The sharper transfer confirms the failure cannot be attributed to the
saved prolate approximation uncertainty. It does not rule out a
different estimate, candidate correction, or growing-parameter path.

The source paper's [Section 8](https://arxiv.org/html/2511.22755v1#S8)
also leaves the simple-even ground theorem and sufficiently accurate
prolate-to-Weil approximation open. Its candidate convergence lemma
does not prove ground-profile convergence. The separate
[signed rank-response audit](DEFLATED_RANK_RESPONSE_2026_10_06.md)
suggests controlling the low constrained spectral projections directly.
Doing so for the prolate forcing uniformly in support and rank remains
an unproved input; tighter finite projection balls alone do not supply it.

Tests replay all three certificates, check a genuinely perturbed unit
vector against (1)–(3), and exercise the positive-clearance and rejection
boundaries. These results are not Lean-formalized and do not prove RH.

Verification on 2026-10-06: all 154 prime-spectral unit tests passed in
227.066 seconds. The three new exact-prolate audits and both signed
rank-response certificates replay, and their source/input hashes match.
