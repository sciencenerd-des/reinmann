# Prolate-wave candidate: projection and finite gate replay

The [conditional strip theorem](STRIP_RESIDUAL_TRANSFER_2026_09_23.md)
requires a candidate in precisely the orthonormal even Fourier space
of the certified prime-defined Weil matrix. The existing construction
and certificates already supply such a finite candidate. This note
records an independent replay of its normalization, projection, and
finite residual-and-gap prerequisite. The source candidate is the
zero-integral combination of the first and third even prolate
eigenfunctions in [Connes–Consani–Moscovici, §7](https://arxiv.org/html/2511.22755v1).

Put `C=lambda^2`, `L=log C`, `z=x/lambda`, and use the even Legendre
basis `sqrt((2l+1)/2) P_l(z)`. The rescaled differential operator is
`-d/dz((1-z^2)d/dz)+(2*pi*C)^2 z^2`. Only the degree-zero
Legendre coefficient contributes to the integral, so if `H_0,H_4`
are the normalized eigenfunctions, `h=H_4-H_4[0]/H_0[0]*H_0` has
zero integral. The overall scalar does not affect the unit Fourier
vector or its origin-normalized profile.

On `I=[-L/2,L/2]`, let
`K(t)=exp(t/2)*sum_(n exp(t)<=lambda)h(n exp(t))` and
`b_0=L^-1/2`, `b_j=sqrt(2/L)` for `j>=1`. The projection is

```
w_j=b_j*integral_I K(t)*cos(2*pi*j*(t+L/2)/L)dt.
```

If `h(lambda*z)=sum_p a_p*z^(2p)`, set `alpha=2p+1/2`,
`omega=2*pi*j/L`, and `theta=omega*log(C/n)`. Substitution
`z=n exp(t)/lambda` gives the closed formula implemented in
`certified_prolate_projection.py`:

```
w_j=b_j/C^(1/4) * sum_(n=1)^(C-1) sum_p a_p
    * [sqrt(C/n)*(alpha*cos(theta)+omega*sin(theta))
       -(n/C)^(2p)*alpha]/(alpha^2+omega^2).              (1)
```

The `n=C` term has zero-length support. Since the constant Fourier
mode is retained, projection preserves `F_0(K)` exactly; after
normalizing the coefficient vector, its profile is divided by its
positive zeroth coordinate. Independent piecewise integration tests
check (1), including jumps at several sum thresholds. The interval
projection and the certified prolate eigenspace-error transfer are
then replayed from their saved inputs.

At support `C=13`, the exact candidate's Rayleigh quotient is
**certifiably above** the second even Weil eigenvalue in each tested
space:

| Fourier modes | Lower bound on exact Rayleigh excess |
|---:|---:|
| 4 | `4.33253e-5` |
| 8 | `8.19896e-10` |
| 12 | `3.55210e-15` |
| 16 | `2.44795e-20` |

The first two results propagate the exact prolate eigenfunction error
through the analytic projection to a rounded rational vector; the
last two use direct higher-mode interval projection and spectrum
certificates. The strip residual theorem requires the **opposite**
strict inequality, `Rayleigh < second eigenvalue`, before its
residual-over-gap denominator exists. Thus this finite candidate
does not clear that gate at any of these four ranks. This is no
obstruction theorem over all ranks or increasing support. In
particular, it neither establishes nor refutes the missing
prolate-to-Weil ground-profile comparison needed for RH.
The [low-cluster certificate](PROLATE_LOW_CLUSTER_2026_09_24.md)
shows that these finite ground-vector gate failures are compatible
with strong concentration in the first four even Weil modes.

The replayed tests are `test_certified_prolate_projection.py`,
`test_exact_prolate_finite_gate.py`, and
`test_higher_mode_prolate_gate.py` under
`experiments/prime_spectral/`. The full certificates and provenance
are in `exact_prolate_gate_13_{4,8,12,16}.json` in this directory.
