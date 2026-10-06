# Smooth-support derivative of the finite Weil matrix

The [prolate residual-and-gap audit](PROLATE_RESIDUAL_GAP_AUDIT_2026_09_26.md)
tests the canonical candidate at fixed supports. A comparison along changing
support also needs control of the prime-defined Weil matrix between prime-power
thresholds. The [interval implementation](../../experiments/prime_spectral/smooth_support_derivative.py)
now encloses its exact derivative in the same even Fourier coordinates used by
that audit. This is a finite matrix derivative, not a ground-profile variation
bound.

Write `L=log C`, `q(t)=q_{mn}(Lt)`, and `q0=2` for `m=n`, otherwise `0`.
The function `q(t)` is independent of `L`; in particular `q(1)=0`.
For the pole term `P(L)=L integral_0^1 2 cosh(Lt/2) q(t) dt`, direct
differentiation gives

```
P'(L) = integral_0^1 [2 cosh(Lt/2)+Lt sinh(Lt/2)] q(t) dt.
```

The regularized archimedean term in `certified_weil.entry` is

```
I(L) = integral_0^L [exp(z/2)q(z/L)-q0]/[2 sinh z] dz.
```

Its moving-endpoint derivative is `-q0/[2 sinh L]`. The analytic tail
`(q0/2) log tanh(L/2)` has derivative `+q0/[2 sinh L]`. These terms cancel
*before* interval evaluation. With `sinhc(x)=sinh(x)/x`, the derivative of
the complete archimedean contribution `-I(L)-(q0/2)log tanh(L/2)` is

```
integral_0^1 exp(Lt/2) q'(t)/[2L sinhc(Lt)] dt.
```

This integrand is regular at `t=0`. It avoids separately enclosing two
opposing endpoint terms. The pole and archimedean integrals are evaluated on
the fixed interval `[0,1]` using Arb complex balls.

Between thresholds, each prime power `p^k<C` contributes
`(log p)/(sqrt(p^k)) * (log(p^k)/L^2) q'(log(p^k)/L)` to the derivative.
At `C=p^k`, the continuous matrix entry has a one-sided derivative jump:
`q'(1)=-2` for every Fourier index pair. Thus the right-minus-left jump
on the even block is exactly

```
-2/(k sqrt C) * u u^T,       u=(1,sqrt(2),...,sqrt(2)).
```

The [17/1](smooth_support_derivative_17_1.json),
[17/8](smooth_support_derivative_17_8.json), and
[19/8](smooth_support_derivative_19_8.json) certificates enclose both
one-sided matrices and verify this rank-one identity at those finite sizes.
The [replay tests](../../experiments/prime_spectral/test_smooth_support_derivative.py)
compare an interior secant of the independently evaluated original Weil
entry with the differentiated formula, then replay all three saved
certificates. The secant is a diagnostic; the displayed differentiation
and Arb enclosures establish the finite derivative formula.

## Coupled finite ground-profile response

The [profile implementation](../../experiments/prime_spectral/smooth_support_profile.py)
uses the isolated simple lowest even eigenpair at `C=17,19`, rank `8`.
Write its eigenvector in origin-normalized coordinates as `h=(1,h_tail)`,
let `A'` be either one-sided matrix derivative, and put
`T=A_tail,tail-lambda_0 I`. Differentiating the eigenvalue equation gives

```
lambda_0' = (h^T A' h)/(h^T h),
h_tail' = -T^(-1) [(A'h)_tail-lambda_0' h_tail].
```

The source combines the matrix and eigenvalue derivatives *before* the
positive constrained solve. For the origin-normalized Fourier functional
`F_z(L)h`, the full response is

```
d/dL [F_z(L)h(L)] = F_z'(L)h + F_z(L)(0,h_tail').
```

The derivative `F_z'` follows by differentiating each sinc term of the
centered Fourier basis. The [17/8](smooth_support_profile_17_8.json) and
[19/8](smooth_support_profile_19_8.json) certificates enclose these
derivatives at `z=4,8,i`. At `C=17`, for example, the two one-sided
derivatives of the profile at `z=4` are approximately `-0.06648` and
`-0.10593`; at `C=19` they are approximately `-0.15783` and `-0.19234`.
The exact outward rational endpoints are in the JSON files. Their jumps
overlap the independently saved [prime-threshold profile-jump](prime_threshold_jump_17_8.json)
certificates. [Tests](../../experiments/prime_spectral/test_smooth_support_profile.py)
replay both finite files, compare all three profile jumps with the
independent certificates, and check `F_z'` against a Fourier-functional
secant. The secant comparison is diagnostic, not a uniform derivative
bound.

These derivatives do not repair the canonical prolate candidate's failed
finite gate: its Rayleigh quotient is above the second even eigenvalue in
the certified configurations. They do not bound the support integral of
the origin-normalized lowest-eigenvector response or a joint support/rank
limit. A uniform spectral-gap and Schur-response budget across the interior
and every prime-power boundary is still missing. RH remains open.

Replay from the repository root:

```sh
uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/prime_spectral -p test_smooth_support_derivative.py -v
uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/prime_spectral -p test_smooth_support_profile.py -v
```
