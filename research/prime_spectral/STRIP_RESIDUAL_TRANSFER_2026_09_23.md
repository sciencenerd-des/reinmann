# A strip-only residual bridge for the prime spectral route

The finite prime-defined quotient profiles have only real zeros under
the [written quotient proof](QUOTIENT_OPERATOR_2026_09_19.md). To infer RH,
it would suffice to show convergence to normalized Xi **locally uniformly
on the strip** `|Im z|<1/2`; convergence on the entire plane is stronger
than necessary. This observation removes a uniform-variance requirement
from this particular convergence strategy, but does not establish the
missing convergence.

The distinction in [Connes–Consani–Moscovici, §7–8](https://arxiv.org/html/2511.22755v1)
is essential. Their Lemma 7.3 concerns the Fourier transform of the
prolate-wave **candidate** `k_lambda`. They explicitly leave open both
the simple-even property of the least Weil-form eigenvector and an
accurate approximation of that eigenvector by `k_lambda`. Neither their
lemma nor our finite real-zero gates identifies the least-eigenvector
Fourier profile with Xi.

## 1. A residual-to-profile theorem

Let `A` be a real symmetric even-mode matrix on the orthonormal basis
`e_0,...,e_N`, with a simple lowest eigenvalue `lambda_0`, a unit
lowest eigenvector `v`, and all other even eigenvalues at least
`lambda_1>lambda_0`. Let `w` be a unit candidate, oriented so
`inner(v,w)>=0`. Set

```
mu=<Aw,w>, rho=||(A-mu I)w||,
d=sqrt(2)*rho/(lambda_1-mu).
```

If `mu<lambda_1`, then `||v-w||<=d`. Indeed write
`w=alpha v+u`, with `u` orthogonal to `v` and `alpha>=0`.
Projecting the residual onto that orthogonal space gives
`rho>=(lambda_1-mu)||u||`; and
`||v-w||^2=2(1-alpha)<=2||u||^2`.

For support length `L`, define the centered Fourier functional `f_z`
on an even coefficient vector by the same orthonormal Fourier basis as
the finite program. Its origin is `f_0(x)=x_0`. For `|Im z|<=sigma`,
Cauchy-Schwarz and Parseval give the *exact full-space norm bound*

```
|f_z(x)| <= W(sigma,L)||x||,
W(sigma,L)=sqrt[sinh(sigma L)/(sigma L)],
W(0,L)=1.
```

The bound depends only on the imaginary part, not on `Re z`.
Let `P_x(z)=f_z(x)/x_0` and suppose `|w_0|>=c>d`.
Then `|v_0|>=c-d>0`, and the same single denominator calculation gives

```
sup_(|Im z|<=sigma)|P_v(z)-P_w(z)|
    <= W(sigma,L)*d/(c-d)*(1+1/c).                (1)
```

This uses **Fourier-origin normalization** `x_0`. The boundary evaluation
used to define the quotient may be extremely small; dividing by it here
would introduce an unnecessary amplification. Equation (1) follows from
`P_v-P_w=(f_z(v-w))/v_0 + f_z(w)(w_0-v_0)/(v_0 w_0)`,
`|f_z(v-w)|<=W||v-w||`, `|f_z(w)|<=W`, and
`|v_0-w_0|<=||v-w||`.

The implementation takes outward bounds for `rho`, `mu`, `lambda_1`,
`c`, `L` and `sigma`, and rejects either a nonpositive spectral
clearance or a central coordinate not protected by the vector error.
It does not use the numerical value of `lambda_0` in the transfer bound.

### A form-level alternative

There is also a transfer requiring **Rayleigh excess**, without an
operator residual. If the candidate lies in the quadratic-form domain,
has unit norm, and `mu=QW(w,w)<lambda_1`, spectral decomposition gives

```
||w-<w,v>v||^2 <= (mu-lambda_0)/(lambda_1-lambda_0),
||w-v|| <= d_Q
       :=sqrt[2*(mu-lambda_0)/(lambda_1-lambda_0)],       (1a)
```

after orienting the unit ground vector `v` toward `w`. Indeed the
orthogonal spectral mass costs at least `lambda_1` while the ground
mass costs `lambda_0`; for unit vectors with nonnegative overlap,
`||w-v||^2<=2||w-<w,v>v||^2`. Substituting `d_Q` for `d` in (1)
gives the same uniform strip-profile bound. The implementation
`rayleigh_distance_upper` accepts interval bounds for all three
spectral quantities and fails closed unless the candidate is strictly
below the second eigenvalue. This version matches the
[Weil-form projection estimates](PROLATE_WEIL_FORM_PROJECTION_2026_09_23.md),
but it needs an all-support estimate
`(mu-lambda_0)/(lambda_1-lambda_0)` strong enough to overcome the
growing strip-functional norm. Absolute form convergence does not
provide that relative estimate.

## 2. A precise sufficient route to RH

Consider a sequence of certified finite prime quotient profiles
`P_(v_j)` with only real zeros and `P_(v_j)(0)=1`. Suppose there are
unit candidate vectors `w_j` in the same finite even spaces such that
their Rayleigh quotients lie below the second eigenvalues, their
central coordinates exceed their residual distance bounds, and for
every `0<=sigma<1/2` the right side of (1) tends to zero.
Suppose in addition that `P_(w_j)` converges locally uniformly on the
strip to `Xi(z)/Xi(0)`. Then RH follows.

The same conclusion holds if the residual distance in these hypotheses
is replaced everywhere by the Rayleigh-excess distance `d_Q` from
(1a). This removes the need to control an unbounded operator residual
but requires lower and upper eigenvalue estimates fine enough to make
the excess-to-gap ratio vanish at the needed support-dependent rate.

The last step uses Hurwitz's theorem: every nontrivial Xi zero lies in
`|Im z|<1/2`. A nonreal zero would have a small closed disk within the
strip and disjoint from the real axis. The finite profiles are zero-free
on that disk, so their nonzero locally uniform limit cannot vanish
there. Since `Xi(0)!=0`, the limit is not identically zero.

For the paper's `k_lambda`, the
[finite-Fourier diagonal theorem](PROLATE_FOURIER_DIAGONAL_2026_09_23.md)
shows that the even projection with `N(C)=ceil(C^9)` preserves the
candidate's origin-normalized Xi limit. This solves the candidate's
**Fourier truncation** step along one explicit path. The finite Weil
matrices still must approximate the intended Weil form along that path,
and no residual-over-gap decay or ground-profile comparison has been
proved. The paper proves convergence for `k_lambda` itself; it does not
supply these prime-matrix comparison bounds.
Equation (1) states how strong the missing eigenvector estimate must be,
including the gap, central mass and support growth.
The later [Parseval origin-norm obstruction](ORIGIN_NORM_TIGHTNESS_OBSTRUCTION_2026_09_24.md)
shows that if the ground profiles do converge to normalized Xi as
`L=log(cutoff)` grows, the zeroth coordinate of their **unit** ground
vectors must be `O(L^(-1/2))`. A successful unit-vector residual
transfer therefore cannot rely on a support-independent central
lower bound; its error has to overcome the shrinking origin
normalization as well as the strip-functional growth.

At each *fixed* support, the Fourier spaces are already a form core and
their Ritz eigenpairs converge under the simple-lowest assumption; see
the [fixed-support audit](FIXED_SUPPORT_FORM_CORE_2026_09_23.md).
The missing comparison is an effective rate along a joint mode/support
path. The logarithmic form norm does not control boundary evaluation,
which requires an additional eigenfunction-specific estimate. In
particular, the paper's Dirichlet-kernel boundary lemma assumes the
domain of the periodic scaling derivative, a stronger condition than
membership in the Weil operator domain.

## 3. Finite diagnostic and trust boundary

For the stored cutoff-13, mode-4 versus mode-8 eigenvectors, the
previous certificate encloses their **direct** origin-normalized
coefficient distance near `0.2698911863`. The exact strip functional
bound gives, for `|Im z|<=2/5` and every real part,

```
|P_(13,4)(z)-P_(13,8)(z)| < 0.293786.
```

This is a finite profile comparison only. The embedded mode-4
Rayleigh quotient does not lie below the mode-8 second eigenvalue,
so the residual theorem does not certify that pair as a candidate
approximation. The existing very large Rayleigh-excess/gap ratio
already signals this failure. The synthetic test verifies the new
residual and origin-normalized strip bounds on a two-eigenvalue matrix;
it is not evidence that the infinite Weil-form hypotheses hold.
The later [two-frequency constraint certificate](PROLATE_PROFILE_CONSTRAINT_2026_09_23.md)
shows that, in the cutoff-13 even spaces with 4 or 8 modes, a vector
passing the theorem's necessary Rayleigh gate must alter at least one
of the exact prolate profile values at real frequencies 4 and 8 by a
certified positive amount. This finite obstruction is compatible with
the conditional theorem, whose hypotheses require a growing family.

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/strip_transfer.py --comparison research/prime_spectral/mode_comparison_13_4_8.json --height 2/5 --output research/prime_spectral/strip_transfer_13_4_8.json
uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/prime_spectral -p test_strip_transfer.py -v
```

The theorem is elementary finite-dimensional spectral analysis and
Fourier Cauchy-Schwarz; the finite values use FLINT balls. The bridge to
Xi, the uniform simple-even gate, and RH remain unproved.
