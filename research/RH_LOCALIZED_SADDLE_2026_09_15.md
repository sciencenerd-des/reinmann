# Effective localized saddle integration and the remaining uniform gap

## Result and scope

`localized_saddle.py` now supplies certified first-summand moment errors to
`curvature_error.py`. The computation includes quadrature error, both infinite
spatial tails, and the previously proved omitted-theta-series remainder.
It certifies negative true log-epsilon curvature at x = 257, 4097, and 65537.
These are three point certificates, not a continuous tail theorem, a uniform
rank budget, or an RH proof. The earlier all-rank shift-one boundary certificate
is unaffected.

The model is a rigorously enclosed localized integral. It is not a Gaussian
approximation with a fitted error. The analytic tail inequality below holds
for every admissible parameter and window, but the numerical integral and
curvature sign have only been evaluated at the recorded points.

## Analytic tail bound

Write the first-summand logarithmic moments as

    J_k(x) = integral_0^infinity u^(2x) phi_1(u) (2 log u)^k du.

With u = exp(t), set

    p_x(t) = (2x+1)t + (9/2)exp(t) - pi exp(2 exp(t)),
    b(t) = 1 - 3/(2pi) exp(-2 exp(t)).

Then J_k = 4pi^2 integral_R exp(p_x(t)) b(t) (2t)^k dt, and
0 < b(t) < 1. Direct differentiation gives

    p_x''(t) = u [9/2 - 2pi exp(2u)(1+2u)] < 0.

The last inequality follows from u > 0 and 2pi > 9/2; it is global,
independent of x. Thus every tangent line is an upper bound for p_x.
Choose a < b with p_x'(a) > 0 > p_x'(b), and any normalization p0.
For either endpoint e, let lambda be p_x'(a) on the left and -p_x'(b)
on the right. The absolute normalized tail of moment order k is at most

    exp(p_x(e)-p0) 2^k sum_{j=0}^k
        [k!/(k-j)!] |e|^(k-j) / lambda^(j+1).

Proof: put t=a-v or t=b+v. Concavity bounds the exponential by
exp(p_x(e)-p0-lambda*v), and |t|^k <= (|e|+v)^k. Expand this polynomial
and integrate each v^j exp(-lambda*v), whose integral is j!/lambda^(j+1).
This also bounds the signed k=1 moment without assuming its integrand positive.

The code takes c = log(W(2x/pi)/2) and window half-width
16/sqrt(-p_x''(c)). The center need not be an exact saddle: certified signs
at the endpoints are the acceptance condition. It encloses the finite integral
with FLINT, adds the two analytic tails, and explicitly checks positivity of
each resulting moment before forming relative errors.

## Propagation and recorded output

Let Jhat_k be the scaled midpoint model and sigma_k its proved relative
first-summand error. The omitted-theta routine supplies
|I_k-J_k| <= eta_k J_k, with J_k > 0 at the parameters used here. Therefore

    |I_k-Jhat_k| <= [sigma_k + eta_k(1+sigma_k)] Jhat_k.

These errors are supplied at x-1, x, and x+1 to the existing log-moment and
curvature transfer bounds. Scaling constants are evaluated as balls, so their
rounding uncertainty also propagates through the reference calculation.

| x | Curvature, approximate | Propagated error upper bound, rounded up |
|---|---:|---:|
| 257 | -7.954e-7 | 6.152e-26 |
| 4097 | -1.463e-9 | 4.163e-36 |
| 65537 | -3.061e-12 | 3.918e-31 |

Exact outward rational enclosures, individual tail bounds, quadrature radii,
omitted-theta bounds and source hashes are in
`certified_xi/localized_saddle.json`. The table is only a readable summary.
The trust boundary is FLINT ball integration plus the analytic arguments here;
this is not a Lean certificate.

## Why this does not close the unbounded theta estimate

The missing step is a uniform bound for the localized integral's contribution
to curvature. Tiny tail errors alone do not control the sign of its central
part for every x. Nor may derivatives of a numerical midpoint model be
identified with true derivatives; the code instead uses independently enclosed
moment integrals for each required derivative.

[O'Sullivan's Theorem 1.4](https://arxiv.org/html/2007.13582v2)
gives arbitrary-order coefficient expansions with asymptotic remainder terms.
Our remaining continuous claim needs explicit constants and appropriate
logarithmic-moment control; differentiating an unspecified remainder is
insufficient. A useful next target is a uniform Taylor enclosure of the phase
and amplitude in the standardized coordinate t=c+s/sqrt(-p_x''(c)), with
the tangent tails above completing the infinite-domain bound. Its propagated
error must be strictly smaller than the negative model curvature throughout
the claimed tail, followed by a certified compact bridge.

## Fixed-shift pole extension and its logical limit

There is an algebraic extension of the two-pole boundary mechanism. It is
conditional here, not a new interior Xi certificate. Suppose, for a fixed m,
the first m+1 poles of H=1/E(-z) are positive real simple poles, with
alpha_1 > ... > alpha_(m+1) > 0 their reciprocal locations and alternating
residue amplitudes A_j of sign (-1)^(j-1). Assume a contour beyond these
poles excludes every other pole and supplies an exponential coefficient
remainder. Then, for fixed k <= m+1, Cauchy-Binet gives

    D_r(k) ~ C_k (alpha_1 ... alpha_k)^r,
    C_k = (-1)^(k(k-1)/2) (product_j A_j)
          product_{i<j} (alpha_i-alpha_j)^2/(alpha_i alpha_j) > 0,
    C_0 = 1.

For fixed m, the relative remainder is exponentially decreasing: the dominant
subset is {1,...,k}; every other subset has a strictly smaller product.
Multilinearity bounds terms containing the contour remainder in the same way.
Consequently, with q_m = alpha_(m+1)/alpha_m < 1,

    t_r(m) ~ (m+r)/m * C_(m-1) C_(m+1)/C_m^2 * q_m^r,
    delta_r(m) = -r log(q_m) - log(m+r) + constant + O(theta_m^r),
    delta_(r+1)-2delta_r+delta_(r-1)
      = log((m+r)^2/((m+r-1)(m+r+1))) + O(theta_m^r),

for some fixed theta_m < 1. This yields eventual positive correction for that
fixed shift once its hypotheses are established, but constants and thresholds
depend on m. Turning it into an effective certificate also requires explicit
determinant remainder constants and a finite bridge at that shift.

Assuming this ordered real pole structure for arbitrarily many initial poles
would already assume the required global zero-location property. Finite pole
certificates can enlarge a laboratory; they cannot supply the missing uniform
all-shift theorem by extrapolation. The interior cumulative loss bound still
needs a theta-defined or arithmetic invariant that does not presuppose it.

## Replay and validation

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/localized_saddle.py --output research/certified_xi/localized_saddle.json
uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/certified_xi -p 'test_*.py'
```

Four new regression tests check exact tangent integrals and invalid domains,
independent integration in the original u coordinate, decreasing analytic
tails with a wider window, and true-theta curvature after error propagation.
Validated with all 41 certified-Xi tests passing, artifact source hashes and
all three output statuses checked, and `git diff --check` passing. No Lean
files changed in this continuation; the analytic additions are not formalized.
