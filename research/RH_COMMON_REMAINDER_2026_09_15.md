# Uniform derivatives of an anchor-common Xi remainder

Update 2026-09-20: [exact absorption of the linear Gaussian tilt](RH_SHIFTED_GAUSSIAN_CURVATURE_2026_09_20.md)
now proves the reference and true curvature sign for every anchor a>=10^6.
This resolves the uniform-sign gap described historically below on the
stated common-reference domain. The interior all-rank budget remains open.

## Precise result and scope

This note constructs a single analytic reference **for each anchor a**, used
unchanged at all neighboring parameters y. It proves explicit bounds for
the derivatives of R_a(y)=log I(y)-log Q_a(y), uniformly over every real anchor
a>=X and every real |y-a|<=1. The bounds include the full theta series and
both infinite spatial tails.

The family Q_a is not the moving model Q_y from the previous calculation.
The anchor a is held fixed when differentiating in y. No globally glued
reference S(y) is claimed. This local common-reference family is sufficient
for the three-neighbor curvature transfer: one uses the same Q_a at a-1,a,a+1.

The derivative theorem does not prove uniform negativity of the reference
curvature as a varies. That sign theorem and the interior all-rank budget
remain open. The previously proved shift-one boundary result is unchanged.

## 1. Frozen reference and complex normalization

Write I(z)=integral_0^infinity v^(2z) Phi(v) dv. This is holomorphic for
Re z>-1/2: on compact subsets, the integrand and each parameter derivative
are dominated by an integrable power times a power of |log v| near zero,
and by the theta kernel's rapid decay at infinity.

Fix a real anchor a>=X>=10^6. Set

    u=W(2a/pi)/2, c=log u,
    A=2a(1+2u)-(9/2)u, L=sqrt(32u),
    t=c+s/sqrt(A).

Let P_a(s) be the degree-16 Taylor polynomial of
p_a(c+s/sqrt(A))-p_a(c), with p_a and b as in the high-order saddle note.
Define the entire function

    Q_a(z)=4pi^2 exp(p_a(c))/sqrt(A)
           integral_{-L}^L exp(P_a(s)) b(t) exp(2(z-a)t) ds.

Every coefficient, endpoint, and amplitude in this definition is frozen at a.
The only dependence on z is the exponential tilt. Therefore its centered
parameter derivatives are integrals with the factors (2s/sqrt(A))^k.
There are no moving-boundary derivative terms.

For complex estimates use the centered quantities

    Qbar_a(z)=exp(-2(z-a)c) Q_a(z),
    Ibar_a(z)=exp(-2(z-a)c) I(z).

Their ratio is exactly I(z)/Q_a(z). Let

    eta=1/4, rho_a=sqrt(A)/(8L).

Since a(1+2u)<=A<=2a(1+2u) and u>=1,
sqrt(a)/32<=rho_a<=sqrt(3a)/32<a/2. Thus the entire disk stays inside
Re z>0, where the true moment integral is holomorphic.

If |z-a|<=rho_a and |s|<=L, the central tilt has
|2(z-a)s/sqrt(A)|<=eta. The model integrand at a is strictly positive, so

    Re Qbar_a(z) >= exp(-eta) cos(eta) Q_a(a)
                  >= exp(-eta)(31/32) Q_a(a).

The last step uses cos t>=1-t^2/2. Thus Q_a has no zeros on this disk;
we have not assumed a zero-free region for the true Xi moment integral.

## 2. Complex saddle error, including both outer tails

Take the constants R0, tau, d, C3, h0, u0 and L0 from the growing-window
bounds at threshold X. Write

    a0=11 exp(-u0)/(2 sqrt(2pi)),
    b0=3/(2pi) exp(-2u0 exp(-h0)),
    H0=2 exp(-a0-1/2-C3/6-R0)(1-b0).

The previous proof gives a lower bound H0 on the normalized reference mass
and the real phase remainder |p_a-p_a(c)-P_a|<=R0 on the central window.
Multiplying by the complex tilt and taking absolute values therefore bounds
the central error relative to Q_a(a) by

    Ec=exp(eta)(exp(R0)-1).

At either window endpoint, the true normalized phase is at most -tau L^2,
and the inward standardized tangent slope is at least d L. The modulus of
the complex tilt contributes at most eta at the endpoint and at most
eta/L per unit outward standardized distance. Hence both tilted tails are
integrable whenever

    dtilt=d-eta/L0^2 > 0,

and their sum relative to Q_a(a) is at most

    Et=2 exp(-tau*32u0+eta)/(H0 dtilt L0).

This uses global real phase concavity to extend the tangent bound over the
entire left and right tails. Both are included; there is no omitted boundary
term. Put Es=Ec+Et. Then, throughout the complex disk,

    |Jbar_a(z)-Qbar_a(z)| <= Es Q_a(a),

where J is the full first-summand integral, centered in the same way.

## 3. Transfer from the first summand to the true theta integral

The original version used a fixed theta bound valid for Re z>=500000.
That bound was valid but left a fixed contribution to the log-remainder
majorant. The current implementation uses the decreasing bound proved in
[the decaying-remainder note](RH_DECAYING_COMMON_REMAINDER_2026_09_15.md).

Writing Es=Ec+Et, that proof gives

    Etheta <= rho_high(exp(eta)+Es)+rho_global Et,
    sigma = (Es+Etheta)/[exp(-eta)(31/32)],

where rho_high decreases with the anchor and rho_global is used only on the
spatial tail. All constants are uniform over a>=X. The implementation checks
sigma<1, which excludes zeros of I and defines the analytic remainder by
its convergent logarithm series:

    R_a(z)=log(1+[I(z)/Q_a(z)-1]),
    |R_a(z)|<=M=-log(1-sigma).

On the real axis this agrees with log I-log Q_a because both integrals are
positive. Zero exclusion is proved before using the logarithm. The derivative
proof below is unchanged; the new note additionally proves a power-law bound
as the anchor increases.

## 4. Uniform derivative theorem

**Theorem.** Let X>=10^6 and let the explicit checks above succeed. Define
r_X=sqrt(X)/32. For every real anchor a>=X, every real |y-a|<=1, and every
integer j>=0,

    |R_a^(j)(y)| <= j! M/(r_X-1)^j.

**Proof.** The disk about a has radius rho_a>=r_X. Each y in the asserted
interval has a disk of radius r_X-1 inside it. Cauchy's derivative estimate
applied to the analytic R_a bounded by M gives the result. If necessary,
apply the estimate at slightly smaller radii and take the limit. The strict
sigma<1 bound supplies an analytic neighborhood of the closed disk. QED.

The code records j=0,...,4. These are bounds for actual derivatives of a
common remainder, not inferred derivatives of sampled errors.

The computed bounds, rounded upward, are:

| Every anchor a>=X | Second derivative absolute bound | Third derivative absolute bound | Fourth derivative absolute bound |
|---|---:|---:|---:|
| 10^6 | 3.056e-24 | 3.031e-25 | 4.008e-26 |
| 10^8 | 4.153e-39 | 4.000e-41 | 5.136e-43 |
| 10^12 | 4.789e-70 | 4.597e-74 | 5.885e-78 |

All suprema here are over the full interval |y-a|<=1. The JSON certificate
contains exact rational upper bounds.

## 5. Cancellation-preserving curvature transfer

For any C^2 function R,

    Delta2 R(a)=R(a-1)-2R(a)+R(a+1)
              =integral_{-1}^1 (1-|s|)R''(a+s) ds.

The tent kernel has mass one. With the anchor frozen, differentiating in
the central parameter gives analogous identities for Delta2 R' and
Delta2 R''. Thus if E_j bounds |R_a^(j)| on [a-1,a+1], the errors in
log q, (log q)' and (log q)'' are at most E_2,E_3,E_4, respectively.

The calculation uses Q_a(a-1), Q_a(a), Q_a(a+1) and their actual centered
parameter derivatives. The common affine term 2(z-a)c disappears from the
second differences and from the variances. A log-q error E_2 implies an
absolute q error at most |q_reference| expm1(E_2). The existing curvature
transfer routine then supplies a true-theta curvature enclosure.

This differs from applying a separate relative error at each of three points:
the cancellations have occurred inside an integral identity before the error
is bounded. All reference quadrature uncertainties are retained as balls.

## 6. Implementation and completion boundary

`common_remainder.py` computes uniform derivative bounds for thresholds
10^6,10^8,10^12 and performs curvature evaluations at two anchors. The
uniform theorem concerns the remainder derivatives. The output classification
continues to restrict each curvature sign to its evaluated anchor.

The new joint transfer certifies true curvature at a=1000001 in
[-8.048253e-15,-8.048208e-15], with propagated error below 2.187e-20.
The earlier independent-error calculation at this anchor was inconclusive.
At a=100000001 the curvature is also certified negative, with propagated
error below 2.737e-35. These decimals are outward summaries of the saved
rational enclosures; they are not a sign theorem over all anchors.

The remaining uniform-sign task is to bound the reference curvature over
all anchors, using the now available common-remainder budget. This note does
not identify the frozen reference with the leading Lambert model, and does
not differentiate the original moving-model error estimates. No all-rank
interior conclusion follows from the derivative theorem.

Trust boundary: the analytic arguments above, the preceding explicit saddle
and theta-tail bounds, and FLINT ball arithmetic. This is not Lean formalized.

Replay:

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/common_remainder.py --output research/certified_xi/common_remainder.json
uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/certified_xi -p 'test_*.py'
```

Validation: 57 certified-Xi tests passed. New tests check centered-moment
consistency, complex tilts against an independent exact-phase integral,
derivative-bound acceptance and monotonicity controls, and the formerly
inconclusive anchor. Saved source hashes, all tabulated derivative ceilings,
zero-exclusion bounds and both curvature signs were checked. `git diff --check`
passed. No Lean source was changed or rebuilt in this continuation.
