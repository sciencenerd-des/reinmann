# A decaying common-remainder bound and the remaining sign problem

## What changed

The common-remainder construction previously used one fixed omitted-theta
bound. It was valid, but its nonzero contribution to the log-remainder bound
made it unsuitable for arbitrarily far-tail comparisons with vanishing
curvature. This note replaces that bound and proves an explicit decay law.
No reference-curvature or interior all-rank positivity theorem is claimed.

Write u(a)=W(2a/pi)/2 and fix X=10^6. For the same frozen reference Q_a and
R_a=log(I/Q_a) as in the preceding note, the improved theorem is

    |R_a^(j)(y)| <= E_j(X) [u(a)/u(X)]^16 [X/a]^(7+j/2),
    every a>=X, every |y-a|<=1, j=0,1,2,3,4.

Here E_j(X) is the explicitly computed threshold constant in
`common_remainder.json`. In particular the decay is
O((log a)^16/a^(7+j/2)). This theorem concerns actual derivatives of a
common analytic remainder. It does not assert a sign for the reference
curvature that the remainder approximates.

## 1. A theta bound that decreases with the anchor

Use v for the original positive integration variable, and write
Phi(v)=phi_1(v)+T(v), T>=0. With E=exp(2v), dropping the negative term in
each omitted summand gives

    T(v)/phi_1(v)
      <= 16 exp(-3pi E)/[(1-16 exp(-5pi E))(1-3/(2pi E))]
      <= C exp(-3pi E),
    C = 16/[(1-16 exp(-5pi))(1-3/(2pi))].

The sum is bounded geometrically: for j>=2 the ratio between successive
j^4 exp(-pi(j^2-1)E) terms is at most 16 exp(-5pi E)<1. This proves the
bound for every v>=0. In particular rho_global=C exp(-3pi) is a global bound.

For the anchor a set L=sqrt(32u), A=2a(1+2u)-(9/2)u and
v_left=u exp(-L/sqrt(A)). For every a>=X the earlier displacement estimate
with D_X=2u(X)h(X)exp(h(X)) gives

    exp(2v) >= exp(2u-D_X), for v>=v_left.

Since a=pi u exp(2u), we obtain

    T(v)/phi_1(v) <= C exp(-3(a/u)exp(-D_X)).

For every positive z and integer N>=1, exp(z)>=z^N/N!, hence

    exp(-z)<=N!/z^N.

Taking N=16 yields the explicit high-region bound

    rho_high(a) = C 16! exp(16D_X) [u(a)/(3a)]^16.

It decreases to zero. The implementation may use the sharper displacement
constant evaluated at its own threshold; both choices are valid. This bound
avoids constructing giant exact denominators for exponentially tiny terms.

## 2. Complex error with both tails retained

Recall eta=1/4, the complex disk |z-a|<=sqrt(A)/(8L), the normalized
first-summand error Es(a), and its absolute spatial-tail component Et(a).
Both errors are measured relative to Q_a(a). The modulus integral for the
first summand is bounded by exp(eta)+Es(a).

Split the omitted theta integral at v_left. In the central and right regions
use rho_high(a); in the left region use rho_global. Since Et bounds both
first-summand spatial tails, the following safe overestimate results:

    Etheta(a) <= rho_high(a)[exp(eta)+Es(a)] + rho_global Et(a).

The total complex relative error is therefore

    sigma(a) <= [Es(a)+Etheta(a)]/[exp(-eta)(31/32)].

As before, sigma<1 proves zero exclusion for I and defines the analytic
log remainder, with M(a)=-log(1-sigma(a)). The implementation uses log1p
for this last expression to avoid loss of precision at small sigma.
The fixed 500000-threshold theta bound is no longer used by this module.

## 3. Proof of the explicit power-law envelope

Freeze every majorant constant at X. Let

    F(a)=[u(a)/u(X)]^16 [X/a]^7.

This lies in (0,1] for a>=X: using a=pi u exp(2u), its logarithmic derivative
with respect to u is 9/u-14<0 because u>=u(X)>3/2.

The high-order phase remainder uses n=17. Its first term scales as
u^(17/2)exp(-15u), so relative to its value at X it equals

    [u/u(X)]^16 [X/a]^(15/2) <= F(a).

Its second term scales as exp(-17u), and is likewise bounded by F(a) times
its threshold value. Convexity of exp(t)-1 on t>=0 implies that the resulting
central exponential error is at most F(a) times its threshold bound.

The tail bound contains exp(-32tau_X u). The saved threshold calculation
certifies tau_X>7/16 and tau_X<1/2. Therefore its ratio to the threshold value
is

    [u/u(X)]^(16tau_X) [X/a]^(16tau_X) <= F(a).

All remaining tail factors can be bounded by their threshold values: the
model-mass lower bound is fixed, the effective tangent slope increases with
L, and L/(sqrt(A)log u) decreases. Thus Et(a)<=Et(X)F(a), and the same
holds for Es.

The high theta factor scales as [u/u(X)]^16[X/a]^16<=F(a). Its product
with Es introduces F(a)^2<=F(a). Hence sigma(a)<=sigma_X F(a).
Convexity of -log(1-t), with value zero at t=0, gives

    M(a)<=M_X F(a).

Finally the Cauchy clearance obeys

    sqrt(a)/32-1 >= sqrt(a/X)[sqrt(X)/32-1].

Applying Cauchy's formula on the neighbor disk gives the stated estimate
E_j(X)F(a)(X/a)^(j/2). All statements quantify over the unbounded real anchor
domain; the finite regression checks are not the reason for that quantifier.

Since pi u>1 on this domain, a=pi u exp(2u)>exp(2u), and u<(log a)/2.
This proves the displayed logarithmic-power asymptotic without additional
asymptotic assumptions about Xi.

## 4. What remains unproved

The reference integral still contains a degree-16 polynomial in its exponent.
Controlling its curvature uniformly as the anchor varies requires a sign
argument for that family, or a further comparison to an explicit model with
a proved sign. The positive margin of the leading Lambert model cannot be
assigned to this reference without that comparison. The decaying error theorem
removes an obstacle to such a comparison; it does not supply the missing sign.

The independent rank problem also remains. A recent preprint,
[Michalowski, An explicit uniform cubic wedge for consecutive Toeplitz minors of the Riemann xi-coefficients](https://arxiv.org/html/2607.16795v1),
claims positivity when the shift k>=10^18 r^3 for every rank r. Its method
uses a complex saddle bound and a q-Pascal dilation factorization. Even if
that result is accepted, it covers a tail region, not the complementary
interior. Its ancillary certificates were not replayed here, and no result
from the preprint is imported as a repository theorem.

Thus neither requested conclusion has been proved in this continuation.
Repeated point evaluations cannot fill either unbounded gap.

## 5. Implementation and validation

- `decaying_theta.py`: geometric-series and factorial theta bounds.
- `common_remainder.py`: decreasing theta error, stable logarithm, and explicit
  power-law derivative envelopes from one threshold.
- `test_common_remainder.py`: checks high-region bounds and compares the
  power-law envelope with independently recomputed threshold bounds.
- `common_remainder.json`: regenerated source hashes, derivative bounds,
  existing anchor certificates and evaluations of the decay envelope.

The analytic proof is not Lean formalized. The prime-defined program and the
shift-one boundary certificate are unchanged.

Validated with 59 certified-Xi tests passing, regenerated source hashes and
anchor classifications checked, and `git diff --check` passing. New regression
tests check the theta comparison on both regions and the power-law envelope
against directly recomputed derivative bounds. The proof of uniform decay
is the analytic argument above, not these finite comparisons.
