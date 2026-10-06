# Integrating the Gaussian error before bounding curvature

Update: [direct derivative bounds](RH_GAUSSIAN_JET_TAIL_2026_09_20.md)
lower the sufficient threshold to u>=14. The u>=40 result below remains
a valid earlier bound; neither result closes all anchors or all ranks.

## Result

The [effective Gaussian tail proof](RH_EFFECTIVE_GAUSSIAN_TAIL_2026_09_19.md)
can be sharpened without changing its reference or omitting any remainder.
Integrate the positive polynomial error bounds against the Gaussian density,
and use a larger common complex disk. For every real anchor

    u=W(2a/pi)/2 >= 40, equivalently a>=40*pi*exp(80),

both the frozen-reference and true Xi curvature satisfy

    |F''(a)+N(a)| < 0.038351*N(a),
    N(a)=(4u^2+8u+1)/[a^2(1+2u)^4].

Thus their sign is strictly negative on this entire tail. The argument
is a written analytic proof, with its explicit inequalities checked using
FLINT balls. It is not Lean formalized. The lower-anchor bridge and
interior all-rank budget remain unproved; RH is not proved.

## 1. Integrated central error

Retain all definitions in the effective proof, including the normalized
error scale u^6/a^(3/2), and fix U>=20. Let

    m_j=(1/sqrt(2pi)) integral_R exp(-s^2/2)|s|^j ds.

Integration by parts gives m_0=1, m_1=sqrt(2/pi), and
m_(j+2)=(j+1)m_j. These are positive absolute moments, so replacing
the finite central interval by the whole line in an error bound only
increases the bound.

The jth phase coefficient, for j>=5, has absolute value at most

    c_j*u^(j/2-1)*a^(1-j/2),
    c_j=(5+2^j*B_j)/(j!*2^(j/2)).

Consequently the integrated phase error, divided by u^6/a^(3/2), is
bounded uniformly on the tail by

    R_int=sum_(j=5)^16 c_j*m_j*U^(j/2-7)*X^((5-j)/2).

For each term the logarithmic derivative of its u-dependent factor is
-4.5/u-(j-5)<0. This establishes the bound for all u>=U directly.
The window supremum R from the effective proof is still retained in
exponential factors; it is not discarded.

There is also a spatially linear amplitude error. Under the same
amplitude conditions as before, |s|<=L implies

    |B(s)-1| <= 12 exp(16u/sqrt(a))*u^(3/2)/a^(3/2)*|s|.

Indeed beta/(1-beta)<=4u/a and the amplitude exponent has magnitude
at most 4u|s|/sqrt(A). Use |exp(x)-1|<=exp(|x|)|x|,
A>=2au, and 16/sqrt(2)<12. Its normalized Gaussian integral is at most

    A_int=12 exp(16U/sqrt(X))*m_1/U^(9/2).

For the exponential Taylor remainder define the positive polynomial

    J(s)=4s+3s^3+3sqrt(U/X)s^4, s>=0.

Since |V1|+|V2|<=sqrt(u/a)*J(|s|), its integrated cubic remainder
is bounded, in the same normalization, by

    exp(B1+B2)*E[J(|G|)^3]/[6U^(9/2)],

where G is standard normal. The expectation is a finite sum of positive
coefficients times m_j, j<=12, evaluated exactly as a polynomial expression
with ball coefficients. No cancellation or tail is dropped.

The two remaining quadratic cross terms have normalized integrals at most

    3(4m_5+3m_7)/U^(9/2), 9m_8/(2U^4sqrt(X)).

Combining these terms replaces equation (3) of the effective proof by

    C_c=exp(eta)*[
      exp(B1+B2+R)*(A_int+R_int)
      +exp(B1+B2)*E[J(|G|)^3]/(6U^(9/2))
      +3(4m_5+3m_7)/U^(9/2)+9m_8/(2U^4sqrt(X)) ].       (1)

Each endpoint expression bounds a decreasing function for u>=U.
All later estimates retain their previous normalization and algebra.
This avoids assigning the largest error near the window edge to the
entire Gaussian mass.

## 2. A larger complex disk, with its full cost included

Choose a fixed divisor d>=1, and assume sqrt(X)>2d. Replace the
reference disk by

    |z-a|<=sqrt(a)/d, t=2(z-a)/sqrt(A), eta=8/d.

Then |t|L<=eta and |t|<=2/[d sqrt(2u)]<=1 for u>=20.
The central error factor exp(eta) in (1) and the Gaussian-tail factor
exp(eta) both use this enlarged value; the tilt penalty is not hidden.

In the Gaussian tail proof T=eta/L satisfies L-T>=L/2, since
eta<=8<=16u=L^2/2. Thus the same integer tail coefficient bound
and its resulting expression C_t remain valid, with the new eta.
The factor exp(-t^2/2) is still bounded in modulus by exp(1/2).
The moment polynomial and logarithm bounds use |t|<=1, so they also
remain valid without change. The condition w<1/2 is checked anew.

For |y-a|<=1 the disk centered at y with radius sqrt(a)/(2d)
lies inside the reference disk. Cauchy's estimate becomes

    |E_a^(j)(y)|<=j!*(2d)^j*C*u^6/a^((3+j)/2).

Accordingly, replace 64 by 2d in K_H,K_L,K_M. Every other transfer
condition and final curvature formula in the effective proof is unchanged.
The true I/Q remainder uses its own previously established complex disk;
it does not require extending that theorem to this larger reference disk.

## 3. Whole-tail certificate and limits

At U=40,d=2, all twelve sufficient conditions in the implementation pass,
including the amplitude, logarithm, deficit, derivative, and true-theta
clearance checks. The final relative margin budget is enclosed below

    0.038351 < 1/2.

The endpoint-to-tail extension follows from the monotonicity arguments
above and those in the effective proof. This certifies a continuum of
anchors, not just a set of evaluated points. At U=35,d=4 the sufficient
budget fails; the code reports unresolved, not positive curvature.

The new threshold remains very large. No conclusion is asserted for
uncertified lower anchors or unbounded interior Toeplitz rank. Improving
this sufficient rank-two curvature condition is not a substitute for
proving the interior rank budget.

Replay:

    uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/gaussian_tail_bound.py --threshold-u 40 --integrated-errors --disk-divisor 2 --output research/certified_xi/integrated_gaussian_tail_bound.json
    uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/certified_xi -p 'test_*.py'

The saved JSON contains exact rational upper bounds and the source hash.
Tests check the absolute moment recurrence, passing and failing budgets,
and parameter rejection. They do not formally verify the analytic proof.

Validation: 71 certified-Xi tests passed. Both tail artifacts match the
current implementation hash; `git diff --check` passed.
