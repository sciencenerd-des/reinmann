# Coefficientwise remainder derivatives and sharper curvature transfer

Update: [absorbing the linear phase exactly](RH_SHIFTED_GAUSSIAN_CURVATURE_2026_09_20.md)
closes the remaining bridge within a>=10^6. The estimates below remain
valid; the interior all-rank budget is still unproved.

## Uniform result and remaining scope

For every real anchor

    u=W(2a/pi)/2>=6, equivalently a>=6*pi*exp(12),

the reference and true theta curvatures satisfy

    |F''(a)+N(a)|<0.468174*N(a),
    N(a)=(4u^2+8u+1)/[a^2(1+2u)^4].

Both are therefore negative on this continuum of anchors. The threshold
is about 3.068e6, reduced from 7*pi*exp(14) in the
[cubic expansion](RH_CUBIC_GAUSSIAN_TAIL_2026_09_20.md).
The remaining common-reference bridge 10^6<=a<6*pi*exp(12) is not closed.
The interior all-rank budget also remains unproved; RH is not proved.

This note changes neither the degree-16 reference nor its exact cubic
logarithm correction. It sharpens the error accounting in two places:
Taylor coefficients receive individual bounds, and curvature sensitivities
retain the available deficit lower bound. The proof is written analysis
with FLINT ball checks of explicit constants, not a Lean formalization.

## 1. Positive Taylor-series majorants

Use all notation of the cubic expansion. At each fixed real tilt t0 with
|t0|<=T=1/sqrt(au), write the Taylor variable as x. If a positive-coefficient
polynomial P majorizes the absolute coefficients of an analytic function's
Taylor series, addition and multiplication preserve that majorization.
This follows coefficient by coefficient from the triangle inequality and
the Cauchy product. Derivatives up to order four depend only on coefficients
of degree at most four, so calculation modulo x^5 is exact for this purpose.

Let d_k be the already proved bounds |D^(k)(t0)|<=d_k*epsilon^4,
epsilon=sqrt(u/a). Instead of summing all coefficients into one jet norm,
retain the polynomial

    c_e(x)=sum_(k=0)^4 sum_(i=0)^k
             M_i(T)*d_(k-i)/(i!*(k-i)!)*x^k.

It majorizes the Taylor coefficients of exp(-t^2/2)D(t)/epsilon^4 through
degree four. The product rule and the absolute Hermite majorants prove this
individually for each k, exactly as in the preceding norm argument.

For P1/epsilon, P2/epsilon^2, P3/epsilon^3, construct the polynomials
p(x), q2(x), q3(x) by the preceding positive expressions, now evaluating
each moment polynomial M_j at T+x instead of the scalar 1+T.
For example p(x)=l*M1(T+x)+b0*M3(T+x). The other two use the full
expressions in the cubic note, including the amplitude term 3*M1(T+x).
Because all M_j have nonnegative coefficients, these majorize the absolute
Taylor coefficients at every |t0|<=T.

Define, using positive coefficients and reducing modulo x^5 only as needed,

    w=epsilon*p+epsilon^2*q2+epsilon^3*q3+epsilon^4*c_e,
    v=q2+epsilon*q3+epsilon^2*c_e.

The preceding norm condition implies w(0)<1. The geometric series 1/(1-w)
has nonnegative Taylor coefficients. Indeed w(0)<1 gives convergence in
a neighborhood of x=0; its coefficients are sums of nonnegative terms.
Therefore the logarithm-tail inequality also holds coefficientwise:

    sum_(n>=4) w^n/n <= w^4/[4(1-w)].

In the algebra on each Taylor coefficient, the fourth-order log remainder
is bounded by epsilon^4*C(x), where

    C(x)=c_e+p*(q3+epsilon*c_e)+v^2/2+p^2*v
           +epsilon*p*v^2+epsilon^2*v^3/3
           +(p+epsilon*q2+epsilon^2*q3+epsilon^3*c_e)^4/[4(1-w)].

This is the same complete logarithm remainder accounting as before, with
positive polynomials replacing scalar norms. If C_j=[x^j]C(x), then

    |E_a^(j)(y)| <= j!*C_j*(u/a)^2/(au)^(j/2),
    j=0,...,4 and every real |y-a|<=1.                 (1)

All the positive input coefficients decrease with u, as proved in the
cubic note. The coefficients of 1/(1-w) increase with each coefficient
of w on w(0)<1. Thus freezing C_j at U gives uniform bounds for every
u>=U; no sampling argument is used.

At U=6, rounded upward, the individual constants are

    C0<92.004, C1<197.666, C2<473.668,
    C3<378.096, C4<550.258.

Previously each derivative was charged the full norm C<1739.068.
In particular the fourth derivative now costs 24*C4/a^4, rather than
24*C/a^4. Its exact cubic correction is still retained unchanged.

## 2. Neighboring-parameter errors

In equation (9) of the cubic note, replace C by C2 in H, by C3 in K,
and by C4 in M. All the polynomial corrections and amplitude/tail bounds
are otherwise unchanged. This yields uniform inequalities

    |log q+h/a|<=H/a^2,
    |(log q)'-ell/a^2|<=K/a^3,
    |(log q)''-m/a^3|<=M/a^4,

where h=4u/(1+2u), ell=16u^2(u+1)/(1+2u)^3 and
m=-16u^3(8u^2+16u+9)/(1+2u)^5. H,K,M are frozen at U.
The same tent-kernel identity preserves the shared-neighbor cancellation.

## 3. Curvature sensitivities with the deficit retained

Set X=pi*U*exp(2U), h_U=4U/(1+2U), and check H/X<1/10.
For r=log q, we have r<0 and |r|<=2.1/a because h_U>=24/13 and h<2.
The elementary inequalities 1+r<=exp(r)<=1+r+r^2/2 for r<=0 give

    |q-(1-h/a)| <= (H+3)/a^2,
    1-q >= d/a, d=h_U-(H+3)/X.                        (2)

The leading q0=1-h/a is also positive and has deficit at least d/a.
Check d>1/2. Both estimates extend to the line segment from q0 to q.

Exact positive-coefficient polynomial comparisons give

    0<ell<=2, |m|<=4.

For example 2(1+2u)^3-16u^2(u+1) and
4(1+2u)^5-16u^3(8u^2+16u+9) have nonnegative coefficients.
Thus, on the corresponding segment of neighboring-parameter derivatives,

    |Lq| <= L*/a^2, L*=2+K/X,
    |Mq| <= M*/a^3, M*=4+M/X.

For the exact curvature expression

    F''=-1/(a+1)^2-q*Mq/(1-q)-q*Lq^2/(1-q)^2,

differentiation now gives the following bounds along the whole segment:

    |partial_q F''| <= [M*/d^2+2(L*)^2/d^3]/a,
    |partial_Lq F''| <= 2L*/d^2,
    |partial_Mq F''| <= a/d.                          (3)

These follow directly from 0<=q<=1 and (2), without replacing d by 1/2.
The leading substitution error can also be bounded more closely. At
(q0,L0,M0)=(1-h/a,ell/a^2,m/a^3), its difference from -N(a) equals

    1/a^2-1/(a+1)^2 + m/a^3 + ell^2/(h*a^3).

Its absolute value is at most (6+4/h_U)/a^3. Combining this with (1)-(3)
gives a uniform reference error C_F/a^3, where

    C_F=[M*/d^2+2(L*)^2/d^3]*(H+3)
              +(2L*/d^2)*K+M/d+6+4/h_U.

As before, N(a)>=4/[(2+1/U)^4*a^2*u^2] and u^2/a decreases. The
relative error for the entire tail is therefore bounded by

    B_reference=[(2+1/U)^4/4]*C_F*U^2/X.

For the true theta integral, retain the previous explicit I/Q error budget
unchanged. Its hypotheses still hold: d>1/2, K/X<1 and M/X<1 imply the
weaker reference bounds used in that transfer, and its three additional
clearance inequalities are checked. No theta summand or spatial tail is
dropped. At U=6 all conditions pass and the combined relative budget is

    B_reference+B_true < 0.468174 < 1.

This proves the asserted uniform strict negativity on the stated tail.

## 4. Replay and limitations

    uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/coefficientwise_curvature.py --output research/certified_xi/coefficientwise_curvature.json
    uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/certified_xi -p 'test_*.py'

Tests check the exact leading derivative bounds, the passing sufficient
conditions, domain rejection, and the individual remainder derivatives
against independent quadrature of the original degree-16 reference at all
three neighboring offsets. They do not prove the missing lower bridge or
uniform head inequalities across every interior shift.

Validation: all 99 certified-Xi tests passed. The artifact's nine source
hashes match and all fourteen sufficient conditions pass. `git diff --check`
passed. No Lean source was changed or rebuilt in this continuation.
