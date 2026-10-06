# Uniform curvature on the full common-reference domain

## Theorem and scope

For every real anchor a>=10^6, let Q_a be exactly the frozen degree-16
reference of the [common-remainder construction](RH_COMMON_REMAINDER_2026_09_15.md).
With the anchor fixed, set

    q_a(y)=y(2y-1)/[(y+1)(2y+1)] * Q_a(y-1)Q_a(y+1)/Q_a(y)^2,
    F_a(y)=log[(y+1)(1-q_a(y))],
    u=W(2a/pi)/2,
    N(a)=(4u^2+8u+1)/[a^2(1+2u)^4].

Then 0<q_a(a)<1 and

    |F_a''(a)+N(a)| < 0.229338*N(a).                  (1)

The same bound holds for the true theta curvature, with every Q_a replaced
by the moment integral I. Thus both curvatures are strictly negative for
every a>=10^6, including the endpoint. This closes the previously missing
lower-anchor bridge **within the stated common-reference domain**.

There is no extension here to all smaller positive parameters. The uniform
interior all-rank budget also remains unproved. Neither an RH theorem nor
an all-rank conclusion follows from (1). The argument is written analysis
with FLINT ball verification of constants; it is not Lean formalized.

## 1. Exact absorption of the linear phase

Use A,L,lambda,b,c,d,beta and gamma from
[the cubic expansion](RH_CUBIC_GAUSSIAN_TAIL_2026_09_20.md). The normalized
reference integral is exactly

    Z(t)=1/sqrt(2pi) * integral_-L^L
           exp(-s^2/2+(t+lambda)s)
           exp(b*s^3+c*s^4+d*s^5+r6(s))*B(s) ds.

No phase or amplitude has been changed: lambda*s has simply been included
in the Gaussian tilt. Define w=t+lambda. Since the anchor is fixed,
dw/dy=dt/dy=2/sqrt(A), and all higher derivatives of w vanish.
For every |y-a|<=1, put epsilon=sqrt(u/a) and

    l=9/4+1/(2u), vtilt=l+1/u,
    |w|<=T=epsilon*vtilt.

The inequality follows from |lambda|<=l*epsilon and
|t|<=1/sqrt(au)=epsilon/u. This tilt is larger than the previous bound
on |t| alone, and its full cost exp(TL) is retained below.

After extracting the Gaussian integral exp(w^2/2), the perturbation
polynomials are now

    P1=b*M3(w),
    P2=c*M4(w)+b^2*M6(w)/2,
    P3=d*M5(w)+b*c*M7(w)+b^3*M9(w)/6+gamma*M1(w).

These are the previous expressions with the perturbative linear
coefficient set to zero; the actual linear phase is still in w.
The exact cubic identity specializes to

    P3-P1*P2+P1^3/3=alpha1*w+alpha3*w^3+alpha5*w^5,
    alpha1=135b^3+96b*c+15d+gamma,
    alpha3=144b^3+84b*c+10d,
    alpha5=27b^3+12b*c+d.                              (2)

The second-order log polynomial, apart from its constant, is

    3b*w+b*w^3+(6c+18b^2)w^2+(c+(9/2)b^2)w^4.

All identities are exact. Retaining the Gaussian tilt avoids bounding
the powers of lambda that would otherwise cancel in its logarithm.

## 2. Uniform derivative bounds at the endpoint a=10^6

Set X=10^6 and U=W(2X/pi)/2. A rigorous ball check gives U>5. For any
subsequent anchor a>=X the coordinate u>=U obeys a=pi*u*exp(2u).
Every domination argument used below is valid for u>=5 and a>=10^6:

* A>=4au, beta<1/2, and the amplitude remainder bounds hold as before.
* The individual Touchard coefficient bounds D_j are decreasing.
* Each window term epsilon^(j-2)L^j decreases because
  j/(2u)-(j-2)<0 for j>=3 and u>=5.
* The Gaussian tail summands exp(-12u)*u^p have p<=6, and hence decrease.
* T=epsilon*(9/4+3/(2u)) decreases. Its window product TL also decreases:
  epsilon*sqrt(u) decreases for u>=5 and the remaining factor decreases.

Thus the older sufficient restriction u>=6 is not needed for these
inequalities. The implementation uses the exact rational anchor X, not
a rounded numerical Lambert coordinate, and checks U>5 explicitly.

Use the cubic proof's positive polynomial residual J with precisely the
following substitutions:

    f1=b0*x^3, f2=c0*x^4, f3=D5*x^5,
    f=f1+epsilon*f2+epsilon^2*f3,
    r=sum_(j=6)^16 D_j*epsilon^(j-6)*x^j,
    B=epsilon*f(L), R=epsilon^4*r(L).

Here b0,c0,D_j are the existing positive coefficient bounds. The amplitude
remainder and its gamma*s cross term are unchanged, now multiplying the
nonlinear phase only. Equation (3) of the cubic proof applies verbatim
with this f1. The derivative integrals and both infinite Gaussian tails
receive the larger exp(TL) tilt factor, and T<L/2 is checked anew.

Every nonconstant coefficient of the Gaussian polynomial has modulus at
most one under the checked sufficient condition

    epsilon*b0+epsilon^2*(c0+b0^2/2)
          +epsilon^3*(D5+b0*c0+b0^3/6+3)<1.

The [coefficientwise logarithm proof](RH_COEFFICIENTWISE_CURVATURE_2026_09_20.md)
then applies with

    p(x)=b0*M3(T+x),
    q2(x)=c0*M4(T+x)+b0^2*M6(T+x)/2,
    q3(x)=D5*M5(T+x)+b0*c0*M7(T+x)+b0^3*M9(T+x)/6+3*M1(T+x).

All positive majorants, including the Hermite product terms for
exp(-w^2/2), are evaluated at this T. The constant coefficient of the
logarithm majorant is <1, which proves the requisite local logarithm
branch. Taking coefficients through degree four produces bounds C_j
such that the one common remainder satisfies

    |E_a^(j)(y)|<=j!*C_j*(u/a)^2/(au)^(j/2),
    all a>=10^6, |y-a|<=1 and j=0,...,4.               (3)

Rounded upward, the endpoint constants are

    C0<18.479, C1<42.940, C2<73.505, C3<83.325, C4<90.434.

The coefficientwise geometric-series proof and all endpoint-to-tail
monotonicity arguments remain valid with these substitutions. The scale
and affine factor removed in defining Z contribute no second or higher
logarithmic derivative. This remains the original Q_a.

## 3. Curvature derivatives at the shifted tilt

The polynomial is now evaluated at w=t+lambda, so its derivatives must
not be evaluated at w=0. Put

    s2=6c0+18b0^2, s4=c0+(9/2)b0^2,
    k3=144b0^3+84b0*c0+10D5,
    k5=27b0^3+12b0*c0+D5.

After the chain rule, the polynomial errors beyond the existing leading
second, third and fourth logarithmic derivatives have upper bounds

    [6b0*vtilt+2s2+12s4*T^2]/a^2
       +[6k3*vtilt+20k5*epsilon^2*vtilt^3]*u/a^3,
    [24s4*vtilt+6k3+60k5*T^2]/a^3,
    120k5*vtilt/a^4,

respectively. For example the cubic correction's fourth derivative is
120alpha5*w, bounded after the chain rule by 120k5*vtilt/a^4.
Thus the nonzero shift is accounted for explicitly.

Retain the elementary A_H,A_L,A_M bounds of the cubic proof and the
rational-factor errors 1/a^2, 2/a^3, 6/a^4. Combining them with (3)
and the mass-one tent identity yields

    |log q+h0/a|<=H/a^2,
    |(log q)'-ell/a^2|<=K/a^3,
    |(log q)''-m/a^3|<=M/a^4,

with the usual h0,ell,m and endpoint constants

    H=1+A_H+6b0*vtilt+2s2+12s4*T^2
          +epsilon^2*(6k3*vtilt+20k5*epsilon^2*vtilt^3+2C2),
    K=2+A_L+24s4*vtilt+6k3+60k5*T^2+6C3*epsilon,
    M=6+A_M+120k5*vtilt+24C4.                          (4)

At X=10^6, these are respectively below 7.093, 37.447 and 2321.456.
Every positive term in (4) decreases with u; endpoint bounds therefore
apply to the full anchor interval, not merely to the endpoint.

## 4. Negative reference sign and true-theta transfer

Apply the sharper deficit-sensitive transfer from the coefficientwise
proof with the constants (4). In particular, H/X<1/10 and

    d=4U/(1+2U)-(H+3)/X>1/2,
    L*=2+K/X, M*=4+M/X,
    C_F=[M*/d^2+2(L*)^2/d^3]*(H+3)
                      +(2L*/d^2)*K+M/d+6+4/[4U/(1+2U)].

Then |F_reference''+N|<=C_F/a^3. Since U>5, u^2/a decreases and
N(a)>=4/[(2+1/U)^4*a^2*u^2]. The uniform reference relative budget is

    B_reference=[(2+1/U)^4/4]*C_F*U^2/X <0.229318.

For true I retain the original common I/Q remainder at X0=10^6:

    e_j(a)=E_j(X0)*(u/u(X0))^16*(X0/a)^(7+j/2), j=2,3,4.

The base tail-exponent condition and all three clearance conditions are
checked. The additional uniform relative error is

    B_true=[(2+1/U)^4/4]*U^2
                  *(4500X*e2(X)+108X^2*e3(X)+3X^3*e4(X))
          <0.000020511.

The underlying u^18/a^p envelopes decrease for u>=5 for p=7,6.5,6,
so this still covers every larger anchor. Both original spatial tails
and the full theta-series error are retained through that theorem.
The combined ball computation gives

    B_reference+B_true <0.229338<1.

This proves (1) for the reference and true curvatures on the full stated
domain. No missing lower-anchor interval remains inside a>=10^6.

## Replay and verification boundary

    uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/shifted_gaussian_curvature.py --output research/certified_xi/shifted_gaussian_curvature.json
    uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/certified_xi -p 'test_*.py'

The regression tests integrate the original degree-16 phase, including
its linear term, and compare its logarithm's individual derivatives with
the shifted expansion at all three offsets. A separate check uses the
existing `anchored_moments` routine to verify the H,K,M bounds and the
curvature enclosure at a=10^6. Domain rejection and a larger threshold
are also tested. The uniform theorem relies on the written domination
and monotonicity proof, not on these sampled regression checks.

Parameters below 10^6 and uniform compatible heads across all interior
shifts remain unproved. In particular the all-rank rank-recurrence budget
does not follow from this rank-two curvature theorem.

Validation: all 102 certified-Xi tests passed. The certificate's nine source
hashes match and all fifteen sufficient conditions pass. `git diff --check`
passed. No Lean source was changed or rebuilt in this continuation.
