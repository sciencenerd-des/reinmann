# Cubic cancellation and a fourth-order common remainder

Update: [coefficientwise derivative accounting](RH_COEFFICIENTWISE_CURVATURE_2026_09_20.md)
and sharper curvature sensitivities lower the sufficient threshold to u>=6.
The expansion and u>=7 result below remain valid.

## Result and scope

For every real anchor with

    u=W(2a/pi)/2 >= 7, equivalently a>=7*pi*exp(14),

both the frozen degree-16 reference curvature and the true theta curvature
satisfy

    |F''(a)+N(a)| < 0.742183*N(a),
    N(a)=(4u^2+8u+1)/[a^2(1+2u)^4].

In particular both are strictly negative throughout that tail. This lowers
the preceding sufficient threshold from u=14 to u=7, approximately
a=2.645e7. It does not prove the lower-anchor bridge or the interior
all-rank budget. In the domain of the common-reference theorem, the
remaining bridge is 10^6<=a<7*pi*exp(14). No new conclusion is made for
smaller parameters. This is a written analytic argument with certified
constant evaluation, not a Lean proof or an RH proof.

The improvement retains the entire third-order correction before bounding
the error. Its logarithm is an odd polynomial of degree five: the terms
of degrees seven and nine cancel exactly. Consequently its fourth
derivative vanishes at the center and is small at neighboring parameters.
The leftover common remainder is fourth order, rather than third order,
in epsilon=sqrt(u/a).

## 1. Exact Gaussian logarithm identity

Keep the notation and normalization of the
[direct-derivative proof](RH_GAUSSIAN_JET_TAIL_2026_09_20.md).
The anchor is fixed in every parameter derivative. Let

    V1=lambda*s+b*s^3, V2=c*s^4, V3=d*s^5,
    r6=sum_(j=6)^16 phase_j*s^j,
    gamma=beta*2u/[sqrt(A)*(1-beta)], beta=3u/(2a).

Here c and d are the actual quartic and quintic coefficients of the frozen
phase, not merely upper bounds. Define the third-order integrand polynomial

    W3=1+V1+V2+V1^2/2+V3+V1*V2+V1^3/6+gamma*s.

Let M_j(t) be the Gaussian tilted moment polynomials, so that integration
of s^j against exp(-s^2/2+ts)/sqrt(2pi) gives exp(t^2/2)M_j(t).
In addition to the existing P1 and P2, define

    P3=(d+lambda*c)M5+b*c*M7+lambda^3*M3/6
            +lambda^2*b*M5/2+lambda*b^2*M7/2+b^3*M9/6+gamma*M1.

Exact polynomial algebra gives

    P3-P1*P2+P1^3/3 = alpha1*t+alpha3*t^3+alpha5*t^5,
    alpha1=3lambda^2*b+36lambda*b^2+12lambda*c
                   +135b^3+96b*c+15d+gamma,
    alpha3=18lambda*b^2+4lambda*c+144b^3+84b*c+10d,
    alpha5=27b^3+12b*c+d.                              (1)

`cubic_identity()` checks (1) in an exact rational multivariate polynomial
ring. This is not a numerical near-cancellation. The amplitude's linear
term gamma appears only in alpha1 and therefore contributes zero to every
derivative of order two or higher in (1).

## 2. A bound for the actual amplitude remainder

Fix U>=6, u>=U, a=pi*u*exp(2u), epsilon=sqrt(u/a),
L=sqrt(32u), T=1/sqrt(au), h=sqrt(8/a). We have A>=4au and
|t|<=T at every real |y-a|<=1.

For |s|<=L set x=2u*(exp(s/sqrt(A))-1), x1=2u*s/sqrt(A).
The normalized amplitude is

    B(s)=1+beta/(1-beta)*(1-exp(-x)).

Since beta<1/2, the following bounds follow from the exponential Taylor
remainder and A>=4au:

    |gamma|<=3epsilon^3,
    |x|<=epsilon*exp(h)*|s|,
    |x-x1|<=exp(h)*s^2/(4a),
    |B(s)-1-gamma*s|<=B0*epsilon^4*s^2,
    B0=3[exp(h)/(4u)+exp(2h)*exp(epsilon*exp(h)*L)/2].   (2)

Thus the amplitude is expanded with an explicit remainder, rather than
dropped or differentiated as an uncontrolled approximation.

## 3. Positive polynomial bounds for four residual derivatives

Use l,b0,c0,D_j from the preceding direct-derivative proof, with d0=D_5.
They give |lambda|<=l*epsilon, |b|<=b0*epsilon,
|c|<=c0*epsilon^2, |d|<=d0*epsilon^3. Introduce positive-coefficient
polynomials in x>=0:

    f1=l*x+b0*x^3, f2=c0*x^4, f3=d0*x^5,
    f=f1+epsilon*f2+epsilon^2*f3,
    r=sum_(j=6)^16 D_j*epsilon^(j-6)*x^j,
    B=epsilon*f(L), R=epsilon^4*r(L), v=f2+epsilon*f3.

The absolute difference between the actual normalized integrand factor
exp(V1+V2+V3+r6)B(s) and W3(s), divided by epsilon^4, is at most
the following positive polynomial evaluated at x=|s|:

    J(x)=exp(B+R)*[r+B0*x^2+3x*(f+epsilon^3*r)]
        +exp(B)*f^4/24
        +f1*f3+f2^2/2+epsilon*f2*f3+epsilon^2*f3^2/2
        +f1^2*v/2+epsilon*f1*v^2/2+epsilon^2*v^3/6.     (3)

For completeness, the first line bounds r6, the remainder in (2), and
gamma*s*(exp(V1+V2+V3+r6)-1). The second line is the fourth-and-higher
exponential Taylor remainder. The last two lines are all omitted terms
in the quadratic and cubic exponential polynomials. No signed term in
these remainders is discarded. The maximum degree of J is twenty.

Write the normalized integral as

    Z(t)=exp(t^2/2)*(1+P1+P2+P3)+D(t).

Differentiating this one residual under its integral inserts s^k. The
central contribution to |D^(k)|/epsilon^4 is at most

    exp(TL)*E[J(|G|)*|G|^k], k=0,...,4,

where G is standard normal; absolute moments through order 24 suffice.
The differentiation and domination arguments are the same as those of
the preceding proof, with the explicit polynomial (3).

The constant coefficient of W3 is one. Check that the sum of the absolute
majorants for its nonconstant coefficients is less than one; explicitly,

    epsilon*(l+b0)+epsilon^2*[c0+(l+b0)^2/2]
       +epsilon^3*[d0+(l+b0)c0+(l+b0)^3/6+3] < 1.       (4)

Then every coefficient has modulus at most one, and W3 has degree nine.
The two infinite Gaussian tails, after division by epsilon^4, contribute
at most

    exp(TL)*2*pi^2*exp(-12u)
        *sum_(n=k)^(k+9) sum_(j=0)^n
             [n!/(n-j)!]*2^(j+1)*L^(n-2j-1).           (5)

This follows from the same tangent-tail integration as before, now using
epsilon^-4=pi^2 exp(4u), and T<L/2. Again the factor 1/sqrt(2pi)<1 is
dropped only to enlarge the bound. Let d_k be the sum of these central
and tail constants. Thus |D^(k)|<=d_k*epsilon^4 for k=0,...,4.

All endpoint constants bound the entire tail u>=U. The coefficients D_j,
l,b0,c0,epsilon,h,T decrease. Each term of B and R has logarithmic
derivative at most j/(2u)-(j-2)<0. The exponential in B0 decreases as
well. Every summand in (5) is proportional to exp(-12u)*u^p with p<=6,
which decreases for u>=6. All expressions have nonnegative coefficients.

## 4. Fourth-order logarithm error in a common Taylor jet

At a real t use ||f||_4=sum_(k=0)^4 |f^(k)(t)|/k!. Its
submultiplicativity was proved in the preceding note. For
e=exp(-t^2/2)D, the product rule gives

    ||e||_4<=C_e*epsilon^4,
    C_e=sum_(k=0)^4 sum_(i=0)^k M_i(T)*d_(k-i)/(i!*(k-i)!).

Here M_i(T) bounds the absolute Hermite polynomial, as before.
Positive moment polynomials at 1+T give bounds

    ||P1||_4<=p*epsilon, ||P2||_4<=q2*epsilon^2,
    ||P3||_4<=q3*epsilon^3,

where p,q2 are the preceding expressions, and

    q3=(d0+l*c0)M5+b0*c0*M7+l^3*M3/6
           +l^2*b0*M5/2+l*b0^2*M7/2+b0^3*M9/6+3M1,

with every M evaluated at 1+T. Put

    w=p*epsilon+q2*epsilon^2+q3*epsilon^3+C_e*epsilon^4,
    v0=q2+q3*epsilon+C_e*epsilon^2.

Check w<1. Subtract the logarithm polynomial through cubic order and
define the actual common remainder

    E=log(1+P1+P2+P3+e)
          -[P1+P2-P1^2/2+P3-P1*P2+P1^3/3].

The logarithm series and the submultiplicative jet norm yield

    ||E||_4<=C*epsilon^4,
    C=C_e+p*(q3+C_e*epsilon)+v0^2/2+p^2*v0
        +p*epsilon*v0^2+epsilon^2*v0^3/3
        +(p+q2*epsilon+q3*epsilon^2+C_e*epsilon^3)^4/[4(1-w)].   (6)

One can check (6) by writing A=P1 and D=P2+P3+e. The remaining quadratic
terms are -A(P3+e)-D^2/2, and the remaining cubic terms are
A^2D+AD^2+D^3/3. The fourth-and-higher logarithm tail costs at most
w^4/[4(1-w)]. The linear residual is e. This accounts for every term.

**Derivative theorem.** Freeze C at U. For every u>=U, |y-a|<=1,
and j=0,...,4,

    |E_a^(j)(y)|<=j!*C*(u/a)^2/(a*u)^(j/2).            (7)

The chain-rule factor is (2/sqrt(A))^j<=1/(au)^(j/2).
The logarithm branch is justified locally by w<1 and agrees with the
positive real integral. All derivatives in (7) belong to the same fixed
anchor. The estimate does not identify the moving and frozen references.

## 5. Smaller elementary curvature-transfer constants

To avoid losing the benefit of (7), retain the parameter dependence in
the elementary corrections. Write X=pi*U*exp(2U), v=1+2u, and freeze
all upper-bound constants below at U. The rational coefficient factor
of q is a(a-1/2)/[(a+1)(a+1/2)]. For a>=16, its logarithm and first two
derivatives differ from -2/a, 2/a^2, -4/a^3 by at most

    1/a^2, 2/a^3, 6/a^4, respectively.                 (8)

For the first bound, sum the three logarithm series remainders to obtain
3/[4a^2(1-1/a)]. For the second use the reciprocal remainder to obtain
3/[2a^3(1-1/a)]. For the third use
(1+x)^(-2)-1+2x=x^2(3+2x)/(1+x)^2, yielding at most
3(3+2/a)/[2a^4(1-1/a)^2]. These imply (8) on the asserted domain.

For the replacement A -> A*=2av, r=(9/2)u/A*<=9/(8a)<1/1000.
For 1<=k<=5 we have (1-r)^(-k)<=2 and
(1-r)^(-k)-1<=(k+1)r. The latter follows from the mean value theorem
and (1000/999)^6<6/5<=(k+1)/k. Explicit expansion, including the
cross terms in p3^2, now gives replacement errors bounded by
A_H/a^2, A_L/a^3 and A_M/a^4, where

    A_H=9/(4U),
    A_L=9*(4+7/U+1/U^2)/(8U),
    A_M=(45/4)*(8+24/U+14/U^2+1/U^3)/(16U)+9/(16U^3)
          +(81/2)*(4+6/U+1/U^2)^2/(32U)
          +54*(4+6/U+1/U^2)/(32U^2)+243/(128XU^3).

For the second expression the two terms before replacing v by 2u are
9T3/v^3 and 9u/v^3. For the third they are
(45/4)T4/v^4, 9u/v^4, (81/2)T3^2/v^5,
54uT3/v^5 and (243/4)u^2/(a*v^5). Thus the displayed upper bounds
follow by positive coefficients and v>=2u.

Let l,b0,c0,d0 refer to the majorants at U and put

    s2=6c0+3l*b0+18b0^2, s4=c0+(9/2)b0^2,
    k3=18l*b0^2+4l*c0+144b0^3+84b0*c0+10d0,
    k5=27b0^3+12b0*c0+d0, T0^2=1/(XU).

In the second-order logarithm polynomial, s2 and s4 bound the t^2
and t^4 coefficients after division by epsilon^2. In the third-order
polynomial (1), k3 and k5 bound alpha3/epsilon^3 and alpha5/epsilon^3.
Consequently the polynomial contributions beyond the earlier leading
derivatives, (7), (8), and the replacement estimates give

    |log q+h0/a|<=H/a^2,
    |(log q)'-ell/a^2|<=K/a^3,
    |(log q)''-m/a^3|<=M/a^4,

with h0,ell,m as in the preceding proof and

    H=1+A_H+2s2+6b0/U+12s4*T0^2
           +(6k3+20k5*T0^2+2CU)/X,
    K=2+A_L+24s4/U+6k3+60k5*T0^2+6C*sqrt(U/X),
    M=6+A_M+120k5/U+24C.                              (9)

For example, the fourth derivative of (1) is 120alpha5*t. After the
parameter chain rule its bound is 120k5/(u*a^4). The remainder's
fourth derivative is bounded by 24C/a^4. These are the two terms whose
order improves over the preceding argument. The mass-one tent identity
then bounds second differences without separately bounding the neighbors.

Check H/X<1/3, K/X<1 and M/X<1. The same curvature sensitivity proof,
including the exact leading cancellation, gives

    |F_reference''+N|<=C_F/a^3,
    C_F=532*(3H+10)+40K+2M+100,
    B_reference=[(2+1/U)^4/4]*C_F*U^2/X.               (10)

Because u^2/a decreases for u>=6, (10) is a uniform relative bound.

For the true theta integral retain the same certified common I/Q
derivative errors e2,e3,e4 and all their clearance conditions from the
preceding proof. Their additional relative budget is unchanged:

    B_true=[(2+1/U)^4/4]*U^2
                  *(4500X*e2(X)+108X^2*e3(X)+3X^3*e4(X)).

This includes the full theta series and both outer spatial tails via that
earlier theorem. The power-decay hypothesis is checked against its saved
analytic constants, and each error envelope decreases on the tail.

At U=7 every sufficient condition passes and
B_reference+B_true<0.742183<1. A factor of one half is unnecessary for
strict negativity: an error strictly smaller than N already suffices.
At U=8 the budget is below 0.097409. At U=6 this particular bound exceeds
one and is classified as unresolved, not as positive curvature.

## 6. Replay and validation boundary

    uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/cubic_gaussian_tail.py --output research/certified_xi/cubic_gaussian_tail.json
    uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/certified_xi -p 'test_*.py'

Tests verify the exact polynomial identity and independently integrate
the original degree-16 reference and its first four tilt derivatives at
U=6 and offsets -1,0,1. A Taylor-series logarithm of those integrals is
compared with the fourth-order residual estimate (7). Additional checks
cover elementary denominator/remainder bounds and passing/failing domain
classification. These checks validate implementation; they do not replace
the written continuum domination and monotonicity argument.

The lower-anchor bridge and the all-shift head inequalities required by
the interior all-rank recurrence remain open. No finite test or tail
curvature result is promoted to an all-rank or RH assertion.

Validation: all 95 certified-Xi tests passed; the certificate's eight source
hashes match and all thirteen sufficient conditions pass. `git diff --check`
passed. No Lean source was changed or rebuilt in this continuation.
