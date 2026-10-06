# A conservative unbounded curvature tail

Update: [explicit Gaussian majorants](RH_EFFECTIVE_GAUSSIAN_TAIL_2026_09_19.md)
now improve the sufficient tail threshold from u=2000 to u=80. The proof
below remains a valid, weaker bound and supplies the algebraic derivation.

## Statement and boundary of the result

Let `I`, `Q_a`, and the frozen-anchor convention be as in
[the common-remainder proof](RH_COMMON_REMAINDER_2026_09_15.md). Define

    c(y)=2y(2y-1)/[(2y+2)(2y+1)],
    q_a(y)=c(y) Q_a(y-1)Q_a(y+1)/Q_a(y)^2,
    F_a(y)=log[(y+1)(1-q_a(y))].

The subscript a is held fixed in every y derivative. Set

    u=W(2a/pi)/2, a=pi*u*exp(2u),
    N(a)=(4u^2+8u+1)/[a^2(1+2u)^4].

**Tail theorem, in ordinary analysis.** For every real anchor with u>=2000,
q_a(a) lies in (0,1), and

    |F_a''(a)+N(a)| <= 10^131 u^100/a^(5/2) < N(a)/2.

The same inequality, with the same deliberately loose constant, holds for
the true curvature obtained by replacing every Q_a with I. Thus both
curvatures are negative on this unbounded tail.

The threshold is a_*=2000*pi*exp(4000). It is deliberately enormous.
This does **not** prove negativity for every anchor a>=10^6, close the
remaining compact bridge, or prove the interior all-rank budget. It is not
an RH proof. The proof below is not Lean formalized; the accompanying code
checks exact algebra and the final elementary tail budget, not every step
of the analytic argument.

## 1. Uniform smallness and the finite polynomial reference

In this note all estimates hold for u>=2000. Put

    A=2a(1+2u)-(9/2)u, L=sqrt(32u),
    lambda=(1+(9/2)u)/sqrt(A),
    b=p_a'''(log u)/(6 A^(3/2)),
    c4=p_a''''(log u)/(24 A^2), beta=3u/(2a).

We have A>=2au, and the centered reference phase is exactly

    P_a(s)=-s^2/2+lambda*s+b*s^3+c4*s^4+r(s).

Here r is the sum of degrees 5 through 16, not an unspecified asymptotic
remainder. For j>=2 its coefficient is

    [(9/2)u-(a/u) T_j(2u)]/[j! A^(j/2)],

where T_j is the Touchard polynomial. Its coefficients are nonnegative,
and their sum B_j satisfies B_j<=j^j<=16^16<2*10^19. Since u>=1,
T_j(2u)<=B_j(2u)^j and |s|/sqrt(A)<=4/sqrt(a). Summing the twelve terms,
using j>=5 in the power of a, gives the generous bound

    sup_|s|<=L |r(s)| <= 10^36 u^16/a^(3/2) = R.

Directly from T_3 and T_4,

    |lambda|, |b| <= 10u/sqrt(a), |c4|<=10u^2/a.

Consequently, with V1=lambda*s+b*s^3 and V2=c4*s^4,

    |V1|<=B1=10^4 u^3/sqrt(a), |V2|<=B2=2*10^4 u^4/a.

All uses of smallness below follow from

    10^70 u^60/sqrt(a) < 10^-100.                         (1)

Indeed sqrt(a)>=exp(u)>=2^u. The logarithmic derivative of u^60/2^u is
60/u-log 2<60/u-1/2<0, and the assertion at 2000 is an exact integer
comparison. It is checked in the replay module. No numerical sampling
is used to extend (1) to larger u.

The amplitude divided by its value at s=0 is

    B(s)=[1-beta*exp(-2u*(exp(s/sqrt(A))-1))]/(1-beta).

Writing h=L/sqrt(A)<=4/sqrt(a), the exponent's absolute value is at most
2u*h*exp(h)<=16u/sqrt(a). Using beta<=2u/a, 1-beta>=1/2, and
exp(d)-1<=2d for 0<=d<=1, we obtain

    |B(s)-1| <= 10^3 u^2/a^(3/2).                         (2)

This bound includes amplitude variation; a constant amplitude alone would
not suffice without estimating its variation.

## 2. A complex Gaussian expansion, with a bounded analytic remainder

Let |z-a|<=sqrt(a)/32, and t=2(z-a)/sqrt(A). Then |t|L<=1/4 and |t|<=1.
Remove the constant scale and the affine factor exp(2(z-a)log u) from Q_a,
and divide by (1-beta)*sqrt(2pi). The resulting function is

    Z(t)=(1/sqrt(2pi)) integral_-L^L
         exp(-s^2/2+t*s) exp(V1+V2+r) B(s) ds.

Compare exp(V1+V2+r)B(s) with W(s)=1+V1+V2+V1^2/2. Its difference has
absolute value at most

    exp(B1+B2+R)*10^3 u^2/a^(3/2)
    +exp(B1+B2)*expm1(R)
    +exp(B1+B2)*(B1+B2)^3/6+B1*B2+B2^2/2.                (3)

The first two terms control the amplitude and r; the last three are the
Taylor remainder of the exponential and the omitted quadratic cross terms.
By (1), (3), and |exp(ts)|<=exp(1/4), the normalized central integral error
is at most 10^40 u^20/a^(3/2).

Replacing the integral of exp(-s^2/2+ts)W(s) over [-L,L] with the full
real line has a similarly bounded error. For each monomial s^k, k<=6,
put T=|t|<=1/(4L); the two tails satisfy

    integral_|s|>=L exp(-s^2/2+T|s|)|s|^k ds
      <=2 exp(-L^2/2+TL)
        sum_(j=0)^k [k!/(k-j)!]*L^(k-j)/(L-T)^(j+1).      (4)

To prove (4), set |s|=L+x, drop -x^2/2, expand (L+x)^k, and integrate
x^j exp(-(L-T)x). Every coefficient of W has modulus <=1 by (1).
The sum of these bounds is at most 10^10 u^4 exp(-16u), hence at most
10^40 u^20/a^(3/2). The latter comparison follows by substituting
a=pi*u*exp(2u), using pi<4, and exp(-13u)<=1.

The Gaussian tilted moments M_j satisfy M_0=1, M_1=t and
M_(j+1)=t*M_j+j*M_(j-1). Integration by parts proves the recurrence;
completion of the square, or analytic continuation from real t, proves

    integral_R exp(-s^2/2+ts)s^j ds=sqrt(2pi)exp(t^2/2)M_j(t).

It follows that

    Z(t)=exp(t^2/2)[1+P1(t)+P2(t)+e(t)],
    P1=lambda*M1+b*M3,
    P2=c4*M4+lambda^2*M2/2+lambda*b*M4+b^2*M6/2,
    |e(t)|<=10^42 u^20/a^(3/2).                          (5)

The error is analytic on the stated disk. The factor exp(t^2/2) has
modulus >=exp(-1/2)>1/2. Also |P1|<=50u/sqrt(a) and
|P2|<=5000u^2/a. These estimates and (1) place |P1+P2+e| below 1/2,
so its logarithm is defined by the convergent power series, without
assuming zero exclusion. The series estimate
|log(1+w)-w+w^2/2|<=2|w|^3 for |w|<=1/2 now gives

    log Z(t)=t^2/2+P1(t)+P2(t)-P1(t)^2/2+E_a(z),
    |E_a(z)|<=10^50 u^50/a^(3/2).                       (6)

Constants independent of z may be retained or removed; they disappear
from all derivatives in the next section. For real |y-a|<=1, the disk
centered at y with radius sqrt(a)/64 stays in the disk used above.
Cauchy's estimate therefore proves, for j=0,...,4,

    |E_a^(j)(y)|<=j!64^j*10^50 u^50/a^((3+j)/2).         (7)

This is the step that justifies differentiating the expansion. No derivative
of an uncontrolled real-axis big-O term has been taken.

## 3. The cancellations and the neighboring-parameter quantities

Polynomial multiplication in (6) gives, apart from its constant term,

    P1+P2-P1^2/2 =
      (lambda+3b)t+(6c4+3lambda*b+18b^2)t^2
      +b*t^3+(c4+(9/2)b^2)t^4.                          (8)

In particular its third derivative at zero is 6b and its fourth derivative
is 24c4+108b^2. Omitting the b^2 term changes the leading curvature and
invalidates the desired cancellation.

Write g_a(y)=log Q_a(y). From (7)-(8), uniformly for |y-a|<=1,

    g_a''(y) = 4/A + O_bound(D0/a^2),
    g_a'''(y) = 8p_a'''(log u)/A^3 + O_bound(D0/a^3),
    g_a''''(y) = 16p_a''''(log u)/A^4
                  +48[p_a'''(log u)]^2/A^5
                  +O_bound(D0/a^(7/2)),                (9)

where D0=10^62 u^50 and O_bound(B) means absolute value at most B.
For explicit accounting: the coefficients of t^2 and t^4 in (8) are
bounded by 10^4u^2/a and 10^3u^2/a; |t(y)|<=2/sqrt(a).
The non-remainder corrections in the first two lines of (9) are bounded
by 10^6u^2/a^2 and 10^6u^2/a^3 respectively. In the last line the
polynomial terms are exact. The largest factor j!64^j in (7) is below
10^9. These facts give (9) with substantial room in D0.

Put v=1+2u, T3=1+6u+4u^2, T4=1+14u+24u^2+8u^3. Exactly,

    p_a'''(log u)=(9/2)u-2a*T3,
    p_a''''(log u)=(9/2)u-2a*T4.

Replacing A by 2av in (9) introduces errors of order a^-2, a^-3,
and a^-4, respectively. Their absolute coefficients are bounded by
10^8u^6: use (9u/2)/(2av)<=2/a and
|(1-r)^(-k)-1|<=2^(k+1)k*r for 0<=r<=1/2, k<=5.

The mass-one tent identity Delta2 g(y)=integral_-1^1(1-|s|)g''(y+s)ds,
and the corresponding identities for g' and g'', preserve the same
bounds. The rational factor c satisfies, at a,

    log c=-2/a+O_bound(100/a^2),
    (log c)'=2/a^2+O_bound(100/a^3),
    (log c)''=-4/a^3+O_bound(100/a^4).

These follow by expanding log(1+r) and (1+r)^(-1), (1+r)^(-2), for
|r|<=1/a; their convergent series tails give the stated constants.
Thus, putting D=10^63u^50, H=log q_a(a), Lq=(log q_a)'(a),
and Mq=(log q_a)''(a), we have

    H=-h/a+O_bound(D/a^2),
    Lq=ell/a^2+O_bound(D/a^3),
    Mq=m/a^3+O_bound(D/a^(7/2)),                          (10)

where

    h=4u/v,
    ell=2-2*T3/v^3=16u^2(u+1)/v^3,
    m=-4-2*T4/v^4+6*T3^2/v^5
      =-16u^3(8u^2+16u+9)/v^5.

For u>=1, 4/3<=h<=2, |ell|<=4, |m|<=32. Equation (1) implies
D/sqrt(a)<10^-100. Consequently q=exp(H) is in (0,1),

    |q-(1-h/a)|<=10D/a^2, 1-q>=1/(2a),
    |Lq|<=5/a^2, |Mq|<=33/a^3.

The exact curvature is

    F_a''(a)=-1/(a+1)^2-q*Mq/(1-q)-q*Lq^2/(1-q)^2.

On the line segment joining the quantities in (10) to
(q0,L0,M0)=(1-h/a,ell/a^2,m/a^3), its partial derivative bounds are
532/a, 40, and 2a, respectively. These follow by differentiating the
last display and using the preceding inequalities. Therefore its error
relative to these leading quantities is at most

    5360D/a^3+2D/a^(5/2).

Replacing the leading expression by a^-2[-1-m/h-ell^2/h^2]
adds at most 100/a^3. Exact polynomial algebra gives

    -1-m/h-ell^2/h^2=-(4u^2+8u+1)/(1+2u)^4.             (11)

In particular the total error is smaller than 10^70 u^50/a^(5/2),
and hence smaller than the much looser bound in the theorem.

## 4. True Xi curvature, final sign, and the remaining gap

For the true I use the already proved
[decaying common-remainder bounds](RH_DECAYING_COMMON_REMAINDER_2026_09_15.md)
with X=10^6. The existing certificate has E_j(X)<1 and u(X)>1.
The scaling formula therefore bounds its orders 2,3,4 by

    10^48 u^16/a^8, 10^51 u^16/a^(17/2), 10^54 u^16/a^9.

By the tent identity these bound the additional errors in H,Lq,Mq.
The q error is at most twice the first bound. The same curvature
sensitivity calculation, slightly widening the deficit bound if needed,
adds less than 10^60 u^16/a^8. Both the reference and true errors thus
fit within 10^131 u^100/a^(5/2).

Since v<=3u and 4u^2+8u+1>=u^2,

    N(a)>=1/(81a^2u^2).

The error-to-margin ratio is at most

    81*10^131*u^102/sqrt(a) <= 81*10^131*u^102/2^u.

Its right side decreases for u>=2000, because 102/u-log 2<0.
At 2000 it is less than 1/2 by an exact rational comparison (see the
JSON artifact). This proves the strict sign for every real anchor on
the stated tail, including the threshold. There is no tail sampling.

The all-anchor statement still requires control below a_*, where this
coarse bound deliberately spends too much error. Sharpening (3)-(7) is
a plausible way to reduce that interval. No part of the proof estimates
cumulative curvature losses as the Toeplitz rank grows; the interior
all-rank budget remains a separate unproved statement.

## Replay and trust boundary

    uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/gaussian_curvature.py --output research/certified_xi/gaussian_curvature.json
    uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/certified_xi -p 'test_*.py'

The implementation verifies (8), the factorizations in (10), (11), and
the exact endpoint comparisons for uniform smallness and the final sign
budget. Analytic integral domination, Cauchy's estimate, and the displayed
inequalities remain a written mathematical proof, not machine verification.

Validation: all 63 certified-Xi unit tests passed, including the four new
Gaussian identity, cubic-square regression, tail budget, and domain tests.
