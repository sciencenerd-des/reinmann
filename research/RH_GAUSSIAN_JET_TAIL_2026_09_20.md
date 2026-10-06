# Direct derivatives of the common Gaussian remainder

Update: the [cubic cancellation argument](RH_CUBIC_GAUSSIAN_TAIL_2026_09_20.md)
retains the next logarithm polynomial and lowers the sufficient threshold
to u>=7. The u>=14 theorem below remains valid and supplies the jet method.

## Result and exact scope

For the same degree-16 frozen reference Q_a and true theta integral I as in
[the common-remainder construction](RH_COMMON_REMAINDER_2026_09_15.md), the
reference and true curvatures are strictly negative for every real anchor

    u=W(2a/pi)/2 >= 14, equivalently a>=14*pi*exp(28).

More precisely, with N(a)=(4u^2+8u+1)/[a^2(1+2u)^4], both satisfy

    |F''(a)+N(a)| < 0.274447*N(a).

The previous sufficient threshold was u=40. This improvement comes from
bounding derivatives under one common integral, followed by logarithm
algebra in a finite Taylor-jet norm. It does not follow from point samples.
The proof is ordinary analysis with explicit FLINT ball checks of constants;
it is not Lean formalized. The interval 10^6<=a<14*pi*exp(28) is **not**
closed by this theorem. Uniform all-anchor negativity and the interior
all-rank budget remain unproved. In particular this is not an RH proof.

## 1. A sharper phase scale

Use the definitions A, L, lambda, b, c4, beta and Z(t) from
[the Gaussian expansion](RH_GAUSSIAN_CURVATURE_TAIL_2026_09_19.md).
Throughout this note U>=6, u>=U, a=pi*u*exp(2u), and

    epsilon=sqrt(u/a), L=sqrt(32u), A=2a(1+2u)-(9/2)u.

Then a>10^6, A>=4au, beta=3epsilon^2/2, and the neighboring real
parameters |y-a|<=1 give |t|=|2(y-a)/sqrt(A)|<=T=1/sqrt(au).
The positive majorants

    l(u)=9/4+1/(2u),
    b0(u)=(4+6/u+1/u^2)/24,
    c0(u)=(8+24/u+14/u^2+1/u^3)/192

satisfy |lambda|<=l*epsilon, |b|<=b0*epsilon,
|c4|<=c0*epsilon^2. For j>=5 define

    D_j(u)=sum_(k=0)^j S(j,k)*2^(k-j)*u^(k-j)/j!.

The degree-j phase coefficient has absolute value <=D_j epsilon^(j-2).
Indeed its numerator is (9/2)u-(a/u)T_j(2u)<0, and dropping the
positive (9/2)u before taking the absolute value gives the bound using
A>=4au. Each D_j is decreasing. We retain the individual Touchard
coefficients instead of bounding their sum by a Bell number.

Set V1=lambda*s+b*s^3, V2=c4*s^4 and r=sum_(j=5)^16 phase_j*s^j.
Uniform window majorants are

    B1=epsilon*(l*L+b0*L^3), B2=c0*epsilon^2*L^4,
    R=sum_(j=5)^16 D_j*epsilon^(j-2)*L^j.

For the normalized amplitude B(s) of the preceding proof, put
h=sqrt(8/a). Since L/sqrt(A)<=h and beta<1/2,

    |B(s)-1| <= A0*epsilon^3*|s|,
    A0=3 exp(h) exp(epsilon*exp(h)*L).

This follows from |exp(s/sqrt(A))-1|<=exp(h)|s|/sqrt(A),
beta/(1-beta)<=3epsilon^2, and |exp(x)-1|<=|x|exp(|x|).
The amplitude is still present; it has not been replaced by a constant.

## 2. Derivative bounds before taking the logarithm

Let W=1+V1+V2+V1^2/2 and let m_k be the absolute standard Gaussian
moments, m_0=1, m_1=sqrt(2/pi), m_(k+2)=(k+1)m_k.
Write

    Z(t)=exp(t^2/2)*(1+P1(t)+P2(t))+D(t).

Here P1 and P2 are exactly those of the previous Gaussian expansion.
There is only one residual D(t). Differentiation inserts s^k into its
integrals, including the subtracted infinite Gaussian tails. Dominated
differentiation is justified by Gaussian decay and the finite central
window. For k=0,...,4 the central contribution to |D^(k)|/epsilon^3
is bounded by exp(eta)*C_k, eta=T*L, where

    J(s)=l*s+b0*s^3+c0*epsilon*s^4,
    C_k=exp(B1+B2+R)*(A0*m_(k+1)
             +sum_(j=5)^16 D_j*epsilon^(j-5)*m_(j+k))
        +exp(B1+B2)*E[J(|G|)^3*|G|^k]/6
        +c0*(l*m_(k+5)+b0*m_(k+7))
        +c0^2*epsilon*m_(k+8)/2.

This is the exponential Taylor remainder through quadratic order,
integrated against the Gaussian; the last two lines include V1*V2
and V2^2/2. The tilt on the central interval costs exp(eta).

Check that every nonconstant coefficient of W has modulus at most one;
the code uses the stronger sufficient condition that the sum of their
absolute majorants is <1. Its constant coefficient is exactly one.
If T<L/2, both infinite tails contribute at most

    exp(eta)*2*pi^(3/2)*exp(-13u)
       *sum_(n=k)^(k+6) sum_(j=0)^n
            [n!/(n-j)!]*2^(j+1)*L^(n-2j-1)

to |D^(k)|/epsilon^3. To see this, use s=L+x on each tail,
drop -x^2/2, expand (L+x)^n, and integrate against exp(-(L-T)x).
Then use L-T>=L/2 and epsilon^-3=pi^(3/2)exp(3u).
Dropping the common factor 1/sqrt(2pi)<1 enlarges the bound.
Denote the combined central and tail constant by d_k.

Every quantity used here can be bounded at U for the entire tail.
In particular epsilon=pi^-1/2 exp(-u), and
epsilon^(j-2)L^j decreases because j/(2u)-(j-2)<0.
Each tail summand has the form a positive constant times
exp(-13u)*u^p with p<5, hence decreases for u>=6, including terms
with negative p. The other factors are positive decreasing functions.

## 3. Finite Taylor-jet algebra preserves common-error cancellation

At a fixed real t define

    ||f||_4=sum_(k=0)^4 |f^(k)(t)|/k!.

The product rule proves ||fg||_4<=||f||_4||g||_4: the left hand side
uses only terms with combined degree at most four. Thus ordinary
convergent power-series estimates apply to these truncated Taylor jets.
This is an algebraic norm estimate, not a Cauchy-disk estimate.

Put e(t)=exp(-t^2/2)D(t). If H_k^+(T) is the polynomial with absolute
coefficients of the kth probabilists' Hermite polynomial, then
|(d/dt)^k exp(-t^2/2)|<=H_k^+(T) for real |t|<=T. Therefore

    ||e||_4 <= C_e*epsilon^3,
    C_e=sum_(k=0)^4 sum_(i=0)^k H_i^+(T)*d_(k-i)/(i!*(k-i)!).

The positive polynomials H_k^+ obey M_0=1, M_1=x,
M_(k+1)=x*M_k+k*M_(k-1). These are also the Gaussian tilted moment
polynomials. Evaluating them at 1+T bounds the sum of the absolute
Taylor coefficients of each M_k at |t|<=T, including all degrees.
Consequently

    ||P1||_4<=p*epsilon,
    p=l*M_1(1+T)+b0*M_3(1+T),
    ||P2||_4<=s0*epsilon^2,
    s0=c0*M_4(1+T)+l^2*M_2(1+T)/2
           +l*b0*M_4(1+T)+b0^2*M_6(1+T)/2.

Check w=p*epsilon+s0*epsilon^2+C_e*epsilon^3<1. This also ensures
the scalar logarithm has its correct analytic branch locally at each
real t. Set

    E=log(1+P1+P2+e)-P1-P2+P1^2/2.

Writing the logarithm series through degree two, preserving the P1^2
cancellation exactly, and bounding its remaining terms in the jet norm
gives ||E||_4<=C*epsilon^3, where

    C=C_e+p*(s0+C_e*epsilon)+epsilon*(s0+C_e*epsilon)^2/2
         +(p+s0*epsilon+C_e*epsilon^2)^3/[3(1-w)].

The infinite series bound uses 1/n<=1/3 for n>=3; it controls derivatives
as well as values because the jet norm is submultiplicative. Its constants
decrease with u, so evaluating C at U is sufficient for all larger u.

**Common derivative theorem.** Holding the anchor fixed, for j=0,...,4,

    |E_a^(j)(y)| <= j!*C*(u/a)^(3/2)/(a*u)^(j/2),
    every u>=U and every real |y-a|<=1.                 (1)

The factor (2/sqrt(A))^j comes from the affine tilt t=2(y-a)/sqrt(A).
This establishes derivatives of one remainder shared by the neighbors.
It does not differentiate a real-axis big-O assertion or the moving anchor.

For the underlying differentiation-under-the-integral principle see
[DLMF 1.10](https://dlmf.nist.gov/1.10); the actual dominating functions
and explicit constants needed here are displayed above.

## 4. Transfer into curvature without unnecessary powers of u

The exact Gaussian logarithm polynomial from the previous proof is
unchanged, including its cubic-square term. Its non-remainder corrections
to g_a'' and g_a''' are bounded by 10000/a^2 and 4224/(u*a^3).
Its fourth derivative is exact before adding E_a''''.

Here are sharper bounds for replacing A by A*=2a(1+2u). Write v=1+2u,
T3=1+6u+4u^2, T4=1+14u+24u^2+8u^3 and r=(9/2)u/A*<=2/a.
Use (1-r)^(-k)-1<=2^(k+1)*k*r for k<=5 and r<=1/2,
together with T3<=2v^2 and T4<=6v^3. Then

    |4/A-2/(a*v)| <= 4/a^2,
    |8p3/A^3+2T3/(a^2*v^3)| <= 250/a^3,
    |16p4/A^4+48p3^2/A^5
           +2T4/(a^3*v^4)-6T3^2/(a^3*v^5)| <= 10000/a^4.

For explicit bookkeeping the second bound costs at most
(192/u+4.5/u^2)/a^3. The third costs at most
(1536/u+4.5/u^3+7680/u+216/u^2+30.375/(a*u^3))/a^4,
which is below 10000/a^4 for u>=1,a>=1. These estimates include
both denominator perturbations and the cross terms in p3^2.

Let X=pi*U*exp(2U) and freeze C at U. Applying (1), the rational-factor
bounds from the preceding proof, and the mass-one tent identity gives

    |log q+h0/a| <= H/a^2,             H=10104+2C*sqrt(U/X),
    |(log q)'-ell/a^2| <= K/a^3,       K=4574+6C,
    |(log q)''-m/a^3| <= M/a^(7/2),    M=10100/sqrt(X)+24C/sqrt(U).

Here h0=4u/v, ell=16u^2(u+1)/v^3, m=-16u^3(8u^2+16u+9)/v^5.
The tent identity takes the second difference before bounding it;
affine terms cancel. Check H/X<1/3, K/X<1, M/sqrt(X)<1.
The same deficit and curvature sensitivity bounds as before now yield

    |F_reference''+N| <= C_F/a^(5/2),
    C_F=[532*(3H+10)+40K+100]/sqrt(X)+2M.

Since N>=4/[(2+1/U)^4*a^2*u^2], the relative reference budget is

    B_reference=[(2+1/U)^4/4]*C_F*U^2/sqrt(X).         (2)

The factor u^2/sqrt(a) decreases for u>=6, so (2) bounds the whole tail.

For true I, retain the certified E_j(10^6) from the existing common
I/Q remainder theorem rather than replacing them by one. For j=2,3,4,

    e_j(a)=E_j(10^6)*(u/u(10^6))^16*(10^6/a)^(7+j/2).

The implementation checks that the base saddle exponent lies in [7/16,1/2],
as required by that power-decay theorem, and checks X*e2<1/12,
X^2*e3<1, X^3*e4<1. Curvature partial-derivative bounds then give

    B_true=[(2+1/U)^4/4]*U^2
                *(4500X*e2(X)+108X^2*e3(X)+3X^3*e4(X)).       (3)

Each underlying term is proportional to u^18/a^p for p=7,6.5,6.
Its logarithmic derivative (18-p)/u-2p is negative for u>=6.
Thus (3) includes the omitted theta summands and both spatial tails
uniformly, by the earlier common-remainder theorem.

At U=14 all conditions pass and B_reference+B_true<0.274447<1/2.
This proves the claimed strict tail sign. At U=6 the same sufficient
budget exceeds one: it is unresolved, not evidence of positive curvature.

## 5. Validation and unresolved obligations

The new tests independently integrate Z and its first four tilt derivatives
at U=6 and all three neighboring offsets. Taking the resulting Taylor-series
logarithm checks the common-jet bound against direct FLINT quadrature.
Additional tests check exact polynomial majorants, denominator-replacement
regressions, a passing tail, an unresolved lower threshold, and invalid input.
These tests validate implementation details; the continuum assertion relies
on the written domination and monotonicity proof above.

Replay:

    uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/gaussian_jet_bound.py --output research/certified_xi/gaussian_jet_tail.json
    uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/certified_xi -p 'test_*.py'

The saved certificate records exact rational upper bounds and source hashes.
This theorem does not supply a compatible head region at every shift for
the rank recurrence. Boundary theorems for shifts one and two remain
separate. A proof of all-anchor curvature alone would still leave the
interior all-rank argument outstanding.

Validation: all 91 certified-Xi tests passed. The saved certificate's seven
source hashes match the files used in the calculation; `git diff --check`
passed. No Lean sources were changed or rebuilt in this continuation.
