# Effective majorants for the Gaussian curvature tail

Update: [integrated Gaussian errors](RH_INTEGRATED_GAUSSIAN_TAIL_2026_09_19.md)
improve the sufficient threshold to u>=40. This note retains the baseline
majorants and the shared transfer proof.

## Result and scope

The [preceding Gaussian proof](RH_GAUSSIAN_CURVATURE_TAIL_2026_09_19.md)
used intentionally large constants and the threshold u>=2000. This note
replaces those constants by explicit decreasing envelopes. In the same
notation, for every real a with

    u=W(2a/pi)/2 >= 80, equivalently a>=80*pi*exp(160),

both the frozen-reference curvature and true Xi curvature satisfy

    |F''(a)+N(a)| < 0.009502*N(a),
    N(a)=(4u^2+8u+1)/[a^2(1+2u)^4].

Here the reference is frozen when differentiating, as before. This is a
written analytic theorem with rational/ball checks of its explicit
constants; it is not Lean formalized. The lower-anchor bridge and the
interior all-rank budget remain unproved. No RH conclusion follows.

## 1. Endpoint envelopes that apply to the full tail

Fix U>=20 and put X=pi*U*exp(2U). For any subsequent u>=U write
a=pi*u*exp(2u). The basic monotonicity rule is

    d/du log(u^p/a^q) = (p-q)/u-2q.

Every power/exponential envelope below is decreasing for u>=20. Constants
computed at U are held fixed throughout the larger domain. Thus the
endpoint calculation is a sufficient condition for the entire tail,
not an inference from sampled agreement.

For the phase coefficients of degree j>=5 use B_j=sum_k S(j,k) and

    D_j=(5+2^j*B_j)*4^j/j!,
    C_R(U)=sum_(j=5)^16 D_j*(U/sqrt(X))^(j-5).

Indeed, |p_a^(j)(log u)|<=a*(5+2^j*B_j)*u^(j-1), and
L/sqrt(A)<=4/sqrt(a). Since u/sqrt(a) decreases,

    |r(s)|<=C_R(U)*u^4/a^(3/2), |s|<=L.                  (1)

The first four coefficients admit smaller bounds than previously used:

    |lambda|<=4sqrt(u/a), |b|<=3sqrt(u/a), |c4|<=3u/a.

These follow directly from A>=2au and the displayed T_3,T_4 polynomials
in the preceding proof. Therefore

    |V1|<=600u^2/sqrt(a), |V2|<=3072u^3/a.

Let B1=600U^2/sqrt(X), B2=3072U^3/X, and R=C_R*U^4/X^(3/2).
They bound the corresponding quantities uniformly on the tail. Check

    16U/sqrt(X)<1, 2U/X<1/2, 4/sqrt(X)<1/2.             (2)

The amplitude estimate in the preceding proof then remains valid:
|B(s)-1|<=1000u^2/a^(3/2).

## 2. An explicit constant for the analytic log remainder

Write eta=1/4. Dividing the central integral error (equation (3) of the
preceding proof) by u^6/a^(3/2) gives the following uniform upper bound:

    C_c=exp(eta)*[
        exp(B1+B2+R)*(1000/U^4+C_R/U^2)
        +exp(B1+B2)*(600+3072U/sqrt(X))^3/6
        +600*3072/U+3072^2/(2sqrt(X)) ].                 (3)

For example the cubic term uses
|V1|+|V2| <= (u^2/sqrt(a))*(600+3072U/sqrt(X));
the amplitude term uses u^-4<=U^-4. The same reductions give every
term in (3). For the phase term expm1(r)<=exp(R)*r.

For the Gaussian polynomial W, all coefficients have modulus <=1 if

    16sqrt(U/X)+15U/X<1.                               (4)

Using L-T>=L/2 in the Gaussian tail formula, each power L^(k-2j-1)
is at most L^5, since L>=1 and k<=6. The exact integer sum

    sum_(k=0)^6 sum_(j=0)^k [k!/(k-j)!]*2^(j+1) < 10^6

gives the following tail constant, after dividing by u^6/a^(3/2):

    C_t=2exp(eta)*10^6*32^(5/2)*pi^(3/2)*exp(-13U)/U^2.

As in the preceding proof, dividing by exp(t^2/2) costs at most exp(1/2).
Consequently (5) of that proof holds with

    |e(t)|<=C_e*u^6/a^(3/2), C_e=exp(1/2)*(C_c+C_t).

The exact Gaussian moments at |t|<=1 give

    |P1|<=16sqrt(u/a), |P2|<=508u/a.

For the second inequality, bound the four contributions by 30,16,120,
and 342 times u/a, respectively. Define

    p=16sqrt(U/X), s=508U/X, e=C_e U^6/X^(3/2), w=p+s+e.

Require w<1/2. The logarithm power-series tail is bounded by
|w|^3/[3(1-|w|)]. Including the cross terms between P1, P2, and e,
one obtains the uniform analytic remainder bound

    |E_a(z)|<=C*u^6/a^(3/2), |z-a|<=sqrt(a)/32,          (5)

where

    C=C_e*(1+p+s+e/2)+8128/U^(9/2)+508^2/(2U^4sqrt(X))
      +[16+508sqrt(U/X)+C_e U^(11/2)/X]^3
        /[3(1-w)U^(9/2)].                              (6)

For clarity, the terms after C_e in this estimate come from
P1*P2, P1*e, P2^2/2, P2*e, e^2/2 and the logarithm series tail.
All are bounds on one analytic function on one complex disk. Cauchy's
estimate gives, for j<=4 and every |y-a|<=1,

    |E_a^(j)(y)|<=j!64^j C*u^6/a^((3+j)/2).             (7)

## 3. Curvature error with explicit constants

In the exact log polynomial, the coefficients of t^2 and t^4 have
modulus at most 216u/a and 44u/a. With |t(y)|<=2/sqrt(A), the
polynomial corrections to g_a'' and g_a''' are bounded by

    (936+4224/X)/a^2, 4224/(u*a^3),

respectively. There is no polynomial remainder in g_a''''.
For the first bound use 4/A<=2/(au); the term involving b is bounded
by 36sqrt(u)/a inside the bracket, which is <=36u/a. These estimates
are deliberately rounded upward.

The previous proof bounds the replacements A -> 2a(1+2u) by
10^8u^6 times a^-2, a^-3, a^-4 in these three expressions.
For completeness, use r=(9/2)u/[2a(1+2u)]<=2/a and
|(1-r)^(-k)-1|<=2^(k+1)k*r for k<=5. The numerators obey
T3<=11u^2 and T4<=47u^3. The cross term in
[(9/2)u-2a*T3]^2 is bounded by 198au^3+21u^2; together these
bounds are below 10^8u^6 at each of the specified orders.

Apply the mass-one tent identity and the rational c(y) estimates from
the preceding proof. Define

    K_H=100+10^8+10000+2*64^2*C/sqrt(X),
    K_L=100+10^8+4224+6*64^3*C,
    K_M=(100+10^8)/sqrt(X)+24*64^4*C.

Then, uniformly over every anchor in the tail,

    |log q+h/a|<=K_H*u^6/a^2,
    |(log q)'-ell/a^2|<=K_L*u^6/a^3,
    |(log q)''-m/a^3|<=K_M*u^6/a^(7/2),                (8)

with h,ell,m as in the preceding proof. Require

    K_H*U^6/X<1/3, K_L*U^6/X<1, K_M*U^6/sqrt(X)<1.    (9)

These conditions extend uniformly by the monotonicity rule. They imply
log q<=-1/a, 1-q>=1/(2a), |(log q)'|<=5/a^2, and
|(log q)''|<=33/a^3. For K_q=3K_H+10, Taylor's formula also gives

    |q-(1-h/a)|<=K_q*u^6/a^2.

Using the curvature partial derivative bounds 532/a,40,2a from the
preceding proof, and its exact leading cancellation, yields

    |F_a''(a)+N(a)|<=C_F*u^6/a^(5/2),
    C_F=(532K_q+40K_L+100/U^6)/sqrt(X)+2K_M.            (10)

The remaining term 100/a^3 covers replacing the leading rational
curvature expression by exactly -N(a).

## 4. Transfer to the true theta integral and close the whole tail

Use the established common-remainder theorem at X0=10^6. Its E_2,E_3,E_4
are less than 1, and u(X0)>1, so the additional errors in log q and its
first two derivatives are bounded by

    e2=10^48u^16/a^8, e3=10^51u^16/a^(17/2),
    e4=10^54u^16/a^9.

Require, at u=U,

    a*e2<1/12, a^2*e3<1, a^3*e4<1.                   (11)

The same inequalities then hold throughout the tail. The q error is at
most 2e2, so the true deficit stays >=1/(3a); the derivative magnitudes
are at most 6/a^2 and 34/a^3. Thus curvature partial derivative bounds
2250/a,108,3a suffice during this second transfer. The extra curvature
error is less than 10^60u^16/a^8. In the normalization of (10), this adds

    C_I=10^60U^10/X^(11/2).

Since N(a)>=1/(81a^2u^2), both reference and true relative errors are
bounded on the full tail by the single endpoint quantity

    B=81*(C_F+C_I)*U^8/sqrt(X).                        (12)

The last factor decreases for u>=20. A rigorous ball computation at
U=80 satisfies every condition (2),(4),(9),(11), w<1/2, and

    B < 0.009502 < 1/2.

This proves the asserted strict curvature sign for every real anchor in
the tail. Both spatial tails, amplitude variation, common analytic
remainder derivatives, and the omitted theta summands are included.

## Validation and what is still missing

`gaussian_tail_bound.py` implements (1)-(12) with 512-bit FLINT balls and
records exact rational upper bounds. It returns `unresolved` if any
curvature sufficient condition fails; that status is not a counterexample.
The integer sum in the Gaussian tail bound, algebraic identities, domain
rejection, failed budgets, and successful endpoint budgets have tests.

The analytic monotonicity and domination arguments above are written
proofs, not consequences of those tests. No claim of formal verification
is made. This improves the threshold dramatically but still leaves a
large lower-anchor interval. It does not address cumulative losses across
unbounded Toeplitz rank, which remain a separate requirement for RH.

Replay:

    uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/gaussian_tail_bound.py --output research/certified_xi/gaussian_tail_bound.json
    uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/certified_xi -p 'test_*.py'

Validation: all 68 certified-Xi tests passed; `git diff --check` passed.
