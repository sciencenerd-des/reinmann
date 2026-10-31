# Pricing a stronger long inverse moment, 24 October 2026

The exact scalar comparison admits **B=874793/1000000=0.874793** if
Liu's long inverse second moment is replaced by the specific hypothesis
below. The unchanged short moments use **kappa=3/4**, justified by the
preceding 7/8 bound. The new B is never used to justify its own moment.

This is a conditional scalar certificate, not a proved arithmetic moment,
new zero-free theorem, external Lean replay or RH result. The DH moment
analogue remains uninstantiated. The proposed moment stays outside the
proved research register. No novelty is claimed: varying the amplification
exponent is explicitly discussed in Liu section 34.3.

## 1. Exact arithmetic hypothesis H(4/5)

Use [Liu 2610.12234v2](https://arxiv.org/html/2610.12234v2), sections 2,
9.1, 29 and 31-32. The source archive SHA-256 remains
`da1db207bb54437245c4fff75f33cfb29088f32f57e6364a6b3b955bc3372204`.

Let K=Q(sqrt(-3)), q_n=N(n), and let n run over integral ideals represented
by the prescribed primary generators. Fix the ray character nu, finite
excluded set S and one sign e in {-1,1}. Retain

    psi_u(n) = nu(n) chi_n(u)^e,
    M_u(D) = D^(-1/2) sum_n mu_K(n) psi_u(n) W(q_n/D).

The powers, including negative powers, are extended by zero on the
noninvertible residue classes. Deleted primes and imprimitive defining
moduli are retained; replacing a presentation by its primitive inducing
character must retain the original coprimality indicator. The same sign,
character presentation and fixed arithmetic data are used throughout the
detectors and selected prime factors.

For D=U^r, **1<=r<=3/2**, the proposed estimate is

    sum_(q_u~U, u sixth-power-free, (u,S)=1) |M_u(U^r)|^2
      << U^(1/5+4r/5+epsilon) (1+T_1)^A.                 H(4/5)

Include all prescribed unit associates. There are no selected prime
factors in this long estimate. It must permit the original admissible
smooth weights, including u-dependent W(y)y^(-sigma_u+it_u), with sigma_u
in a fixed compact interval and |t_u|<=T_1. Constants may depend on the
fixed ray data, compact ranges and finitely many smooth seminorms, as in
the source. The exponent must hold throughout the varying-u family; an
estimate for one fixed conductor is insufficient. No new assertion of
uniform constants over all fixed ray characters is imposed here.

The old bound is U^(1/6)D^(5/6), the proposed bound U^(1/5)D^(4/5).
The gain is **(D/U)^(1/30)**. At r=3/2 this is U^(1/60).
Nothing here establishes that gain.

## 2. A rational certificate through the full comparison

Implementation: [liu_conditional_moment.py](../../experiments/prime_spectral/liu_conditional_moment.py).
Primary exact receipt: [conditional_verified.json](verification_2026_10_24_liu_conditional/conditional_verified.json).

| parameter | exact value |
|---|---:|
| alpha | 4/5 (hypothesis) |
| kappa | 3/4 (preceding 7/8 input) |
| ell | 125621/750000 |
| b | 55363/500000 |
| l_x | 1082669/3000000 |
| l_y | 1414847/3000000 |
| h | 161321/200000 |
| B | 874793/1000000 |

The full direct majorant, including every reflection and Gram positive
part in Liu (22.4)-(22.6), is evaluated. It gives exactly this B;
the reflection exponent is zero. In particular ell<1/5, l_x>b+ell,
l_y>ell+11b/6 and l_x+l_y+ell=1. The principal Euler restriction
B>437/500 is retained. The unchanged direct-side floor 13/15 still
prevents a count-only route to RH.

Put delta=2a-1, x=gbar/delta, c=2/(3kappa), and

    D_c=3-(1+c)x,             P_c=(2-cx)(1-x),
    J=(alpha-delta)D_c+delta P_c,
    t=1+delta P_c/(2J),
    R=1-delta+(alpha-delta)delta P_c/(2J).

Here D_c is a count polynomial, distinct from the inverse length D in
section 1. The short moments and selected-prime restrictions are unchanged:

    r+2z<=1,  2r+8z<=3;       2m+6kappa z<=1.

The code derives the crossing, both balanced counts and cutoff identities
symbolically for general alpha. For r>=1 the long exponent is
1-alpha+(alpha-delta)r. For r<=1 the short inverse and ordinary moments
cross at the same point as in Liu. For 0<=delta<=alpha the decreasing
short count and increasing long count balance at the displayed t.
The independent piecewise affine detector optimizer agrees at all twelve
rational validation classes. This numerical sampling is a regression
check; the identities and monotonicity give the count construction.

All actual zero classes have delta<=3/4+O(class width). The denominator
and cutoff reserves are checked through delta<=19/25<alpha and
x<=51/100. The central endpoint certificate itself covers x<=1/2;
its strict uniform saving and continuity absorb sufficiently small
rounding errors. It does not assert an unrounded endpoint inequality
on the whole enlarged x<=51/100 box.

## 3. Uniform proof of the central endpoint

With y=1/2-x, h=(1+b+3ell)/2 and C0=-1/4+b/6+5ell/4,

    E=C0+(1/2+ell)delta+ell x delta-h(1-R),
    Q=-2JE=-2C0 J+(b+2ell y)delta J-h(alpha-delta)delta P_c.

Write Q=A(y)delta^2+B_q(y)delta+C_q(y). Exact rational arithmetic
checks both identities and the completion of the square

    4A Q = (2A delta+B_q)^2 + (4A C_q-B_q^2).

All four coefficients of A(y) and all five coefficients of the
discriminant complement 4A C_q-B_q^2 are strictly positive. Their
exact values, in increasing powers of y, are in the receipt. In particular
its constant coefficient is

    d0 = 22256173511/1139062500000000 > 0.

Thus Q>0 for every real delta and y>=0. On 0<=delta<=alpha,
0<=x<=1/2, J>0 and the endpoint exponent is uniformly negative.
For Amax=sum_i A_i/2^i, the explicit lower bound is

    -E >= d0/(24 alpha Amax) > 0.00000076229.

This uses A(y)<=Amax and J<=alpha D_c<=3alpha. It is a proof over
the whole rectangle, rather than a mesh of class values.

The full relative nonprincipal exponent at d=h is symbolically checked
against E for every delta,x,R and central contour coordinate. The
moderate-norm slope is between positive 33/50-delta/2 and 2. Consequently
the endpoint controls d<=h. The strict endpoint saving and ell/h>1/5
allow the same small extension past h and the same remote-contour choice
as in Liu's scalar assembly.

## 4. Other norm ranges and losses

Thirty strictly positive fixed-parameter reserves are checked. The
xi/kappa derivative tests from Liu's iterative geometry are inapplicable
because this certificate uses a fixed kappa. They are not reported as
newly verified iteration conditions.

| range or requirement | checked saving or reserve |
|---|---:|
| lowest zero class delta=1/50, trivial R=1 | m_F=0.007152493333... |
| small norms d<=1/100, including previous-bound gap | 0.0757893 |
| intermediate norms, delta=1/50 | m_I=0.212577843333... |
| intermediate norms, delta=19/25 | m_I=0.01676928 |
| ell/h>1/5 | 5ell-h=0.030868333333... |
| principal Euler range | B-437/500=0.000793 |
| room below preceding bound | 7/8-B=0.000207 |

The intermediate saving m_I is affine in delta, so its two endpoint
checks prove it on the entire interval. Its d-slope is positive. The
small-norm saving uses the unchanged estimate R=1 and source quotient-free
Euler bounds. Principal residues and remote-contour exponents are unchanged.
The prime-length bounds remain below 1/5; fixed length decrements give
strict analytic support gaps. Class, smooth-weight and rounding losses
must be chosen after the positive savings, following the source's order.

These are scalar compatibility checks with the existing analytic
estimates. The Mellin continuation construction and its external
formalization have not been reproved or rebuilt in this phase.

The algebraic tangency used to find the rational parameters is

    240 xi^2-475 xi+148=0,
    xi=(475-sqrt(83545))/480=0.38741350102317480288...,
    ell=(5-6xi)/(9+18xi).

Solving E=partial_delta E=0 gives b=0.1107258057716572... and
B_tangent=0.8747921786371273.... This is a tangency diagnostic, not a
claim of global optimality for the modified architecture. The rational
certificate deliberately has a strict margin. With the original alpha=5/6,
its discriminant constant becomes negative and its exponent at the new
critical class is positive: the old moment does not certify the new B.

## 5. Why an arbitrary-coefficient replacement cannot supply this moment

Here is a separate obstruction, not a refutation of H(4/5). Suppose one
replaces the prescribed ideal-Mobius coefficients by *arbitrary bounded
squarefree-supported coefficients*, with a bound uniform in those
coefficients. Fix a member u0 of the family and choose

    a_n = mu_K(n)^2 conjugate(psi_u0(n)).

These coefficients are bounded, supported on squarefree ideals and
independent of the running variable u. They may depend on u0, as a
uniform arbitrary-coefficient assertion would permit. For nonnegative W,

    |D^(-1/2) sum_n a_n psi_u0(n) W(q_n/D)|^2
      = D^(-1) [sum_n mu_K(n)^2 |psi_u0(n)|^2 W(q_n/D)]^2.

This exact finite identity already lower-bounds the whole family moment.
For a smooth W positive on an interval, take u0 to be a growing prime
element outside the fixed excluded set. The bracket is bounded below by
c D for large D. One elementary justification in this class-number-one
quadratic field is the lattice count A(X)=c_K X+O(sqrt(X)) for ideals,
followed by squarefree Mobius inversion; the squarefree count has error
O(sqrt(X) log X). Fixed excluded primes change the positive main constant,
and ideals divisible by u0 number O(D/q_u0). Thus the moment is at least
c' D along this family, for D=U^r and any fixed r>1.

An asserted arbitrary-coefficient bound U^(1-alpha)D^alpha would imply

    U^r << U^(1-alpha+alpha r+epsilon).

This is impossible for alpha<1 after choosing
0<epsilon<(1-alpha)(r-1). The exponent gap is (r-1)/5 for alpha=4/5.
The same obstruction also applies to an arbitrary-coefficient version of
the *original* alpha=5/6 bound. There is no conflict with Liu: its inverse
coefficients are fixed to mu_K, not these aligned coefficients.

Consequently an operator-norm/large-sieve estimate uniform over all
bounded coefficients cannot directly replace the needed long moment.
A successful proof must use the prescribed coefficient structure or
another restriction excluding alignment. This does not rule out using
Guth–Maynard ideas inside a coefficient-sensitive proof, or improving a
simultaneous detector count without proving H(4/5). It does not give a
new RH discriminator.

The existing amplification also cannot be improved by changing a scalar
cutoff alone. With ua^6 in an enlarged norm range H, q_a<=(H/U)^(1/6),
and its cost is at best H/(H/U)^(1/6)=U^(1/6)H^(5/6). The short mean square
needs H>D with a fixed exponent margin. Taking its closure H=D already
gives the old alpha=5/6. The gain above therefore requires a new estimate,
not rebalancing this sixth-power averaging. Replacing six by five would
change the character identity and is not permitted.

## 6. DH gate and reproducibility

The route remains `uninstantiated` and its separating inequality remains
null. The retained DH reciprocal witness
b_91-b_7 b_13=-1-kappa_DH^2 rules out the verbatim ideal-Mobius transfer;
it neither proves H(4/5) nor implements a replacement DH moment family.
The parked row-density analytical route has not been resumed.

Reproduce the scalar receipt and tests with Python 3.12 and SymPy 1.14:

    uv run --with sympy==1.14.0 --python 3.12 python \
      experiments/prime_spectral/liu_conditional_moment.py
    uv run --with sympy==1.14.0 --python 3.12 python -m unittest \
      discover -s experiments/prime_spectral -p 'test_liu*.py' -v
    python3 experiments/prime_spectral/check_dh_research_gate.py

The CLI refuses to overwrite a receipt when --output is supplied.
conditional_verified.json is primary; conditional_certificate.json is an
earlier exploratory output, retained with its original narrower metadata.
The final manifest binds source, report, register snapshots and validation
logs to the actual dirty checkout's base commit. It is not a CI receipt or
proof-chain claim. Earlier manifests remain unchanged and describe earlier
file versions; their pre-edit register/literature bytes are retained here.
The known historical full-round verifier failure was not rerun or repaired
for these scalar changes.

The next mathematical task is proving a coefficient-sensitive estimate
that earns the required saving for the actual inverse polynomials, or a
weaker estimate confined to the simultaneous critical detector class.
The scalar certificate now specifies a payoff and the precise hypothesis
needed; it supplies no evidence that this analytic estimate is true.
