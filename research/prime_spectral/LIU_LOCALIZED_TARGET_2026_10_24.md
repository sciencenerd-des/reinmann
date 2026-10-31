# Localized arithmetic targets for Liu's comparison

The conditional B=0.874793 comparison can be reduced to **either** of two
unproved arithmetic inputs:

1. The improved long inverse moment only for **1.099<=r<=1.19**, with
   D=U^r, rather than the full 1<=r<=1.5 range used in phase 2.
2. An additive **1/850 saving in the character-count exponent**, only on
   **1/3<=delta<=47/100, 21/50<=x<=1/2**.

The original count suffices outside that class rectangle. This statement
is proved here by exact scalar inequalities. Neither new arithmetic input
is proved, neither is a transported Guth–Maynard theorem, and neither has
an instantiated DH replacement. No new zero-free theorem, RH result or
novelty is claimed. The two alternatives are not asserted to imply one
another. The register was updated before development.

## Conventions and inputs

Retain the rational geometry and all thirty auxiliary reserves from the
[conditional moment note](LIU_CONDITIONAL_MOMENT_2026_10_24.md):

    kappa=3/4, ell=125621/750000, b=55363/500000,
    l_x=1082669/3000000, l_y=1414847/3000000,
    h=161321/200000, B=874793/1000000.

The preceding 7/8 bound supplies kappa=3/4. The full direct majorant and
principal Euler restriction are unchanged. Write alpha_0=5/6 for the
original long inverse exponent and alpha_1=4/5 for the hypothetical one.

All arithmetic conventions are those of [Liu v2](https://arxiv.org/html/2610.12234v2),
sections 2, 5, 9, 10, 29 and 31-32. In K=Q(sqrt(-3)), q_n is ideal norm;

    M_u(D)=D^(-1/2) sum_n mu_K(n) psi_u(n) W(q_n/D),
    psi_u(n)=nu(n) chi_n(u)^e,   e in {-1,1} fixed.

Retain primary generators, original zero extensions, deleted primes,
defining moduli and all unit associates. The unweighted detector has
coefficient 1. Smooth weights may depend on u in precisely the prescribed
norm-twist form, with compact real part, height <=T_1 and the original
polynomial height loss. Prime sets are disjoint and independent of u.
No arbitrary-coefficient replacement of the inverse polynomial is made.

The class has one fixed zero-location bin (i,a), delta=2a-1, and the same
prime-sum bins as in Liu section 10. The amplitude ratio is
x=gbar/delta, gbar=sum_i ell_i g_i/ell, with 0<=g_i<=delta/2. The two
large detector values use **one common character presentation and height**.
The original detector supplies t-1/2<=r<=t, 0<=m<=1/2, r+m>=t, up to
arbitrarily small fixed losses. The worst short face is m=t-r.

Liu section 5 explicitly bounds the primitive inducing conductor norm by
O_A(U), and retains omitted Euler factors at S and divisors of u. These
are varying ideal conductors. A bound for one fixed integer modulus or
one real-height family does not supply either target below. T_1<=U^(1/100)
and the stronger prescribed smooth-seminorm height loss must be retained.

## 1. Exact localization of the old comparison's failure

For either alpha, put

    c=8/9, D_c=3-(1+c)x, P_c=(2-cx)(1-x),
    J_alpha=(alpha-delta)D_c+delta P_c,
    R_alpha=1-delta+(alpha-delta)delta P_c/(2J_alpha),
    t_alpha=1+delta P_c/(2J_alpha).

D_c is a count polynomial, not the inverse length D. For the fixed
geometry, the endpoint exponent is

    E_alpha=C0+(1/2+ell)delta+ell*x*delta-h*(1-R_alpha),
    C0=-1/4+b/6+5ell/4.

The original count gives E_(5/6)>0 at delta=2/5,x=1/2, so some improvement
really is needed. Let y=1/2-x and Q=-2J_(5/6)E_(5/6). Write
Q=A(y)delta^2+B_q(y)delta+C_q(y).

The exact certificate covers the complement of the rectangle as follows:

| region | proof | lower bound for -E_(5/6) |
|---|---|---:|
| delta<=1/3, 0<=y<=2/25 | Q decreases up to delta=1/3; Q(1/3,y) has positive coefficients | 0.00000580246... |
| delta>=47/100 | partial_delta Q is positive there; Q(47/100,y) has positive coefficients | 0.00001988344... |
| y>=2/25 (equivalently x<=21/50) | 4AC_q-B_q^2, expanded about y=2/25, has positive coefficients | 0.00001372192... |

The first derivative sign uses an exact one-variable Bernstein
certificate on 0<=y<=2/25. The other coefficient signs are exact
rationals. Completing the square gives the third result. All four
coefficients of A are positive. Bounds use J<=3alpha_0 and the same Amax
as in the preceding certificate. These facts control the whole class
rectangle 0<=delta<=19/25, 0<=x<=1/2, not a numerical mesh.

The displayed exceptional rectangle is a sufficient enclosure, not a
minimal rectangle or a claim that every enclosed point fails. Strict
positive margins handle the original sufficiently small class/bin errors.

## 2. A moment on a short band of inverse lengths suffices

Assume H_band: the original ideal-Mobius polynomial above obeys

    sum_(q_u~U, u sixth-power-free, (u,S)=1) |M_u(U^r)|^2
        << U^(1/5+4r/5+epsilon) (1+T_1)^A
                  ONLY for 1099/1000<=r<=119/100.

All weight, ray-data and height hypotheses are unchanged. This is an
all-family mean square on that band, with no selected prime factors;
no new moment is assumed at shorter or longer lengths.

Inside the exceptional class rectangle choose t=t_(4/5). The following
three inequalities have exact tensor Bernstein certificates:

    R_(4/5) > 1-alpha_0+(alpha_0-delta)(1099/1000),
    1099/1000 < t_(4/5) < 119/100.

After multiplication by 2J_(4/5), their positive Bernstein lower bounds
are respectively

    287/810000,   2429/135000,   33559/18750000.

For inverse lengths 1<=r<1099/1000, the OLD long count is increasing in r
and already lies below R_(4/5). For 1099/1000<=r<=t use H_band; its count
is increasing and reaches R_(4/5) at r=t. No detector length exceeds t,
so nothing beyond 119/100 is required. The short inverse and unweighted
counts are unchanged and give the same crossing as in phase 2.

An independent piecewise affine supremum actually uses the OLD moment
below 1.099, rather than extending the new alpha there. It agrees exactly
with R_(4/5) at nine rational validation classes, including all corners.
The uniform argument is the Bernstein certificate and monotonicity above.
Rounding the lower edge up to 1.1 would invalidate this particular
comparison at delta=1/3,x=1/2; a regression test retains that negative
control. The proposed band is not claimed to be minimal.

Inside the class rectangle, the phase-2 endpoint certificate then applies.
Outside, use the original count from section 1. The combined endpoint
saving is >0.00000076229. The full direct, small/intermediate norm,
principal, support and tail-contour checks remain those of phase 2.
The moment improvement is a factor (D/U)^(1/30), now sought only on the
short band; at its largest length the saving is U^(19/3000).

## 3. An alternative direct large-values target

Instead of H_band, it suffices to prove, ONLY for the exceptional class
rectangle and the simultaneous zero/prime-amplitude family specified above,

    #B(delta,x;U,T_1)
      << U^(R_(5/6)(delta,x)-1/850+epsilon) (1+T_1)^A.       H_count

This is a proposed improvement of the class count, not a moment for
arbitrary bounded coefficients. The common-character, height,
coprimality, disjoint-support and original coefficient restrictions
are essential hypotheses. It must count elements u with their original
multiplicities, not merely distinct primitive conductors or independent
marginal detector families. It is not inferred from multiplying marginal
probabilities or applying Cauchy–Schwarz to the existing separate counts.

Subtracting eta=1/850 from R changes E by -h*eta. Thus

    Q_eta=Q+2J_(5/6)h*eta.

All five coefficients of its discriminant complement are positive. Exact
completion of the square proves the modified endpoint globally, although
H_count is required only inside the exceptional rectangle. Its strict
endpoint saving is >0.00000513261; the original count controls the exterior
with saving >0.00000580246. Its local d-slope remains positive:

    R_(5/6)-eta+delta/2-17/50
      >=33/50-47/200-1/850 >0.

The other scalar checks are unchanged. At a class where R_(5/6)=2/3,
this target asks for exponent

    2/3-1/850 = 1697/2550 = 0.665490196078... .

An arbitrary small improvement is not automatically enough for the
fixed B=0.874793 geometry: eta=1/1000 fails this uniform certificate.
The direct count target and the band moment target are different
sufficient hypotheses; no implication between them is proved. Neither
is a new analytic theorem.

The pointwise required count exponent can also be written, for a chosen
strict endpoint saving sigma>0, as

    R_req(delta,x)=1-[C0+(1/2+ell)delta+ell*x*delta+sigma]/h.

The additive 1/850 target is one convenient sufficient specification,
not a claim of an optimal required gain.

## 4. A direct selected-prime extension of the old averaging fails

One attempted input is to attach a prime product of total length U^z to
the long inverse polynomial, then repeat the existing sixth-power
averaging with a larger range U^h. Even granting such an extension with
no extra coprimality or smoothing losses, the old short inverse moment
requires, in closure,

    h>=max(1,r+2z,(2r+8z)/3).

The old averaging cost is U^(1/6+5h/6). A selected prime product supplies
squared amplitude at least U^(2delta*x*z), up to the prescribed losses.
Thus this optimistic proposed counting exponent is

    1/6+5h/6-delta*r-2delta*x*z
      >= [1/6+(5/6-delta)r] + (5/3-2delta*x)z.

Inside the exceptional class rectangle,

    5/3-2delta*x >=5/3-47/100 =359/300>0.

The bracket is precisely the old unselected long exponent. For r>=1,
z=0 attains the minimum of this cost model; every positive selected
prime length worsens it. The second closure restriction can only make
the exponent larger. The symbolic identity and rational lower bound are
recorded in [prime_extension_obstruction.json](verification_2026_10_24_liu_localized/prime_extension_obstruction.json),
with its check script alongside.

This rejects the proposed proof-cost substitution even before additional
losses. It does not assert a new mixed-moment theorem, disprove H_band or
H_count, or rule out a genuinely stronger correlation/large-values input.
It explains why simply carrying selected primes through the unchanged
sixth-power averaging cannot earn the required arithmetic improvement.

## Reproduction and remaining arithmetic gap

Code: [liu_localized_target.py](../../experiments/prime_spectral/liu_localized_target.py).
Primary receipt: [localized_verified.json](verification_2026_10_24_liu_localized/localized_verified.json).
All scalar calculations use exact rational arithmetic and polynomial
identities; reported decimals only display those certificates.

    uv run --with sympy==1.14.0 --python 3.12 python \
      experiments/prime_spectral/liu_localized_target.py
    uv run --with sympy==1.14.0 --python 3.12 python -m unittest \
      discover -s experiments/prime_spectral -p 'test_liu*.py' -v
    python3 experiments/prime_spectral/check_dh_research_gate.py

The registry remains `uninstantiated`, with separating inequality null.
The retained DH reciprocal nonmultiplicativity witness blocks the verbatim
ideal-Mobius transfer, but supplies neither a DH implementation of these
new targets nor a proof of their truth. The parked analytical row-density
route is unchanged. No previous receipts or manifests are rewritten;
updated register/literature bytes from the prior phase are retained here.

The remaining step is an arithmetic proof of H_band or H_count for the
actual family. This localization does not establish a conductor-uniform
Guth–Maynard transport, any statistical independence, or a sufficient
new DH separator. The existing coefficient-alignment obstruction still
rules out a coefficient-insensitive all-family version of H_band; it
alone does not refute H_count. Neither estimate has been Lean-formalized
or analytically reproved in this phase.
