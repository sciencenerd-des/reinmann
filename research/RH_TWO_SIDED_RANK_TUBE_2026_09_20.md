# A two-sided rank comparison retaining neighboring cancellation

Update: the [width obstruction](RH_RANK_TUBE_WIDTH_2026_09_20.md) proves
that these rectangular inequalities force at least linear width growth
whenever a central or neighboring interval has nonzero width. Thus the
rational specialization below cannot admit nonidentical ordered envelopes;
the exact repeated-root control remains valid. A bounded-error Xi model
needs a comparison retaining correlated errors, beyond these rectangles.

Update: [the Xi shift-two exponential tube](RH_SHIFT_TWO_EXPONENTIAL_TUBE_2026_09_20.md)
now supplies a proved exterior boundary at shift two, from rank 60 onward.
It also proves that a positive rational lower ratio envelope cannot fit
this Xi tail. The general comparison theorem remains applicable; its
rational specialization is not a global Xi model.

## Result and scope

There is a conditional comparison theorem that bounds both the curvature
and its rank slope, and keeps both neighboring correction terms. Unlike
the previous scalar criteria, it admits the exact repeated-root control
with a rank slope tending to zero. In that control, both correction
inequalities are polynomial identities, for all ranks and all degrees.

The general theorem still needs actual head and boundary bounds, and
uniform comparison inequalities at every interior shift. None of those
new hypotheses has been established for Xi. This is an ordinary analytic
comparison proof and exact algebraic implementation, not an RH proof or
a Lean formalization.

## 1. A general two-sided comparison theorem

Let delta_r(m)=-log t_r(m), v_r(m)=delta_r(m)-delta_(r-1)(m), and

    Phi_(r,m)(x)=log[1+(m/r)*(1-exp(-x))].

For x>=0 its logarithm argument is at least one, and Phi is increasing.
The normalized recurrence gives

    C_r(m)=2Phi_(r,m)(delta_r(m))
                -Phi_(r,m-1)(delta_r(m-1))
                -Phi_(r,m+1)(delta_r(m+1)),
    v_(r+1)=v_r+C_r, delta_(r+1)=delta_r+v_(r+1).

Suppose we have functions g_r(m),h_r(m), defined from rank R-1 onward,
with 0<=g_r(m)<=h_r(m) for r>=R and ordered backward rank differences.
Write nabla f_r=f_r-f_(r-1) and Delta_r^2 f=f_(r+1)-2f_r+f_(r-1).
For every r>=R and every interior shift assume

    2Phi_(r,m)(g_r(m))
      -Phi_(r,m-1)(h_r(m-1))-Phi_(r,m+1)(h_r(m+1))
          >=Delta_r^2 g_r(m),                         (1)

    2Phi_(r,m)(h_r(m))
      -Phi_(r,m-1)(g_r(m-1))-Phi_(r,m+1)(g_r(m+1))
          <=Delta_r^2 h_r(m).                         (2)

At the head require

    g_R(m)<=delta_R(m)<=h_R(m),
    nabla g_R(m)<=v_R(m)<=nabla h_R(m).                (3)

For a finite strip, both exterior shift boundaries must remain in these
value and slope bounds at every later rank, with positive boundary
determinants. For the full half-line m>=2 only shift one is exterior,
but (1)-(3) must be established at every interior shift. Positive initial
determinant rows and the exact normalized condensation identities are
also required.

**Theorem.** Under these hypotheses the value and slope bounds persist
for every r>=R, and the interior determinant rows remain positive.

**Proof.** Suppose the bounds hold at rank r. Monotonicity of Phi bounds
C_r below by the left side of (1), and above by the left side of (2).
Notice the directions: a lower bound for central curvature is paired
with *upper* bounds for neighboring curvatures. Adding these correction
bounds to the current slope proves

    nabla g_(r+1)<=v_(r+1)<=nabla h_(r+1).

Adding the new slope to the current value proves the next value bounds.
There is no assumption of the next row in this argument. More explicitly,
before taking its logarithms, delta_r>=g_r>=0 gives t_r<=1 and B_r>=1.
Condensation and the two positive starting rows construct a positive next
interior row. The supplied exterior boundary rows are positive, so its
ratios and logarithms are defined. The logarithmic recurrence can then
be used as above. This is simultaneous induction over the interior shifts.
It also applies to infinitely many shifts when the hypotheses hold at
every shift. QED.

Thus future positive neighboring factors need not be assumed separately
if the full two-sided comparison and boundary package is actually proved.
Their positivity follows within the induction. The package is currently
missing for Xi.

## 2. Rational envelopes and exact all-rank polynomial tests

The implementation studies a concrete special case. At each shift choose
positive rational amplitudes and rational offsets and set

    L_r(m)=a_m/(r+k_m), U_r(m)=A_m/(r+K_m),
    g_r(m)=-log U_r(m), h_r(m)=-log L_r(m).

Require 0<L<=U<1 for all r>=R, and R+k_m>1, R+K_m>1.
The ordering of backward slopes is K_m>=k_m. The inequalities L<=U
are linear polynomial inequalities after clearing positive denominators;
U<1 follows from U_R<1 since U decreases with r.

For any envelope e_r(j)=a/(r+k), define

    Q_j(e;r)=(r+j)(r+k)-j*a.

Then B_r(j;e)=Q_j(e;r)/[r(r+k)]. It is positive on the asserted domain.
For three envelopes e0,e-,e+ at shifts m,m-1,m+1 respectively, let

    P(r;e0,e-,e+)=Q_m(e0;r)^2*(r+k_-)*(r+k_+)
             -[(r+k_0)^2-1]*Q_(m-1)(e-;r)*Q_(m+1)(e+;r).   (4)

The logarithmic lower-comparison condition (1) is exactly

    P(r;U_m,L_(m-1),L_(m+1))>=0.                      (5)

The upper condition (2) is exactly

    P(r;L_m,U_(m-1),U_(m+1))<=0.                      (6)

To derive these, exponentiate the comparison, use
exp(Delta_r^2[-log(a/(r+k))])=1-1/(r+k)^2, and clear
the strictly positive denominators. The factors r^2 and the central
(r+k)^2 cancel before forming (4). No neighboring factor is discarded.

The polynomial in (4) has degree at most six. The code expands (5) and
the negative of (6) in powers of r-R and checks that every coefficient
is nonnegative using exact rational arithmetic. This is sufficient for
all real r>=R, hence for every subsequent integer rank. A negative
coefficient is classified as unresolved; it is not automatically a
negative polynomial or a counterexample. The zero polynomial passes
exactly. No rank sampling is used in this certification.

The head bounds can also be checked rationally. If
p0<=t_(R-1)<=p1 and q0<=t_R<=q1, with all endpoints positive, then
(3) follows from

    q1<=U_R, q0>=L_R,
    p0>=q1*(R+K)/(R+K-1),
    p1<=q0*(R+k)/(R+k-1).                             (7)

The certificate keeps (7), future boundary bounds, and the actual-array
identification separate from the local polynomial tests.

## 3. Exact critical control, including both boundaries

For E_N(z)=(1+z/N)^N, take

    L_r(m)=U_r(m)=(N-m)/(r+N-m), 1<=m<=N-1.

At every shift this is the exact ratio proved in the
[repeated-root determinant control](RH_REPEATED_ROOT_RANK_CONTROL_2026_09_20.md).
The head value and slope tests (7) hold with equality at every R>=1.
For interior 2<=m<=N-2 both exterior neighbors have positive amplitudes.
Writing k=N-m, the three numerators in (4) simplify identically to

    Q_m=Q_(m-1)=Q_(m+1)=r(r+N).

Also (r+k_-)(r+k_+)=(r+k+1)(r+k-1)=(r+k)^2-1. Thus P is identically
zero, proving both (5) and (6) for all r,N,m in the stated domain.
`repeated_root_identity()` verifies these identities in an exact rational
multivariate polynomial ring, not at finitely many ranks or degrees.

The finite-strip boundaries m=1 and m=N-1 are supplied at every rank by
the existing exact determinant formulas; their determinant values are
positive as required. Thus the comparison package is fully instantiated
for this control. It reproduces

    delta_r(m)=log(1+r/(N-m)),
    v_r(m)=log[(N-m+r)/(N-m+r-1)] -> 0.

There is no positive slope surplus. The difference from the failed scalar
comparison is precisely the simultaneous retention of central and
neighboring terms in (4).

## 4. What remains for Xi

The general comparison theorem permits other functions g,h; only the
implemented polynomial checker specializes to rational ratio envelopes.
Such two-sided rational envelopes force delta_r=log r+O(1) at a fixed
shift. They therefore cannot be silently imposed in a regime with a
different growth rate. No assertion about Xi's tail growth follows from
the control.

An application to Xi needs analytically justified lower and upper ratio
envelopes, both initial slope bounds, all-shift correction inequalities,
and the exterior boundary information. The rank-two theta theorem does
not provide these higher-rank hypotheses. No Xi head is classified as
passing by this experiment, and no RH conclusion is claimed.

Replay:

    uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/two_sided_rank_tube.py --output research/certified_xi/two_sided_rank_tube.json
    uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/certified_xi -p 'test_*.py'

Tests check the symbolic all-degree identities, exact head equality,
the polynomial-to-rational correction identity, invalid inputs, and a
perturbed neighboring lower bound that loses certification. The general
comparison proof is written analysis, not Lean formalized.

Validation: all 115 certified-Xi tests passed. The artifact's two source
hashes match, every local polynomial and head condition in the exact
control passes, and `git diff --check` passed.
