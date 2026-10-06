# A self-sustaining rank-tail budget

Update: [an exact repeated-root control](RH_REPEATED_ROOT_RANK_CONTROL_2026_09_20.md)
shows that this positive-slope criterion is stronger than real-rootedness
and determinant positivity. Its Xi-specific growth hypothesis remains
unproved; a general cumulative budget may need zero limiting slope margin.

## Result and scope

The normalized recurrence admits a conditional infinite-tail theorem:
a sufficiently large positive curvature and positive rank slope at a head
rank can pay for every later negative correction. This follows from an
exponential correction bound, not from fitting the finite Xi data.

The theorem is not yet instantiated uniformly for Xi. It needs either
positive neighboring correction factors throughout the tail, or a
simultaneous induction at every shift supported by compatible head bounds.
A finite list of shifts does not provide those hypotheses.

The following notation is from the
[normalized recurrence](RH_NORMALIZED_RECURRENCE_2026_09_14.md):

    t_r(m)=A_r(m-1)A_r(m+1)/A_r(m)^2,
    delta_r(m)=-log t_r(m),
    B_r(m)=1+(m/r)(1-t_r(m)),
    C_r(m)=2log B_r(m)-log B_r(m-1)-log B_r(m+1),
    delta_(r+1)=2delta_r-delta_(r-1)+C_r.

All uses of logs below require their displayed arguments to be positive.

## 1. A negative correction is exponentially small in current curvature

Fix r>=1,m>=2. Suppose all three t values are positive, the neighboring
B values are positive, and the central delta_r(m)=d is positive. Factor

    B_r(j)=(r+j)/r * [1-alpha_j*t_r(j)],
    alpha_j=j/(r+j), j=m-1,m,m+1.

Then

    C_r(m)=log[(r+m)^2/((r+m)^2-1)]
           +2log(1-alpha_m*exp(-d))
           -log(1-alpha_(m-1)*t_r(m-1))
           -log(1-alpha_(m+1)*t_r(m+1)).                 (1)

The first term is positive. Each of the last two terms is nonnegative:
its log argument lies in (0,1), by positivity of B and t. It is not
necessary to assume that the neighboring t values are <=1 for this step.
Since alpha_m<1 and -log(1-x)<=x/(1-x) for 0<=x<1,

    C_r(m) >= -2 exp(-d)/(1-exp(-d)).                   (2)

The elementary log inequality follows by integrating 1/(1-s) from 0 to
x and replacing the integrand by its largest value 1/(1-x). Equation (2)
controls a potentially negative correction without requiring C_r>=0.
The omitted positive terms in (1) could improve the estimate further.

## 2. Scalar tail theorem

Suppose the recurrence and the hypotheses needed for (2) hold at every
rank r>=R at a fixed shift. At rank R assume

    delta_R>=d>0, delta_R-delta_(R-1)>=v>0.

Choose 0<b<v and define the explicit total loss budget

    T(d,b)=2 exp(-d)/[(1-exp(-d))(1-exp(-b))].           (3)

If v-b>=T(d,b), then for every integer j>=0,

    delta_(R+j)>=d+j*b,
    delta_(R+j)-delta_(R+j-1)>=b.                      (4)

**Proof.** Write v_r=delta_r-delta_(r-1). If (4) is known through j,
(2) gives, for each preceding tail step k,

    C_(R+k) >= -2 exp(-d-kb)/(1-exp(-d-kb))
              >= -2 exp(-d)exp(-kb)/(1-exp(-d)).

Adding v_(R+j+1)=v_R+sum_(k=0)^j C_(R+k), the geometric series is
bounded by (3). Therefore v_(R+j+1)>=v-T>=b, and
adding this slope to delta_(R+j) proves the next lower bound in (4).
The case j=0 starts with the head assumptions. This proves the infinite
claim by induction, without assuming (4) in advance. QED.

The implementation takes b=v/2 as a simple sufficient choice. It is not
claimed to be the optimal b. Its loss bound is conservative: it does not
spend any of the positive baseline in (1).

## 3. How a genuine all-shift induction could discharge the dependency

The scalar theorem alone cannot assert that the neighboring B values
stay positive. For the actual determinant array, that dependency can be
handled by a simultaneous induction over all shifts, if a compatible
head region is proved first.

A sufficient package is:

1. The exact condensation identities and positive initial rows A_0,A_1.
2. Positive shift-zero boundary values and the already separate shift-one
   curvature control at every rank.
3. For every shift m>=2, a finite cutoff R(m)>=1 such that the head
   curvatures delta_r(m)>=0 are established for 1<=r<=R(m), and the
   cutoff curvature/slope admit d(m),v(m),b(m)>0 satisfying (3).

All these head assertions must concern the actual array. They are
unbounded in m, even though the head at each individual m is finite.
No bounded coefficient table proves item 3.

Here is the induction order, to avoid circularity. Assuming positive A
values at ranks r and r-1 and nonnegative delta_r at **every** shift,
we have t_r<=1 and B_r>=1 everywhere. Condensation first constructs a
positive row A_(r+1). All neighboring factors in (1) are therefore
positive. At a shift still inside its head region, the next curvature
is supplied by the head theorem. At a shift beyond its cutoff, the
scalar induction proves its next positive curvature. The separate
shift-one result supplies the boundary case. This closes the induction
provided item 3 actually holds.

Allowing R(m) to depend on m is important: a universal finite head rank
is not asserted. This is a sufficient mechanism for proving the rank
tail once uniform-in-shift head information is available, not a proof
that such information exists for Xi.

## 4. Certified finite head witnesses

Using the certified coefficients through index 120 and dual determinants,
`rank_tail_bootstrap.py` finds the following first passing heads within
its scanned range, with b chosen as half the certified lower slope:

| Shift m | First passing head rank R |
|---|---:|
| 2 | 24 |
| 3 | 28 |
| 4 | 51 |
| 5 | 43 |
| 6 | 59 |

Every reported pass checks d>0, v>0 and v-b-T>0 using outward ball
arithmetic. They are finite witnesses to the scalar budget, not
unconditional infinite-rank Xi certificates. In particular, the exterior
shift needed by a finite strip is not controlled by scanning the strip.
The output status explicitly says `conditional_tail_budget_pass` and
records the missing neighboring-factor hypothesis in each row.

This changes the next analytic target: establish a compatible head region
and slope at all shifts, or obtain an independent positivity bound for
the neighboring factors. The existing large-parameter rank-two curvature
tail alone does not supply either condition.

## Replay and trust

    uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/rank_tail_bootstrap.py --coefficients research/certified_xi/coefficients_120.json --output research/certified_xi/rank_tail_bootstrap.json
    uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/certified_xi -p 'test_*.py'

Equations (1)-(4) have a written elementary proof; they are not yet Lean
formalized. The finite heads depend on the coefficient and determinant
ball trust boundary. Input and source hashes are retained in the artifact.
RH and the unconditional all-rank interior budget remain unproved.

Validation: 75 certified-Xi tests passed; input/source hashes match the
current files, and `git diff --check` passed.
