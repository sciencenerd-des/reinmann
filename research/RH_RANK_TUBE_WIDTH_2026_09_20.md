# Width obstruction for the rectangular rank comparison

Follow-up: the [exact linearization](RH_RANK_LINEARIZATION_2026_09_20.md)
shows that even an error constant across shifts can amplify quadratically
in rank in the repeated-root control. Retaining correlation is necessary
for the proposed approach, but does not itself yield a uniform stability bound.

## Result

The two-sided comparison in
[the rank tube theorem](RH_TWO_SIDED_RANK_TUBE_2026_09_20.md) is valid,
but cannot certify any nontrivial bounded-width tube at an interior
shift. More generally, sublinear width is impossible if the central
or either neighboring interval ever has positive width. This restricts
the comparison method, not the Xi array, and is not an RH counterexample.

In particular, its rational-envelope specialization only admits exact
coinciding envelopes throughout each interior triple. Searching for
slightly widened rational envelopes cannot repair the missing Xi proof.
This conclusion holds independently of numerical precision.

## 1. Necessary width inequality

Retain the original notation

    Phi_(r,m)(x)=log[1+(m/r)(1-exp(-x))],
    0<=g_r(m)<=h_r(m), w_r(m)=h_r(m)-g_r(m),
    d_r(m)=Phi_(r,m)(h_r(m))-Phi_(r,m)(g_r(m)).

Since Phi is strictly increasing, d>=0, with equality exactly when w=0.
The two rectangular comparison hypotheses are

    Delta_r^2 g <= 2Phi(g_m)-Phi(h_-)-Phi(h_+),
    Delta_r^2 h >= 2Phi(h_m)-Phi(g_-)-Phi(g_+).

Subtracting the first from the second gives the necessary condition

    Delta_r^2 w_r(m)>=2d_r(m)+d_r(m-1)+d_r(m+1)>=0.   (1)

The neighboring terms have positive signs in (1). Cancellation between
actual neighboring errors was lost when the rectangle selected their
opposite endpoints. Ordered backward slopes in the original theorem give
nabla w_R(m)>=0. Equation (1) therefore implies nabla w_r(m)>=0
for every r>=R.

Suppose at rank s>=R at least one of the triple's intervals has positive
width. Put gamma=2d_s(m)+d_s(m-1)+d_s(m+1)>0. Then

    nabla w_(s+1)(m)>=nabla w_s(m)+gamma>=gamma.

Convexity in (1) preserves that slope lower bound. Hence

    w_(s+j)(m)>=w_s(m)+j*gamma, every integer j>=1.    (2)

This contradicts w_r(m)=o(r), and in particular bounded or decaying
width. This is an all-rank obstruction, not a negative polynomial
coefficient being misclassified as a negative polynomial.

The full discrete integration identity gives the stronger necessary bound

    w_(R+n)(m)>=w_R(m)+n*nabla w_R(m)
      +sum_(k=R)^(R+n-1) (R+n-k)
         *[2d_k(m)+d_k(m-1)+d_k(m+1)].                (3)

It follows by summing (1) first over slopes and then over values.

## 2. Exact rational diagnostic

At one rank let L_j<=t_j<=U_j, with 0<L_j<=U_j<=1.
The corresponding g_j=-log U_j, h_j=-log L_j satisfy

    exp(d_j)=(r+j-j*L_j)/(r+j-j*U_j).

Both numerator and denominator are positive. Thus

    exp(gamma)=product_(j=m-1,m,m+1)
       [(r+j-j*L_j)/(r+j-j*U_j)]^(1,2,1).            (4)

For rational endpoints (4) is an exact rational number. It exceeds one
if and only if some L_j<U_j. No floating-point logarithm is needed to
certify the obstruction. The helper `width_forcing_ratio` evaluates (4).

For the original rational functions L=a/(r+k), U=A/(r+K),

    w_r=log(A/a)+log((r+k)/(r+K)).                    (5)

This has a finite limit as r tends to infinity. Under the original
ordering assumptions it therefore cannot satisfy (2) for any gamma>0.
Global ratio ordering follows from A>=a and U_R>=L_R: after clearing
positive denominators, U-L has an affine numerator with nonnegative
slope and nonnegative value at R. Ordered backward slopes follow from
K>=k. The diagnostic checks these hypotheses before claiming anything.

If two such globally ordered functions are not identical, their affine
numerator is strictly positive at R+1, even when they touch at R.
Consequently evaluating (4) at R+1 detects every nonidentical triple.
An identical triple is classified only as having no width obstruction;
its head, correction and boundary hypotheses still require separate proof.
The repeated-root exact control remains a valid successful example.

## 3. Consequence for the Xi research direction

This does not invalidate the exterior shift-two boundary tube. The
rectangular correction hypotheses are imposed on the interior; an
exterior boundary is supplied separately. Its practical use in a
comparison may, however, force widening at adjacent interior shifts.
Nor does this rule out linearly widening interior tubes: their slope
and positivity margins would have to survive that widening.

It does rule out a proposed interior tube with the same exact linear
slope in its upper and lower models and bounded remainder width,
unless the models coincide exactly. The certificate intervals for an
unknown slope must not be silently identified with a fixed exact slope.

A replacement should retain correlated neighboring errors before taking
absolute values. To specify the missing estimate, choose an approximate
profile f_r(m), write delta=f+e, and set

    H_r(m)=Phi_(r,m)(f_r(m)+e_r(m))-Phi_(r,m)(f_r(m)),
    T_r(m)=2Phi_(r,m)(f_r(m))-Phi_(r,m-1)(f_r(m-1))
           -Phi_(r,m+1)(f_r(m+1))-Delta_r^2 f_r(m).

Where the actual logarithmic recurrence is defined, subtraction gives
exactly

    Delta_r^2 e_r(m)=T_r(m)+2H_r(m)-H_r(m-1)-H_r(m+1). (6)

A bound on the *joint spatial second difference* of H can preserve
cancellation that individual interval radii cannot. Such a bound must
come from the common theta/determinant structure and be available during
positivity induction, rather than assuming the future positive array.
No uniform Xi estimate for this expression is proved here. Equation (6)
identifies the quantity required of that next argument.

## Validation and scope

The proof of (1)-(3) is elementary subtraction and discrete summation.
The implementation uses Python exact fractions. Four tests cover the
exact repeated-root control; independent central and neighboring
perturbations; envelopes touching at the head; a hand-computed rational
forcing factor; and invalid domains. Existing polynomial checks report
the perturbed controls as unresolved, consistently with this stronger
analytic obstruction.

Replay from the repository root:

```sh
uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/certified_xi -p test_rank_tube_width.py -v
```

This is a written proof about a sufficient comparison method, not a Lean
formalization and not a proof or disproof of RH. The uniform interior
all-rank budget remains open.
