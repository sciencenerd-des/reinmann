# An exponential Xi boundary tube at shift two

Update: the [second-difference refinement](RH_SHIFT_TWO_CORRECTION_2026_09_20.md)
proves that these slopes strictly increase to beta, with explicit
inverse-square correction bounds and a convergent cumulative gain.

## Results and scope

Using the established three-pole shift-two certificate, the following
stronger rank-growth statement holds for the actual Xi coefficient array:

    delta_r(2)-delta_(r-1)(2)>0.06085, every integer r>=1,
    delta_0(2)=0,
    0<t_r(2)<=exp(-0.06085*r).                         (1)

There are also explicit two-sided bounds for both delta_r(2) and its
rank slope, valid for every r>=60. They have a linear term, a logarithmic
correction, and controlled geometric errors. These bounds supply a
Xi-specific exterior shift-two boundary for a future comparison over
interior shifts m>=3.

This is not a uniform theorem over those higher shifts. Their two-sided
envelopes and comparison inequalities remain unproved. The result uses
the same written analytic and numerical trust boundary as the
[three-pole theorem](RH_UNIFORM_SHIFT_TWO_2026_09_19.md), not additional
global assumptions about the zeros. It is not Lean formalized or an RH proof.

## 1. A rational lower envelope is incompatible with this Xi tail

The existing theorem already proves, for a constant C>0 and 0<q<1,

    t_r(2)<=C*(r+2)*q^r, every r>=45.

Hence no fixed a>0 and finite k can satisfy

    a/(r+k)<=t_r(2)

at every sufficiently large rank. Such an inequality would imply
a<=C*(r+k)*(r+2)*q^r, whose right side tends to zero. Geometric decay
beats this fixed quadratic factor; for example its successive ratio
tends to q<1 and is eventually bounded above by a number below one.

Thus the rational-envelope specialization of the new two-sided theorem
cannot be imposed globally even at shift two of Xi. This is a consequence
of a certified Xi tail, not a hypothetical example. The general comparison
theorem permits other envelopes, and the following exponential ones fit
this boundary's actual growth.

## 2. Shared leading model and logarithmic remainder

The pole certificate proves for m=1,2,3 and r>=45 that

    D_r(m)=W_m*lambda_m^r*(1+e_m(r)),
    |e_m(r)|<=E_m(r)<1,
    E_m(r)=sum_l c_(m,l)*q_(m,l)^r,
    c_(m,l)>=0, 0<q_(m,l)<1.                          (2)

These are uniform analytic coefficient bounds, with the repeated-column
cancellations in the residual determinant expansion retained. All weights
and rates are fixed actual quantities enclosed by the saved intervals.
Set

    A=W_1*W_3/(2W_2^2), q=lambda_1*lambda_3/lambda_2^2,
    beta=-log q>0.

Then exactly

    t_r(2)=A*(r+2)*q^r*[(1+e_1(r))(1+e_3(r))/(1+e_2(r))^2].

Since |log(1+x)|<=-log(1-|x|) for |x|<1, define

    K(r)=-log(1-E_1(r))-2log(1-E_2(r))-log(1-E_3(r)).

The shared logarithmic model

    f(r)=beta*r-log(r+2)-log A

satisfies

    |delta_r(2)-f(r)|<=K(r).                          (3)

Let sigma be the largest saved upper bound on any q_(m,l). It is
strictly less than one and is approximately 0.781928746117914. From (2),
E_m(r+j)<=sigma^j E_m(r). For 0<=s<=1 and 0<=x<1,

    -log(1-s*x)<=s*(-log(1-x)).

One proof is to expand -log(1-x)=sum_(n>=1) x^n/n and use s^n<=s.
Consequently

    K(r+j)<=sigma^j K(r), every integer j>=0.         (4)

This extends the error bound uniformly; it is not a fit to sampled ranks.

## 3. Rank slopes and their limiting value

Subtract (3) at neighboring ranks. The same fixed A and q occur at both
parameters, so the common log A cancels exactly. For r>=46,

    |v_r(2)-[beta-log((r+2)/(r+1))]|<=K(r)+K(r-1),
    v_r(2)=delta_r(2)-delta_(r-1)(2).                 (5)

At R=60 put E=K(R-1)+K(R), rounded upward to an exact rational bound.
Equations (4)-(5) give, for all r>=R,

    |v_r(2)-[beta-log((r+2)/(r+1))]|<=E*sigma^(r-R).   (6)

The saved enclosure has E<0.050830. In particular v_r converges to the
fixed actual beta, which lies in the certified interval around
0.347477279614256. This conclusion uses only the three already isolated
simple poles in the bounded disk; it is not a simplicity assertion for
all Xi zeros.

Let A_-<=A<=A_+ and q_-<=q<=q_+ be the exact rational endpoints of
the saved ball calculations. They satisfy 0<A_- and 0<q_-<=q_+<1.
Since log((r+2)/(r+1)) and E*sigma^(r-R) decrease, (6) yields

    v_r(2)>=-log q_+-log((R+2)/(R+1))-E>0.2803876,
    every r>=60.                                    (7)

The finite ranks 1..59 are covered by fresh dual determinants from the
existing certified coefficients. With t_0(2)=1, their slope enclosures
all exceed 0.0608539. There is no rank gap between that bridge and (7).
This proves v_r(2)>0.06085 at every integer r>=1. Summing from delta_0=0
gives (1), including its exponential ratio bound.

## 4. Boundary functions compatible with the two-sided comparison

The shrinking error in (3) is not by itself a pair of comparison functions
whose backward differences enclose the actual slopes. To obtain that
compatibility, integrate the slope-error envelope explicitly. Define

    W(r)=E*(1-sigma^(r-R+1))/(1-sigma), r>=R-1,
    W(R-1)=0, W(R)=E,
    W(r)-W(r-1)=E*sigma^(r-R).                        (8)

For every r>=R, W(r)>=E>=K(R)>=K(r), so it also bounds the value error.
Define

    g(r)=-log A_+-log(r+2)-r*log q_+-W(r),
    h(r)=-log A_--log(r+2)-r*log q_-+W(r).             (9)

Combining (3), (6), (8), and the endpoint orderings proves

    g(r)<=delta_r(2)<=h(r),
    g(r)-g(r-1)<=v_r(2)<=h(r)-h(r-1), every r>=60.     (10)

The definitions at R-1 are used to define the initial backward difference;
no value enclosure at R-1 is claimed by (9). The initial value and slope
enclosures in (10) are separately justified by (3) and (6).

The computed lower value g(60)>16.2192. Its backward differences are
positive by (7), so g(r)>0 throughout r>=60. The corresponding upper
ratio envelope exp(-g(r)) is therefore below one, and the lower ratio
envelope exp(-h(r)) is strictly positive. Positive shift-two determinants
at every rank are supplied by the preceding three-pole theorem.

Thus the head, future boundary-value, boundary-slope and boundary
determinant requirements of the general
[two-sided comparison](RH_TWO_SIDED_RANK_TUBE_2026_09_20.md) are now
available at the exterior shift m=2 for every r>=60. The polynomial
checker for rational envelopes does not apply to (9); the analytic
comparison theorem, which accepts general functions g,h, does.

No bounds have been manufactured for m>=3. Extending a finite-pole
construction to arbitrarily many shifts would require additional zero
and remainder information, which cannot be assumed from RH or from
these three poles.

## Replay and verification boundary

    uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/shift_two_exponential_tube.py --base research/certified_xi/pole_shift_two.json --coefficients research/certified_xi/coefficients_120.json --output research/certified_xi/shift_two_exponential_tube.json
    uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/certified_xi -p 'test_*.py'

The implementation checks the input and base source hashes, positivity
and geometric decay of every serialized error term, the head/tail
clearances, and the complete finite slope bridge. It records the base
artifact hash, exact rational constants, and all interval bridge values.
The source hashes establish provenance, not a formal proof of the
underlying analytic estimates.

Tests compare both value and slope bounds with fresh determinant
calculations at ranks 60,61,80,100, check the integrated-width identity
exactly, and reject inconsistent source inputs or nondecaying error
terms. These finite tests validate the implementation; equations (2)-(10)
supply the written all-rank argument.

Validation: all 119 certified-Xi tests passed. Base-artifact, coefficient,
and source hashes match; the finite slope bridge covers ranks 1..59 and
the analytic tail starts at 60. `git diff --check` passed. No Lean source
was changed or rebuilt in this continuation.
