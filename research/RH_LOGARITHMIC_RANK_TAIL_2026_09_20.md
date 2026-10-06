# A logarithmic rank comparison and its structural limitation

## Outcome

A logarithmic comparison gives an elementary sufficient head condition,
with no chosen constant slope parameter b and with equality allowed in
the head inequalities. It has a written conditional all-rank proof and
finite certified Xi head witnesses.

However, the full neighboring-factor hypotheses make this criterion imply
eventual linear growth anyway. It therefore does **not** resolve the
[repeated-root obstruction](RH_REPEATED_ROOT_RANK_CONTROL_2026_09_20.md).
The useful finding is that changing the shape of the scalar barrier alone
does not remove the stronger growth assumption: the neighboring terms
must be retained with more precise bounds. RH remains unproved.

## 1. Exact rational head conditions

Use the normalized determinant recurrence and notation t_r(m), delta_r(m),
B_r(m), C_r(m). Fix m>=2 and R>=1. Assume the recurrence holds and, at
every rank r>=R, the central and neighboring t values and both neighboring
B values are strictly positive. These hypotheses are not inferred from
finite data.

Put n=R+m. Suppose exact positive rational one-sided bounds q,p satisfy

    t_R(m)<=q, t_(R-1)(m)>=p,
    m*n*q<=1, (n-1)*p>=n*q.                          (1)

The second inequality gives the required initial rank slope:

    delta_R-delta_(R-1)>=log(p/q)>=log[n/(n-1)].

No transcendental rounding is needed to test (1). Set d=-log q>0 and

    g_j=d+log[(n+j)/n], j>=-1.

Then delta_R>=g_0 and its initial slope is at least g_0-g_(-1).

## 2. Uniform comparison theorem

For r=R+j set x=n+j=r+m. The exact correction decomposition from the
compensated theorem gives

    C_r(m)>=s_x+2log(1-alpha_m*t_r(m)),
    s_x=-log(1-1/x^2), alpha_m=m/x.                  (2)

Only the two nonnegative neighboring terms were dropped in (2). Under
the inductive hypothesis delta_(R+j)>=g_j, we have

    t_(R+j)(m)<=q*n/(n+j),
    alpha_m*t_(R+j)(m)<=beta/x^2, beta=m*n*q<=1.

Therefore

    C_r(m)>=s_x+2log(1-beta/x^2)
           >=s_x+2log(1-1/x^2)
           =log(1-1/x^2)
           =g_(j+1)-2g_j+g_(j-1).                  (3)

The logarithm arguments are positive because x>=3 and beta<=1.
If the current slope is at least g_j-g_(j-1), the recurrence and (3)
make the next slope at least g_(j+1)-g_j. Adding it to the current value
gives the next value bound. Starting from (1), induction proves

    delta_(R+j)>=d+log[(n+j)/n],
    delta_(R+j)-delta_(R+j-1)>=log[(n+j)/(n+j-1)],
    t_(R+j)(m)<=q*n/(n+j), for every j>=0.            (4)

This is a conditional infinite-rank theorem, not an extrapolation of the
finite table. In particular the comparison slope in (4) tends to zero.

## 3. Why the actual hypotheses still force a positive slope surplus

The discarded neighboring contribution at the head is

    eta_R=-log(1-alpha_(m-1)*t_R(m-1))
           -log(1-alpha_(m+1)*t_R(m+1)) >0.           (5)

It is strictly positive because m>=2, the t values are strictly positive,
and each log argument is in (0,1) by positive neighboring B. Retaining
(5) in the first step shows

    delta_(R+1)-delta_R >= g_1-g_0+eta_R.

At every subsequent step (3) still applies. Thus the difference between
the actual slope and the comparison slope never decreases. Inductively,

    delta_(R+j)>=g_j+j*eta_R, j>=1.                  (6)

Consequently (1) and the full strict positivity hypotheses imply eventual
linear growth, even when the initial inequalities in (1) are equalities.
The zero-limit slope in the *comparison function* is not the same as an
admissible zero-limit slope in an actual array satisfying all the theorem's
hypotheses. This distinction prevents a false claim of resolving the
positive-slope limitation.

For the exact control `(1+z/N)^N`, K=N-m, the amplitude condition fails:

    beta=m*(R+m)*K/(R+K)>1

for interior m>=2,K>=2,R>=1. Indeed mK(R+m)-(R+K)
=(mK-1)R+K(m^2-1)>0. So there is no conflict between (6) and that
control's logarithmic growth.

To accommodate such behavior, a comparison must retain enough of the
neighboring contributions at every step to match the critical negative
rank curvature, rather than replace them by zero and keep the resulting
central-only estimate. This remains an analytic requirement, not a
theorem about the actual Xi array.

## 4. Finite Xi witnesses and comparison with earlier criteria

The implementation uses the existing 120-coefficient certified input and
fresh dual determinants, scanning ranks 2..113. At each head it takes the
exact rational upper endpoint of t_R and lower endpoint of t_(R-1), then
checks (1) by rational arithmetic. The first passing heads found are:

| Shift | Logarithmic comparison | Existing compensated comparison |
|---|---:|---:|
| 2 | 22 | 16 |
| 3 | 28 | 21 |
| 4 | 46 | 33 |
| 5 | 45 | 34 |
| 6 | 60 | 44 |

The new comparison does not improve these particular finite head cutoffs.
Its benefit is an explicit alternative target and the structural proof
(5)-(6), not new unconditional Xi ranks. The classifier remains
`conditional_logarithmic_tail_pass` and records the missing neighboring
and all-shift hypotheses. The required uniform heads remain unproved.

## Replay

    uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/logarithmic_rank_tail.py --coefficients research/certified_xi/coefficients_120.json --output research/certified_xi/logarithmic_rank_tail.json
    uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/certified_xi -p 'test_*.py'

Tests check exact head equality, each failed condition, the rational
one-step barrier inequality, rejection of the repeated-root control, and
domain validation. They do not discharge the Xi hypotheses. The analytic
comparison and persistent-surplus argument are written proofs, not Lean
formalized.

Validation: all 111 certified-Xi tests passed. Input/source hashes and the
five finite head ranks were checked; `git diff --check` passed.
