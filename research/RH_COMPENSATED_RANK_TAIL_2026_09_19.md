# A compensated infinite rank-tail budget

Update: [the repeated-root control](RH_REPEATED_ROOT_RANK_CONTROL_2026_09_20.md)
proves that a positive uniform tail slope is not implied by real-rootedness
alone. This sufficient criterion remains valid but is not a universal
positivity criterion; the required Xi head growth still needs proof.

## Conditional theorem

This refines the [rank-tail bootstrap](RH_RANK_TAIL_BOOTSTRAP_2026_09_19.md).
It keeps the positive factorial baseline and the actual shift-dependent
factor alpha=m/(r+m). Neither term requires a new Xi assumption.

The conclusion remains conditional on positive neighboring correction
factors at every subsequent rank, or a compatible simultaneous induction
at all shifts. Passing finite heads do not establish those hypotheses.
No unconditional all-rank Xi or RH theorem is claimed.

Fix a shift m>=2 and a head rank R>=1. Suppose

    delta_R>=d>0, delta_R-delta_(R-1)>=v>0,
    0<b<v, n=R+m.

For j>=0 define

    z_j=m/(n+j)*exp(-d-j*b),
    s_j=log[(n+j)^2/((n+j)^2-1)].

Under the bootstrap hypothesis delta_(R+j)>=d+j*b, the exact correction
identity from the previous note gives

    C_(R+j)(m)>=s_j+2log(1-z_j).                        (1)

The neighboring logarithmic contributions have the correct nonnegative
sign under the stated positivity hypothesis and are discarded only for
a lower bound. Compared with the earlier estimate, alpha has not been
replaced by 1 and the positive baseline has not been dropped.

The baseline sum telescopes exactly:

    sum_(j=0)^(J-1) s_j
      =log[n*(n+J-1)/((n-1)*(n+J))].                   (2)

This formula also equals zero at J=0. It follows by cancelling the
factors (n+j)/(n+j-1) and (n+j)/(n+j+1).

Define the lower slope margins

    P_J=v-b+log[n*(n+J-1)/((n-1)*(n+J))]
          +2 sum_(j=0)^(J-1) log(1-z_j), P_0=v-b.      (3)

Choose any finite integer K>=0. The negative tail beyond K has the bound

    T_K=2z_K/[(1-z_K)(1-exp(-b))].                      (4)

Indeed z_(K+l)<=z_K*exp(-l*b), and
-log(1-x)<=x/(1-x). Replacing each denominator by 1-z_K and summing
the resulting geometric series proves (4).

**Theorem.** If P_J>=0 for J=1,...,K and P_K>=T_K, then

    delta_(R+j)>=d+j*b,
    delta_(R+j)-delta_(R+j-1)>=b

for every j>=0, subject to the recurrence and the neighboring-factor
hypothesis.

**Proof.** For steps J<=K, summing (1) bounds the new slope minus b
by P_J. For J>K, the first K terms contribute P_K, the remaining
positive baseline can be discarded, and the remaining negative terms
cost at most T_K. The slope therefore stays at least b in both cases.
Adding the slope proves the next curvature bound, starting from the
head value d. This is induction; the lower linear curvature bound is
used only for already-established steps when applying (1). QED.

The implementation uses strict ball inequalities, so inconclusive
endpoint equality is reported as unresolved. K=0 is supported: it
recovers an infinite geometric-tail criterion retaining alpha_R.
The default b=v/2 and K=16 are sufficient choices, not claimed optimal.

## What was checked on Xi

Fresh dual determinant evaluations from the 120-coefficient input give
the following first passing heads within the scanned rank range 2..113:

| Shift | Previous scalar budget | Compensated budget |
|---|---:|---:|
| 2 | 24 | 16 |
| 3 | 28 | 21 |
| 4 | 51 | 33 |
| 5 | 43 | 34 |
| 6 | 59 | 44 |

These are finite head witnesses to a conditional theorem. Each row stores
all 16 prefix margins and a rigorous upper bound for the **infinite**
residual loss. The finite prefix is evaluated from the explicit comparison
sequence d+j*b, not extrapolated from observed later Xi curvatures.

The saved classifier is `conditional_compensated_tail_pass`. It explicitly
retains the missing neighboring-factor hypothesis. In particular, an
exterior shift is still needed to close a finite strip, and the table
does not supply a compatible head region at every shift.

## Remaining analytic requirement

The simultaneous induction in the preceding note remains applicable:
prove the appropriate head inequalities up to some R(m) at every shift,
including a passing compensated budget at its endpoint. Positivity of
all B_r then follows within the induction from the preceding rank's
nonnegative curvatures. The separate shift-one boundary estimate is
unchanged. Uniform-in-shift head bounds remain unproved.

The compensated criterion is an improvement to the sufficient rank-tail
budget, not a replacement for those head bounds. The large-parameter
rank-two theta result does not establish them by itself.

A simple stronger head target is also available without choosing a prefix:
if 0<v<=2 and d>=log(32/v^2), the original scalar budget already passes
with b=v/2. Indeed exp(-d)<=v^2/32<=1/8, and
1-exp(-v/2)>=v/4, so its total loss is at most 2v/7<v/2.
This gives an explicit analytic target for the head curvature in terms of
the head slope. No assertion is made that Xi satisfies it at every shift.

## Replay and validation scope

    uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/compensated_rank_tail.py --coefficients research/certified_xi/coefficients_120.json --output research/certified_xi/compensated_rank_tail.json
    uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/certified_xi -p 'test_*.py'

The theorem above has a written elementary proof, not a Lean
formalization. Ball arithmetic checks the sufficient head conditions;
exact rational tests check the telescoping product. Recurrence tests
include adverse corrections and input rejection. None of these tests
verifies the missing all-shift Xi hypotheses.

Validation: 79 certified-Xi tests passed, input/source hashes match, and
`git diff --check` passed.
