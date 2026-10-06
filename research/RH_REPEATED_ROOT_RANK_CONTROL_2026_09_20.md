# An exact all-rank control for the cumulative-budget method

## Finding

The existing scalar and compensated tail criteria require an eventual
strictly positive lower bound on the rank slope of delta. That requirement
is stronger than real-rootedness and positivity of the relevant determinants.
An exactly solvable polynomial family demonstrates the distinction at
every rank, with all neighboring-factor hypotheses satisfied.

This does not falsify either conditional theorem and is not a Xi
counterexample. It means that their positive-slope hypothesis needs its
own Xi-specific proof; real-rootedness alone cannot supply it. A more
general cumulative-budget program should allow a slope tending to zero
and retain the neighboring contributions that compensate the losses.

## 1. Exact determinant family

Let N>=4 be an integer and

    E_N(z)=(1+z/N)^N,
    a_n=binomial(N,n)/N^n for 0<=n<=N, and zero otherwise.

Every zero equals -N, with multiplicity N. Let D_r(m) be the repository's
contiguous Toeplitz determinant, P_r(m)=product_(j=0)^(r-1) j!/(m+j)!,
and A_r(m)=D_r(m)/P_r(m). Then, for 0<=m<=N and every integer r>=0,

    A_r(m)=N^(-r*m)*product_(i=1)^m product_(j=1)^r (N+j-i).   (1)

These values are strictly positive. For r>=1 and m>N the determinant
is zero: the diagonal and all entries below it have indices greater than
N, so the matrix is strictly upper triangular. The shift-zero determinant
is one, and the rank-zero determinant is the empty determinant one.

**Proof of (1).** At ranks zero and one it is immediate from a_m and
P_1(m)=1/m!. At r>=1, ratios of the candidate products give

    t_r(m)=A_r(m-1)A_r(m+1)/A_r(m)^2
           =(N-m)/(N-m+r),
    A_(r+1)(m)A_(r-1)(m)/A_r(m)^2
           =(N+r)/(N-m+r)=1+(m/r)(1-t_r(m)).           (2)

For m=N use the zero determinant at shift N+1, so t=0 and the second
identity still holds. Thus the candidates satisfy normalized condensation
with the exact initial rows and boundaries. Inductively, the denominator
A_(r-1)(m) is positive for m<=N, so condensation determines the next row
uniquely. The actual determinant array must therefore equal (1).
This proves the formula at every rank, without extrapolating a finite scan.

## 2. Interior curvature and correction at all ranks

Fix 2<=m<=N-2 and put K=N-m>=2. Then the central and both neighboring
t values are strictly positive, and all B values are positive, for every
r>=1. The exact formulas are

    t_r(m)=K/(K+r),
    B_r(m)=(N+r)/(K+r),
    delta_r(m)=log(1+r/K),
    C_r(m)=log(1-1/(K+r)^2)<0.                        (3)

The neighboring B factors in (3) must both be retained to obtain this
exact correction. Equations (3) satisfy the logarithmic curvature
recurrence, and delta_r(m)>0 at every positive rank, although C is
negative at every rank.

At a head R>=1 let x=K+R. The current slope is

    v_R=delta_R-delta_(R-1)=log[x/(x-1)]>0.

The correction sum telescopes exactly. For every J>=0,

    product_(j=0)^(J-1) exp(C_(R+j))
        =(x-1)*(x+J)/[x*(x+J-1)],
    v_R+sum_(j=0)^(J-1) C_(R+j)
        =log[(x+J)/(x+J-1)]>0.                       (4)

The last expression tends to zero, so

    sum_(j=0)^infinity C_(R+j)=-v_R.

Every finite cumulative slope budget is positive, but the infinite loss
uses exactly the entire initial slope. There is no positive residual
slope margin. The curvature itself remains positive and grows like log r.

## 3. Consequence for the current sufficient criteria

Both [the scalar criterion](RH_RANK_TAIL_BOOTSTRAP_2026_09_19.md) and
[the compensated criterion](RH_COMPENSATED_RANK_TAIL_2026_09_19.md) imply

    delta_(R+j)>=d+j*b for every j>=0, with b>0.

Neither can pass any head of the family (1) at the interior shifts above,
even with exact head data and all their neighboring-factor hypotheses.
Otherwise their valid conditional conclusions would contradict
log(1+(R+j)/K)/j -> 0. This is an all-rank obstruction to those sufficient
conditions, not merely failure of their chosen default b=v/2 in a scan.

For the RH program this leaves two distinct options:

1. Prove the required stronger growth for the actual Xi array, rather
   than assuming that positivity or real zeros imply it.
2. Develop a cumulative comparison that allows the limiting slope margin
   to be zero while keeping every finite prefix nonnegative, as in (4).

This control does not establish either option for Xi. In particular it
does not prove that Xi fails the current criteria, and no statement about
Xi zero multiplicities is inferred from this polynomial example.

## Replay and validation

    uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/repeated_root_rank_control.py --output research/certified_xi/repeated_root_rank_control.json
    uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/certified_xi -p 'test_*.py'

Tests compare (1) with exact rational determinants, check condensation
and the telescoping product, and confirm that the existing implementations
reject representative control heads. The all-rank conclusion is the
written induction and limit proof above; the finite tests validate code.
The Xi all-rank budget and RH remain unproved.

Validation: all 106 certified-Xi tests passed, the saved control's source
hash matches, and `git diff --check` passed. The all-rank argument is not
Lean formalized.
