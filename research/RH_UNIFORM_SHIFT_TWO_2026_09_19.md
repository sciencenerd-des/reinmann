# Shift two at every rank from three certified poles

Update (2026-09-20): the [correction refinement](RH_SHIFT_TWO_CORRECTION_2026_09_20.md)
now proves C_r(2)>11/[100(r+2)^2] at every rank and an exact convergent
cumulative sum. The scope statement below describes this original theorem;
the all-shift interior budget remains unproved.

## Result and scope

Using the same coefficient and analytic trust boundary as the
[shift-one certificate](RH_UNIFORM_BOUNDARY_CURVATURE_2026_09_15.md), this
calculation proves, for every integer r>=1,

    D_r(2)>0,
    0<t_r(2)=(r+2)/2 * D_r(1)D_r(3)/D_r(2)^2 <1.

Thus the normalized shift-two curvature delta_r(2)=-log t_r(2) is positive
at every rank. This result does not assume positive neighboring correction
factors at subsequent ranks: the required determinants are bounded directly.

The analytic tail begins at rank 45; certified coefficient intervals cover
ranks 1..44. The proof is analytic-numerical, not Lean formalized. It does
not prove the correction curvature C_r(2) is nonnegative, the cumulative
interior rank budget at every shift, or RH.

## 1. Exactly three poles in a bounded disk

Retain the notation

    E(z)=sum a_n z^n, a_n=mu_n/mu_0,
    F(z)=E(-z), H(z)=1/F(z)=sum h_n z^n.

Take the degree-120 coefficient polynomial P for F, R=800, S=1600.
Positive coefficients and the Xi theta identity give

    |F-P|<=tau=E(S)*2^-121 on |z|<=R,
    |F'-P'|<=121*tau/R.

The derivative bound follows because n*2^-n decreases for n>=121.
The special-function expression for E(S) is evaluated at the real argument
1/2+sqrt(S), with FLINT balls, exactly as in the shift-one proof.

A 512-arc contour computation uses Taylor translation on each arc disk.
Each image disk excludes zero, its modulus lower bound exceeds tau,
and the endpoint argument increments certify winding number three.
Rouche's theorem transfers that count to F. The function tail is below
1.328e-26; the polynomial modulus lower bound exceeds 4.3308e-7.

Three disjoint real sign-changing brackets, initially (199,201), (441,443),
and (624,627), account for all three zeros in the disk. Refinement gives
roots rho_1<rho_2<rho_3<R near

    199.79045483238686, 441.92615057408249, 625.54299689433.

The total zero count forces these roots to be simple and excludes any
additional zeros in the disk. Derivative enclosures also exclude zero.
The amplitudes a_l=-1/[rho_l F'(rho_l)] have signs +,-,+. Put
x_l=1/rho_l, so x_1>x_2>x_3>1/R.

Removing these three poles gives an analytic function on the closed disk:

    H(z)-sum_(l=1)^3 a_l/(1-z/rho_l).

On its boundary the absolute value is at most

    M=1/(min_circle|P|-tau)+sum_l |a_l|/(R/rho_l-1).

Cauchy's coefficient bound therefore proves, for every n>=0,

    h_n=sum_l a_l x_l^n+e_n, |e_n|<=M R^-n.             (1)

All roots, derivatives, amplitudes and M remain interval quantities in
this calculation. No rounded root table or global zero hypothesis is used.

## 2. Determinants and their leading pole terms

The dual Jacobi-Trudi identity gives

    D_r(m)=det[h_(r+i-j)]_(0<=i,j<m).

For a subset S of pole labels, define

    W(S)=(-1)^(m(m-1)/2) product_(l in S) a_l
         * product_(i<j in S) (x_i-x_j)^2/(x_i*x_j),
    |S|=m.

The determinant of the pole-only matrix is exactly

    sum_(|S|=m) W(S)*(product_(l in S) x_l)^r.           (2)

To see this, write the matrix as the sum of three rank-one matrices
with columns x_l^i, weights a_l*x_l^r and rows x_l^-j. Expanding and
using the Vandermonde determinant gives (2), including its sign.
The tests compare it directly with determinants of pole-only sequences.

For m=1,2,3, the leading subset S_m={1,...,m} has positive weight W_m,
because the amplitudes alternate +,-,+. Put lambda_m=product_(l=1)^m x_l.
Every other pure-pole subset in (2) has product strictly smaller than
lambda_m. Its absolute contribution relative to W_m*lambda_m^r is
therefore a decreasing geometric term.

## 3. Residual determinant errors without losing the cancellations

A bound that treats all entries independently is insufficient here:
it may allow a spurious contribution proportional to x_1^(2r)R^-r in
the size-three determinant. That contribution is identically zero.

Instead expand by columns. Select k>=1 residual columns E and assign
pole labels to the remaining m-k columns. **Repeated pole labels give
proportional columns and zero determinant**, even with residual columns
present. Only injective assignments f are retained.

For a fixed assignment and row permutation pi, the normalized absolute
term is bounded by

    M^k * product_(j not in E) [|a_f(j)| x_f(j)^(pi(j)-j)]
        * product_(j in E) R^(j-pi(j))
        * [R^-k product_(j not in E) x_f(j)]^r.         (3)

This follows from (1), since a residual entry in row i,column j has
absolute value <=M R^-r R^(j-i). It requires r>=m-1 so all coefficient
indices are nonnegative; the tail search starts at r=3.

Sum (3) over row permutations, injective pole assignments and residual
column sets. Divide by W_m*lambda_m^r and add the nonleading terms
from (2). This produces a finite explicit list

    |D_r(m)/(W_m lambda_m^r)-1| <= E_m(r),
    E_m(r)=sum_l K_(m,l) q_(m,l)^r, K_(m,l)>=0.         (4)

Every q_(m,l) is strictly between zero and one. For residual terms this
follows because each missing leading pole is replaced by 1/R<x_3;
nonleading pole selections only decrease the product further. The
implementation also verifies every ratio with interval arithmetic.
Thus every E_m decreases over the whole tail, not just sampled ranks.
The artifact records exact rational upper bounds for each K and q.

## 4. Uniform strengthened ratio bound from rank 45

At r=45 the computed normalized errors satisfy

    E_1 < 1.601e-14,
    E_2 < 4.191e-6,
    E_3 < 0.881640.

In particular E_1,E_2<1/2 and E_3<1. These inequalities hold for all
larger r by the geometric decrease. Therefore D_r(1),D_r(2),D_r(3)
are positive and

    D_r(1)<=2W_1 lambda_1^r,
    D_r(2)>W_2 lambda_2^r/2,
    D_r(3)<2W_3 lambda_3^r.

Since lambda_1*lambda_3/lambda_2^2=x_3/x_2, this gives

    0<t_r(2)<8(r+2)*W_1*W_3/W_2^2*(x_3/x_2)^r.        (5)

The upper bound at r=45 is below 0.000191179. Its successive ratio is

    (r+3)/(r+2)*(x_3/x_2),

which decreases in r and is below 0.721500 at r=45. Hence (5) stays
below one for every r>=45. This proves the entire infinite tail.

## 5. Finite bridge and completion boundary

Dual determinants computed from the certified coefficient input verify
D_r(1),D_r(2),D_r(3)>0 and 0<t_r(2)<1 for every r=1,...,44. The
bridge has no gap before the tail starting at 45. Its ratio intervals
are stored individually; a failed or inconclusive interval aborts the
certificate rather than being classified as a pass.

This closes the shift-two strengthened inequality at every rank under
the stated trust boundary. It adds a second established boundary column
for an eventual simultaneous rank induction. It does not remove the
need for an exterior condition at higher shifts.

Extending the pole argument to arbitrary shift would require compatible
information about arbitrarily many poles and remainders. Assuming all
those poles are real would introduce the very global zero information
being sought. The present proof uses only three poles certified inside
one fixed disk and makes no such extension.

## Replay and trust boundary

    uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/pole_shift_two.py --coefficients research/certified_xi/coefficients_120.json --output research/certified_xi/pole_shift_two.json
    uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/certified_xi -p 'test_*.py'

The trust boundary is coefficient enclosures, the Xi theta/special-function
identity, FLINT arithmetic, argument principle, Rouche, Cauchy, and dual
determinant algebra. The analytic argument is written, not Lean checked.
Tests exercise the exact spectral determinant formula, perturbed sequences,
the repeated-column cancellation, and rejection without pole separation.

Validation: 83 certified-Xi tests passed. The input/source hashes and
complete bridge 1..44 were verified; `git diff --check` passed.
