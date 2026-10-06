# A deformation that separates fixed-shift certificates from a global zero theorem

## Precise conclusion

The first 122 Taylor coefficients, the three certified interior zeros,
positive coefficients, and the strengthened all-rank inequalities at shifts
one and two do **not by themselves** force all folded zeros to be positive
real. The construction below preserves these data and inequalities while
adding an exact nonreal zero.

This is not a counterexample to RH. The deformed function is not Xi and
does not satisfy the original full Xi theta or arithmetic identity. No
claim is made that it preserves the imported PF43 baseline at all indices.
The obstruction applies to the specified finite-prefix and fixed-shift
information, not every available Xi-specific fact.

## 1. Exact deformation

Use the normalized entire functions

    E(z)=xi(1/2+sqrt(z))/xi(1/2)=sum a_n z^n,
    F(z)=E(-z), H(z)=1/F(z).

The square-root notation denotes the even entire expansion, as in the
previous certificates. Define L=3200,N=122, and

    E_tilde(z)=E(z)*(1+(z/L)^N),
    F_tilde(z)=F(z)*(1+(z/L)^N),
    H_tilde(z)=H(z)/(1+(z/L)^N).

The relation F_tilde(z)=E_tilde(-z) holds because N is even. Exactly,

    a_tilde_n=a_n                  for 0<=n<N,
    a_tilde_n=a_n+L^-N a_(n-N)    for n>=N.

All coefficients remain strictly positive. The first 122 coefficients
are identical, including every coefficient in the existing input through
index 120. The reciprocal coefficients likewise satisfy

    h_tilde_n=h_n for 0<=n<N,

by the formal geometric-series expansion of the reciprocal factor.

Since i^122=-1,

    F_tilde(iL)=0.

This is an exact nonreal zero at 3200i, not a numerical root estimate.
The multiplier has no zeros inside |z|<L. Hence the previously certified
three real zeros inside |z|=800 remain the complete set of zeros there,
with the same locations and multiplicities.

Multiplication by this finite polynomial also preserves entire-ness and
any finite entire-function order: on a sufficiently large circle its
modulus is bounded above and below by constant multiples of |z|^N.
The folded representation still gives an even function of the square-root
parameter. Thus these general analytic properties do not exclude the
construction either. The original Xi-specific identities do exclude it.

## 2. Residues and a new rigorous remainder

Let rho_l and a_l=-1/[rho_l F'(rho_l)] be the three certified poles and
amplitudes from the shift-two certificate. The new amplitudes are exactly

    a_tilde_l=a_l/[1+(rho_l/L)^N].                       (1)

At the root the derivative of the multiplier contributes zero because
F(rho_l)=0. The amplitude signs +,-,+ therefore remain unchanged.

Let R=800 and let ell>0 be the previous lower bound for |F| on |z|=R.
On that circle,

    |1+(z/L)^N|>=1-(R/L)^N>0,
    |F_tilde(z)|>=ell*[1-(R/L)^N].

Removing the same three poles from H_tilde, Cauchy's estimate gives

    h_tilde_n=sum_l a_tilde_l*rho_l^-n+e_tilde_n,
    |e_tilde_n|<=M_tilde R^-n,
    M_tilde=1/[ell*(1-(R/L)^N)]
            +sum_l |a_tilde_l|/(R/rho_l-1).             (2)

Equations (1)-(2) are evaluated with the original root and amplitude
intervals. No information about zeros outside the disk is assumed.
The added poles of H_tilde lie at modulus L and so do not interfere
with the analytic remainder on |z|<=R.

## 3. The two strengthened all-rank inequalities survive

Apply the rank-one-column determinant expansion from the
[shift-two proof](RH_UNIFORM_SHIFT_TWO_2026_09_19.md) to (2).
The interval calculation at rank 45 again satisfies

    E_1<1/2, E_2<1/2, E_3<1.

All normalized determinant error terms are decreasing geometric terms.
Their leading weights W_j and rates lambda_j now use the deformed
amplitudes and the unchanged pole locations. Consequently, for every
r>=45,

    0<t_tilde_r(1)
       <8(r+1)*W_2/W_1^2*(x_2/x_1)^r<1,
    0<t_tilde_r(2)
       <8(r+2)*W_1*W_3/W_2^2*(x_3/x_2)^r<1.

Both endpoint upper bounds and their successive geometric ratios are
checked strictly below one. The shift-one factor 8 comes from
D_r(2)<2W_2 lambda_2^r and D_r(1)>W_1 lambda_1^r/2.
The shift-two bound is the one in the previous proof.

For ranks 1..44, the required dual determinants use h indices no larger
than r+2<=46<N. They are therefore **exactly unchanged**, not just close.
The implementation rechecks the 88 finite ratio intervals (44 ranks,
two shifts). This joins the infinite tail without a gap.

Thus a function with an exact nonreal folded zero satisfies both
strengthened fixed-shift inequalities at every rank. This is stronger
than merely observing that a finite coefficient prefix is inconclusive.

## 4. Consequence for the RH program

The shift-one and shift-two results remain valid results for Xi under
their documented analytic-numerical trust boundary. The deformation
shows that the following inference is invalid:

    finite Xi coefficient agreement + these all-rank fixed-shift bounds
      implies all folded zeros are positive real.

A successful extension must add information that distinguishes Xi from
this deformation. Possibilities already in the research program include
a genuinely uniform all-shift theta estimate, a compatible all-shift
head region for the rank recurrence, or an independently proved arithmetic
spectral/convergence theorem. None has been supplied by this construction.

The counterexample does not rule out combining the fixed-shift results
with such additional information. It prevents treating more fixed-shift
certificates as an automatic passage to RH, and prevents assuming real
poles at arbitrary modulus as an unproved induction hypothesis.

## Replay and validation scope

    uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/fixed_shift_obstruction.py --poles research/certified_xi/pole_shift_two.json --coefficients research/certified_xi/coefficients_120.json --output research/certified_xi/fixed_shift_obstruction.json
    uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/certified_xi -p 'test_*.py'

The output is explicitly classified as a non-Xi obstruction, not an RH
counterexample. It records the modified Cauchy constant, all tail checks,
the inherited finite bridge, and the original certificate/coefficient hashes.
The analytic arguments are written, not Lean formalized.

Validation: 87 certified-Xi tests passed; source/input hashes and all 88
bridge cells were verified. `git diff --check` passed.
