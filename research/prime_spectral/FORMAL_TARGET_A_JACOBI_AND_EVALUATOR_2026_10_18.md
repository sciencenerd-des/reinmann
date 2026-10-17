# Jacobi bridge and low-rectangle evaluator components

This round continues the author's explicit authorization of formal targets A and B.
The five commits ahead of origin were pushed through aba0f38; the sixth referenced
commit, 648b76c, was already upstream. GitHub CI passed on aba0f38:
https://github.com/sciencenerd-des/reinmann/actions/runs/39054708717 .
This CI result concerns that pushed snapshot, not the subsequent work below.

## Target A: the original coefficient minors

`ToeplitzComplement.lean` proves finite lower triangular Toeplitz multiplication
from ordinary power-series convolution. For f*g=1 and f_0=1, its Jacobi identity is

    det(f_(s+i-j))_(i,j<r) = (-1)^(rs) det(g_(r+i-j))_(i,j<s).

Negative coefficient indices are zero. The proof includes empty sizes and does
not assume either selected block is nonsingular. Multiplying the full matrix by
a matrix consisting of selected inverse columns and identity columns gives two
block triangular determinant evaluations. A finite cyclic permutation computes
the sign explicitly.

`ToeplitzComplementSigned.lean` proves the rectangle-area sign under z -> -z.
For g=1/F(-z), the two signs cancel: the small reciprocal determinant equals the
large original-coefficient determinant exactly. The module applies this equality
to the actual finite product from the preceding round and transfers the
root-order split-pair theorem to original coefficients at unbounded ranks.
No factorial normalization enters.

## Target A: the analytic extension remains incomplete

`SplitPairCauchyTail.lean` treats ordinary Taylor coefficients of an actual
analytic remainder g. A circle bound |g|<=C at radius R proves |g_n|<=C/R^n.
It also proves the Taylor-series identity and decay after normalization by any
d with |d|<R. An exact finite-pole coefficient decomposition then yields the
Cauchy error bound; coefficient decay is not assumed.

An additional divided-difference construction removes the principal part at
one actual simple zero, producing an analytic germ with an exact identity.

These are components of the entire-function extension, not the full genus-zero
split-pair theorem. Still required are patching the single-pole germs into a common finite-pole analytic
remainder and deriving its coefficient decomposition from the function identity, and the determinant estimate
for terms containing analytic remainder columns. Neither is supplied as a
completed theorem. Ties and multiplicities are not removed by assumption from
the existing PF-to-RH bridges. Those bridges and the RH capstones are unchanged.

## Target B: proved rules versus an actual rectangle certificate

`XiFiniteTheta.lean` bounds the actual omitted theta series, for t>=1:

    0 <= cosKernel(0,t)-1-thetaFinite(N,t)
      <= 4 exp(-pi (N+1)^2 t).

The uniform bound 4 exp(-pi (N+1)^2) survives multiplication by the actual Mellin
weight t^(s-1) whenever Re(s)<=1. Integration over [1,T] adds a factor T-1.
This error is separate from the previously proved integral truncation at T.

`EnclosureRules.lean` provides a quadrature rule with an error for every point
inside the tile, a midpoint version with a derivative bound and a sample error,
a derivative-to-variation rule, and a strictly positive modulus-margin rule.
Its floor-index construction proves coverage of the CLOSED rectangle by the
finite grid, including all edges and corners. A finite certificate assembly
lemma combines center enclosures and a genuine variation bound.

The assembly lemma requires its numerical and analytic premises to be proved.
No Xi center enclosures or positive per-tile margins are supplied in this round.
`ZetaNoLowStripZero (141/10)` consequently remains an explicit input in
`QuasiRHInputs.lean`; it is not discharged in either finite-PF theorem. A grid
sample, a winding count or an external Arb number is not a Lean rectangle proof.

## Prior art and exploratory theory

The bounded source audit is retained in this round's `prior_art.json`.
Loeffler–Stoll's named Mathlib nonvanishing theorem concerns Re(s)>=1:
https://afm.episciences.org/15954/pdf . OpenAI's exported theorem requires
Re(s)>7/8:
https://github.com/openai/math/blob/main/lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean .
Neither statement covers the central low-height rectangle. The search checked
56 root sources, three targeted detector sources (including LowGramHeight),
and an untruncated 414-path detector subtree; it does not claim
that no relevant result could exist anywhere else in the release.

`DENSITY_AND_EXACT_INTERPOLATION_2026_10_18.md` records the classical Jensen
obstruction to exact annihilation of a superlinear node count by a fixed-type
entire witness. It is qualitative, not a logarithmic detection theorem.
Forecasting remains closed.

## Validation

Development and final validation receipts are kept separately. The final
validation receipt and round manifest, once generated, bind the checked source,
build and axiom audit. A successful earlier build is not evidence that later
source edits compile. No publication is performed by these formal modules.
