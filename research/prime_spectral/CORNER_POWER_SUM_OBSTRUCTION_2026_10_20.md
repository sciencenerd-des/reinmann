# What an exact corner identity would still have to prove

For an entire genus-zero product normalized as

    F(z)/F(0) = product_i (1+x_i z),    x_i = -1/a_i,

ordinary coefficients are elementary symmetric functions e_k(x). The contiguous
minor det(e_(s+i-j)) of order r is the rectangular Schur function s_(r^s)(x).
Jacobi's complementary identity exchanges this with an order-s determinant in
the complete symmetric functions h_k. This is the identity behind the targeted
DH shift-44 calculation; it applies to DH and zeta equally.

The Frobenius expansion expresses a Schur function through inverse-zero power
sums with character weights of both signs. Thus even positivity of **every**
power sum is insufficient. There is a small exact counterexample:

    F(z) = (1+z)(1+z/3+z^2/9),
    x = {1, exp(i*pi/3)/3, exp(-i*pi/3)/3}.

For k>=1 its power sum is

    p_k = 1+2*3^(-k)*cos(k*pi/3) >= 1/3,

but the order-three, shift-two minor of its ordinary coefficients is -23/729.
`Reinmann/CornerPowerSumCounterexample.lean` proves the real formula's bound,
the exact determinant, and failure of FinitePF at rank three, using standard
axioms only. The complex root interpretation above is explanatory algebra;
the module does not formalize a complex root-to-power-sum identification.

This example rules out the scalar-power-sum shortcut. It does not disprove a
stronger Euler-product identity. A proposed arithmetic identity must control
these mixed character terms on the actual ordinary coefficient sequence and
fail for DH. No such identity is supplied here. In particular, an explicit
formula for each power sum plus nonnegative prime weights is not yet that
identity. The retained DH rank-664, shift-44 negative minor remains the test
for any proposed sufficient corner criterion; no new grid scan is started.

The Schur identities are classical (dual Jacobi–Trudi and Frobenius character
formula), not a novelty claim. See Macdonald, *Symmetric Functions and Hall
Polynomials*, second edition, Chapter I, sections 3 and 7. The exact small
counterexample is a falsification test for this repository's proposed shortcut.
