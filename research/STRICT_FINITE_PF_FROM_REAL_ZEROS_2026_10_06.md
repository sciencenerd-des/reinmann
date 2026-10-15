# Strict contiguous finite-order positivity by extracting real zeros

The missing low-rank strictness can be addressed by a classical factorization
argument. It does not require a uniform saddle-curvature theorem. This note
separates the analytic deduction from its Lean algebraic implementation;
the analytic Xi inputs are not yet formalized in this project.

## 1. General statement

Let `F(z)=sum a_n z^n` be a real entire function with `F(0)=C>0` and a
genus-zero canonical product. Suppose:

1. Every zero lies outside the open sector `|arg z|<r*pi/(r+1)`.
2. There are infinitely many negative real zeros, counted with multiplicity.

Here `r>=1` is **fixed**. Define the zero-extended contiguous minor

```
D_k(m) = det[a_(m+i-j)]_(i,j=0,...,k-1),   a_n=0 for n<0.
```

For every `m>=0` and every `1<=k<=r`, choose any `m` negative real zeros
`-lambda_1,...,-lambda_m`, with `lambda_j>0`. Then

```
D_k(m) >= ( C * product_(j=1)^m lambda_j^(-1) )^k > 0.
```

The choice of the extracted zeros may depend on `m`. The bound may be
extremely small. It is a strictness witness, not an efficient numerical
conditioning estimate. Its rank quantifier stops at the given `r`.

## 2. Why the quotient is still PF_r

Put `P_m(z)=product_(j=1)^m(1+z/lambda_j)` and `G_m=F/P_m`.
Deleting finitely many factors from an absolutely convergent genus-zero
canonical product leaves a locally uniformly convergent product. The
remaining zero set has the same sector exclusion, and `G_m(0)=C`.

Group each nonreal zero with its conjugate when taking finite partial
products. The partial products are therefore **real** polynomials with
positive constant term and zeros outside the specified sector.
Schoenberg's polynomial sector theorem gives PF_r for each such polynomial.
Locally uniform convergence implies coefficient convergence; every fixed
Toeplitz minor is a polynomial in finitely many coefficients. Nonnegativity
thus passes to `G_m`.

This uses the sector theorem on the quotient's own canonical partial
products. It does **not** assert that division by a positive linear factor
preserves arbitrary PF_r sequences; that would be a different assertion.

The sector theorem is stated as Theorem B in
[Katkova, *Multiple positivity and the Riemann zeta-function*](https://arxiv.org/html/math/0505174).
Its reference [29] is
[Schoenberg, *A note on multiply positive sequences and the Descartes rule of signs*,
Rend. Circ. Mat. Palermo 4 (1955), 123–131](https://link.springer.com/article/10.1007/BF02846031).
The publisher confirms the bibliographic details; its full text is behind
subscription access. The accessible mathematical statement checked here
is Katkova's printed Theorem B. A direct original-text verification remains
desirable before citing this deduction as a publication theorem.

## 3. The strict witness: two equivalent algebraic proofs

Write `p_n` and `g_n` for the ordinary coefficients of `P_m` and `G_m`.
Zero extension gives the finite Toeplitz convolution factorization.
Cauchy–Binet expresses `D_k(m)` as a sum of products of ordered minors of
`T(p)` and `T(g)`. Only finitely many intermediate indices contribute:
they are bounded above by `m+k-1`.

All products are nonnegative: `P_m` is PF_infinity and `G_m` is PF_r.
Keep the intermediate indices `0,...,k-1`. The `P_m` block with rows
`m,...,m+k-1` and those columns is upper triangular, because `p_n=0`
for `n>m`; its diagonal is `p_m=product lambda_j^(-1)`.
The `G_m` block at shift zero is lower triangular with diagonal `C`.
This term alone is `p_m^k C^k`, proving the claim.

The Lean proof uses a smaller direct alternative, avoiding a new general
rectangular Cauchy–Binet development. Multiplication by `1+t*z` acts on
integer-indexed rows as

```
A'(i,j) = A(i,j) + t*A(i-1,j).
```

Multilinearity expands any ordered minor into the `2^k` choices of a row
or its predecessor. Since the original integer rows are strictly ordered,
each chosen sequence is weakly ordered. A collision gives determinant
zero; otherwise it is an ordered minor of `A`. For `t>=0`, all terms
are nonnegative. Keeping the all-predecessor choice proves

```
D_k(m+1; A') >= t^k * D_k(m; A).
```

Iterating over the `m` extracted factors gives the displayed strict lower
bound. Integer rows eliminate predecessor truncation ambiguity at zero;
the natural-number Toeplitz extension adds only zero negative rows.

## 4. Application to the folded Xi function

Take `F(z)=xi(1/2+sqrt(z))`, interpreted through its even Taylor series.
The existing conservative sector baseline is `r=43`; see
[the baseline audit](FINITE_PF_BASELINE_2026_09_13.md). The genus-zero
product and positive constant are the same classical inputs used there.

[Hardy's original 1914 note, *Sur les zéros de la fonction ζ(s) de Riemann*,
Comptes rendus 158, 1012–1014](https://fr.wikisource.org/wiki/Page:Comptes_rendus_hebdomadaires_des_s%C3%A9ances_de_l%E2%80%99Acad%C3%A9mie_des_sciences,_tome_158,_1914.djvu/1014)
proves infinitely many critical-line zeros. Nonzero ordinates `gamma`
give negative folded zeros `-gamma^2`. Thus the general argument yields

```
D_k(m; F) >= (xi(1/2) * product_(j=1)^m gamma_j^(-2))^k > 0,
             every m>=0, every 1<=k<=43.
```

This is a deduction from established classical inputs, **not a novelty
claim** and not an RH proof. It closes the written low-rank contiguous
strictness argument, subject to those explicitly identified classical
inputs. In particular it avoids computing the huge region below a
fixed-rank tail-wedge threshold. It does not prove the separate uniform
degree-16 curvature estimate, all-rank theta budget, or Weil intermediate
constrained gap.

## 5. Lean scope and next analytic work

[FinitePFStrict.lean](../Reinmann/FinitePFStrict.lean) develops the determinant
expansion, ordered-minor transport, iteration and positive diagonal witness.
`linearFactors` uses **ordinary** coefficient convolution. It does not
replace coefficients by factorial-scaled Jensen coefficients.

The actual folded Xi and Taylor identification are now proved in
[XiTaylorIdentification.lean](../Reinmann/XiTaylorIdentification.lean).
`foldedXiSeries` has infinite radius; its sum is entire and equals
`xiCompleted (1/2+Complex.sqrt z)` for every complex `z`, including zero and
the branch cut. `foldedXi_taylor` identifies its ordinary coefficients with
`XiMomentCoeff`, without an analytic hypothesis. `foldedXi_neg_square_zero_iff`
identifies the negative folded zeros coming from the critical-line zeta zeros.

The fully analytic Lean strictness theorem still needs:

- The positivity of the center value `xiCompleted (1/2)`.
- The classical canonical product, the sector exclusion, and the polynomial
  sector-to-PF theorem.
- Hardy's infinitude theorem and the corresponding finite factor extraction.

[AnalyticPFLimit.lean](../Reinmann/AnalyticPFLimit.lean) now proves the actual
locally uniform limit leg: polynomial derivative convergence at every fixed
order, ordinary coefficient convergence **without a degree bound**, and
finite-PF closure under coefficientwise limits. Its combined real-polynomial
theorem takes locally uniform complex convergence, PF_r of the approximants,
and the target Taylor identification as explicit inputs. The new
`finitePF_xi_of_folded_locallyUniformLimit` instantiates that last input with
the unconditional folded Xi theorem. This removes the
limit passage from the list of missing general bridge theorems. It does not
construct the Xi canonical approximants or prove their sector positivity.

The source of the derivative-limit step is Mathlib's
`TendstoLocallyUniformlyOn.deriv` in
`Mathlib/Analysis/Complex/LocallyUniformLimit.lean`. Repeated application
works because every polynomial derivative remains entire. The existing
bounded-degree Lagrange interpolation result would not suffice for these
partial products. The new theorem does not impose a hidden degree cap.

The two new PF modules contain 21 kernel-checked supporting theorems;
the integrated-family addition to `FiniteShiftChains` contributes four more.
The full-project verification and axiom ledger are recorded separately from
the mathematical statement of the classical Xi deduction.

These are missing formal proofs, not declarations of custom axioms. Python
sampling cannot supply them. The main search direction is now the remaining
Lean canonical-product, sector-positivity, positive-center and Hardy proofs
rather than a scan of the intermediate shift range.

Verification: full `lake build` passed (3530 jobs); the axiom guard passed
166 audited statements using only `propext`, `Classical.choice`, `Quot.sound`;
the shortcut scan covered 80 files. Direct verification of `FinitePFStrict`,
`AnalyticPFLimit` and `FiniteShiftChains` also passed. Logs and source hashes
are in [the continuation ledger](prime_spectral/verification_2026_10_06_lean_continuation/manifest.json).
These counts refer to that earlier snapshot. The 24 actual Xi Taylor and
folding proofs have a separate
[verification ledger](prime_spectral/verification_2026_10_06_xi_taylor/manifest.json).
