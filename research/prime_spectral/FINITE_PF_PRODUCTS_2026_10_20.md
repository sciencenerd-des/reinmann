# Finite-PF product closure and reconciled sector boundary

## Status correction

The earlier `AnalyticPFLimit.lean` already proves coefficientwise finite-PF
closure and the locally uniform limit bridge for entire real-polynomial
approximants of unbounded degree. It predates the last two research commits.
Consequently `FinitePFLimits.lean` repeats an existing closure result, and
`FinitePFAnalyticLimits.lean` generalizes the analytic result to open domains
and arbitrary centres; neither first discharges a missing entire-polynomial
limit obligation. The last round's wording overstated that progress. This note
supersedes that status interpretation without rewriting immutable receipts.

The ordinary folded-Xi Taylor identification is also already proved as
`foldedXi_taylor`, and the positive centre is proved as
`foldedXi_zero_re_pos`. These are not newly open premises. Their declarations
and both older limit declarations are checked in a separate four-theorem
boundary audit in this round. The actual canonical product remains open.

## Product closure proved this round

`Reinmann/MatrixMinorProduct.lean` proves the row-choice determinant expansion
and a rectangular Cauchy–Binet identity, valid over any commutative ring:

\[
 k!\det(AB)=\sum_{p:\mathrm{Fin}(k)\to\mathrm{Fin}(N)}
   \det(A_{:,p})\det(B_{p,:}).
\]

The function-indexed sum includes repetitions, whose determinants vanish.
Each injective intermediate subset is counted k! times. The paired permutation
signs cancel. No division by k! is used in the ring identity.

`Reinmann/FinitePFConvolution.lean` sorts every injective intermediate map and
uses this identity to prove nonnegative product determinants over the reals.
For Toeplitz matrices the finite cutoff contains all selected row and column
indices; `ToeplitzComplement.toeplitz_mul` proves exact convolution, with no
discarded tail. This gives:

- `finitePF_mul` for ordinary formal power series;
- `finitePF_convolution` for ordinary sequence convolution;
- `finitePF_polynomial_mul` for real polynomials;
- `finitePF_one`, `finitePF_prod` and `finitePF_polynomial_prod`, including
  empty products and rank zero;
- `finitePF_linearFactor` and `finitePF_linear_polynomial`, transporting the
  earlier proved bidiagonal row-step lemma into the natural-index interface.

All arbitrary ordered minors through rank r are covered, with no rank loss.
No statement is made about factorial-weighted Jensen coefficients. These are
classical algebraic facts, not claims of new mathematics.

## Next genuine polynomial obligation

The missing factor-level result is the **arbitrary-minor** PF-r criterion for
the quadratic `1 + 2*cos(phi)*z + z^2` when
`0 <= phi <= pi/(r+1)`. The existing `ToeplitzQuadraticChebyshev` module proves
the tridiagonal contiguous determinant and sine quotient; that is not yet a
proof for arbitrary minors. A suitable next proof is to classify every
nonzero banded Toeplitz minor into contiguous tridiagonal blocks and triangular
pieces. The product-closure theorem then assembles admissible real linear and
conjugate quadratic factors, once their real factorization and sector geometry
are supplied. Boundary angles and multiplicities must be retained.

For folded Xi, one must still prove the actual genus-zero product identity and
inverse-zero summability, and construct conjugation-stable real polynomial
approximants. The generic convergence theorem `GenusZeroProductLimits` does not
identify an arbitrary entire function with that product. The existing Taylor
identity, positive centre, limit bridge and the new product closure can then be
used, with no Target A simple-zero or modulus-gap assumptions.

## Source check and an excluded shortcut

The [publisher record for Schoenberg's Palermo article](https://doi.org/10.1007/BF02846031)
confirms the title and pages. Its PDF link redirects to subscription access, so
the original proof has still not been read here. The separately read
[Ragnarsson–Suen–Wagner correction](https://arxiv.org/pdf/math/0406309)
rules out fixed-rank reciprocal PF transport. Its example
`f=1+4z+3z^2+z^3` is PF2, whereas `1/f(-z)` has coefficients
`1,4,13,41,129,406,...` and the rank-two minor
`129^2-41*406=-5`. The corrected result exchanges rank with minor level, not
with the same rank. None of the new product proofs uses this false transport;
the existing Jacobi complementary identity also keeps the swapped sizes.

## Verification and release boundary

Fresh builds, source elaborations, the fourteen-declaration new axiom audit,
the four-declaration prior-boundary audit, default build and root guard are
recorded in `verification_2026_10_20_products/`. These modules are explicit Lake
targets, outside the unchanged root import and its 1619-declaration audit.
The default build transcript is stored with lossless gzip compression and its
uncompressed SHA256. No old verification manifest is modified.

Replay the saved receipts with
`python3 experiments/prime_spectral/verify_finite_pf_products.py`;
rebuild the new proofs with `lake build Reinmann.FinitePFConvolution`.
Receipt replay checks the saved outputs and source bindings, not hosted CI.

At preparation of this note the default job of
[Target B run 39425081613](https://github.com/sciencenerd-des/reinmann/actions/runs/39425081613)
had passed and the numerical certificate job was still running. The CI-gated
README/objective patch remains unapplied. `KatkovaSectorBridge 43` remains
open. Height 14.1 and all published versions remain unchanged; no RH claim is
made.
