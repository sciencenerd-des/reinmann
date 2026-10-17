# Formal target A: finite-product split-pair oscillation

The author authorized starting this target before publication on 17 October 2026. This supersedes the earlier release-only deferral in `POST_PUBLICATION_FORMAL_TARGETS_2026_10_15.md` and the earlier same-day status notes. The controls-paper publication gate is unchanged.

The target concerns the actual finite product

    B(z) = product_i (1−z/a_i),       h_n = [z^n] B(z)^(-1).

All coefficients are ordinary formal power-series coefficients; no factorial normalization enters.

All roots are nonzero and distinct, and conjugation permutes them. There is a conjugation-invariant inner set J, a nonreal conjugate pair p,q, and strict inverse-modulus ordering: every inner inverse zero is larger than the pair, and every other inverse zero is smaller. The product of the inner inverse zeros is a positive real number. Under these finite hypotheses, the complementary Toeplitz minors

    d_r = det(h_(r+i−j))_(0<=i,j<s),     s=|J|+1,

are real and strictly positive and strictly negative at unbounded ranks. Negative coefficient indices are defined to have coefficient zero. The main geometric theorem is `Reinmann.FiniteProductSplitPair.finite_product_split_pair_of_root_order`.

## What is proved

1. **Actual reciprocal coefficients.** Lagrange interpolation of the constant polynomial 1 gives the partial-fraction identity. A formal geometric series then proves the exact inverse-product coefficient formula. Residues are computed as products and proved nonzero; they are not supplied as an analytic assumption.
2. **Actual determinant expansion.** Multilinearity expands the determinant by row choices. Repeated poles vanish by alternation. Grouping surviving choices by their image gives the subset expansion. A square Vandermonde factorization computes the coefficient, including the column-reversal sign, and proves it nonzero.
3. **Root order implies subset dominance.** A finite exchange bijection proves strict product comparison between equal-cardinality subsets. The only tied exchange is the designated conjugate boundary pair. The geometric theorem derives these comparisons from the inner/pair/outer ordering; users need not assume a two-term asymptotic or verify every subset separately.
4. **Exponential tail.** The remaining subset bases, divided by the dominant modulus, have norm strictly below 1. A common rate 0<rho<1 exists, and the norm of their finite exponential sum is bounded by the sum of coefficient norms times rho^n. `exponential_remainder_bound` applies this to the actual finite-product determinant with its computed nonzero leading coefficient.
5. **Both signs without rotation density.** Two finite geometric sums bound the first and second moments of Re(w*u^n). Every block of length

       N > 4/|1−u²| + 6/|1−u|

   contains a phase below −1/4 and a phase above 1/4. A vanishing remainder preserves both signs at unbounded ranks. This treats rational and irrational angles together.
6. **Reality and controls.** Conjugation is transported through residues, subset coefficients and determinants. Concrete quadratic and cubic controls instantiate the theorem; the cubic has one positive inner inverse zero and the pair ±i, so it exercises shift 2.

The internal index is n>=0, corresponding to paper rank r=n+s−1. This removes negative powers from the algebra. The computed coefficient at n=0 is the paper's leading coefficient multiplied by the corresponding subset base^(s−1); nonvanishing and sign oscillation are unchanged. The final sign theorem uses the original rank and zero-extended coefficient convention.

## Files

| Module | Role |
|---|---|
| `SplitPairCoefficients.lean` | Finite-product inverse and nonzero residues |
| `SplitPairDeterminant.lean` | Row/subset expansion, Vandermonde formula and reality |
| `SplitPairModulusOrder.lean` | Strict finite exchange comparison |
| `SplitPairOscillation.lean` | Finite-block phases, geometric decay and sign stability |
| `FiniteProductSplitPair.lean` | Actual reciprocal-minor capstones and geometric root-order theorem |
| `FiniteProductSplitPairControl.lean` | Concrete quadratic and cubic instantiations |

The formal conclusion concerns the complementary reciprocal Toeplitz determinant itself. The separate Jacobi identity linking it to a large determinant of B’s original coefficients is not added by this round.

This is a classical finite-product theorem, with no novelty claim. It does not formalize the entire-function Cauchy remainder, the numerical DH atlas, the DH shift44 certificates, or an all-rank criterion for the actual Riemann xi function. It supplies no RH proof and removes no RH-strength obligation from the Toeplitz ladder.

## Validation

All final checks passed:

- Targeted build of `Reinmann.FiniteProductSplitPairControl`: 2163 jobs, including all six modules.
- Direct compilation of the full capstone and both concrete controls.
- Full project build: 3583 jobs.
- Standard source/semantic axiom audit: 285 theorems, including all 41 new theorems, with 0 sorry and 0 custom axioms. Only `propext`, `Classical.choice` and `Quot.sound` occur.
- `git diff --check`.

The strict build initially caught a finite-index simplification error in the cubic control; it was corrected before the final successful builds. The retained final logs do not count that failed development check as a pass.

Source and log hashes are recorded in `verification_2026_10_17_formal_A/validation.json` and the round manifest. The previous scientific closure is retained unchanged except for three explicitly updated files: README, the project root import list and AxiomAudit. The prior committed versions of those three files are retained under `historical_4989621/`. Historical manifests are not rewritten.

To verify the current checkout, run from the repository root:

```sh
lake build Reinmann.FiniteProductSplitPairControl
lake env lean Reinmann/FiniteProductSplitPair.lean
lake env lean Reinmann/FiniteProductSplitPairControl.lean
lake build
bash scripts/verify_axiom_clean.sh
python3 experiments/prime_spectral/verify_formal_A_round.py
```

No branch was pushed, no reviewer was contacted and no record was published by this formalization round. The controls PDF is unchanged from the preceding scientific closure.
