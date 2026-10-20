# Analytic limit step for the finite-PF sector route

The coefficientwise closure theorem in `FinitePFLimits.lean` now has an analytic
application layer. These are formalizations of classical limit arguments, not
new mathematical claims or a discharge of `KatkovaSectorBridge 43`.

## Completed this round

`Reinmann/FinitePFAnalyticLimits.lean` proves:

- `iteratedDeriv_locallyUniformly`: on an open complex domain, locally uniform
  convergence of eventually holomorphic functions commutes with every iterated
  derivative. This uses Mathlib's proved Weierstrass derivative theorem.
- `ordinaryCoeff_tendsto`: at any centre in the domain, the coefficients
  `iteratedDeriv n f c / n!` converge. The factorial is essential; these are
  ordinary coefficients, not classical Jensen coefficients.
- `finitePF_of_locallyUniformly`: eventual finite PF of the real parts of those
  coefficients passes to the analytic limit, for all arbitrary minors through
  the given rank. Projection to real parts does not assert that the original
  complex coefficients are real.
- `polynomial_ordinaryCoeff`: for every complex polynomial and every index,
  the ordinary analytic coefficient at zero is the actual polynomial
  coefficient, including indices above the degree.
- `finitePF_of_polynomial_locallyUniformly`: genuine real polynomial
  approximants with eventually PF-r coefficient sequences give PF-r for the
  real ordinary coefficients of their locally uniform limit. Polynomial
  holomorphy and the coefficient identity are proved internally, not added as
  application premises. The limit filter must be nontrivial.

`Reinmann/GenusZeroProductLimits.lean` proves, from the explicit assumption
`Summable (fun i => ‖u i‖)`:

- the products of `1 + u i * z` converge locally uniformly on the entire plane;
- their infinite product is entire, including at zeros of individual factors;
- the finite-product net converges in every ordinary Taylor coefficient at
  every complex centre.

The product proof bounds the factors on each compact set and uses Mathlib's
uniform product convergence theorem. It does not exclude repeated parameters,
zeros of factors, or modulus ties. Repeated zero factors remain separate
indexed factors. It is a convergence theorem; it makes no assertion that an
arbitrary entire function equals this product.

## What remains for rank 43

1. Schoenberg's polynomial sector sufficiency theorem for **all arbitrary
   minors**, with the conservative rank-43 angle convention.
2. Folded Xi's actual genus-zero product identity and summability of its
   inverse-zero norms. The general convergence theorem alone is not an
   identification of that product with Xi.
3. Conjugation-stable real polynomial approximants to that product, allowing
   multiplicities and ties, and the identity of their limiting ordinary
   coefficients with `XiMomentCoeff`.

The last limit passage is now proved. Target A's simple-zero and gap hypotheses
are not used in these new modules and must not be imported into this route.

## Verification and status

Both modules are checked as explicit Lake targets. The independent eight-public-
declaration axiom audit is in `verification_2026_10_20_analytic_limits/`, along
with fresh source elaborations, the default build and root guard, command
timings, and checksum bindings. Their semantic dependency lists contain only
Lean's three standard foundational axioms. They are not added to the root
import or its existing 1619-declaration audit in this round.

Run `python3 experiments/prime_spectral/verify_analytic_pf_limits.py` to verify
the saved evidence and its parent checkpoint. This is a receipt replay, not a
substitute for a fresh Lean build. The explicit build is
`lake build Reinmann.GenusZeroProductLimits`.

Target B's proof-source CI run remains separately gated at
[39425081613](https://github.com/sciencenerd-des/reinmann/actions/runs/39425081613).
The default job passed; at preparation of this note, the numerical certificate
job was still running. The CI-dependent table patch remains unapplied. Height
14.1 and the published Zenodo versions remain unchanged. Neither finite PF at a
fixed rank nor these limit lemmas prove RH.
