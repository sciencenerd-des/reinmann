# The actual folded Xi and its coefficients are now Lean-proved

[XiTaylorIdentification.lean](../Reinmann/XiTaylorIdentification.lean) removes
the Taylor-identification input from the Xi finite-PF limit route. The module
contains 24 kernel-checked statements. It does not assume a canonical product,
a sector theorem, coefficient positivity or RH.

## What the theorem identifies

The existing function `xiCompleted` is the entire pole-removing extension of
Riemann's xi, not the additive completed-zeta function with a different zero
set. Define

```
centeredXi z = xiCompleted (1/2 + z),
criticalXi z = centeredXi (I*z).
```

Both are proved entire. On the real axis `criticalXi` is exactly the complex
cast of the repository's real `Xi`. Restriction of an entire real-valued
function commutes with every iterated derivative. The Lean proof derives this
from uniqueness of the real and complex derivative and then induction; it
does not assume real analyticity of `Xi` as an independent input.

Composition with multiplication by `I` gives

```
criticalXi^(n)(z) = I^n * centeredXi^(n)(I*z).
```

At even order, `I^(2n)=(-1)^n`. Dividing by `(2n)!` proves

```
(XiMomentCoeff n : Complex) = centeredXi^(2n)(0)/(2n)!.
```

This is an identity of **ordinary** coefficients. No Jensen factorial or
Borel normalization is substituted.

## The global folding construction

The functional equation of completed zeta proves that `centeredXi` is even.
Its odd derivatives at zero therefore vanish. Mathlib's global complex Taylor
theorem and the even/odd reindexing of a convergent infinite sum give

```
HasSum (n ↦ XiMomentCoeff n * z^(2n)) (centeredXi z), for every complex z.
```

Define the formal scalar series with coefficients `XiMomentCoeff`, and let
`foldedXi` be its sum. Substitution at a complex square root proves convergence
of the folded series at every complex argument. Absolute summability follows
in the finite-dimensional complex normed space. Applying this at every
nonnegative radius proves that the formal series has infinite radius of
convergence. Its power-series sum is thus entire.

The proved identities are

```
foldedXi(z^2) = centeredXi z,
foldedXi z = xiCompleted(1/2 + Complex.sqrt z),
foldedXi^(n)(0)/n! = XiMomentCoeff n.
```

The second identity is global, including zero and the square-root branch cut.
Entirety comes from the power series, not from asserting that the principal
square root is holomorphic across its cut. The final identity follows from
uniqueness of analytic power series. It is exactly the input previously
left unproved in the Xi specialization of `AnalyticPFLimit`.

## Actual zeros and the PF-limit specialization

The module also proves conjugation symmetry and

```
foldedXi(-t^2) = Xi t,
foldedXi(-t^2)=0 iff riemannZeta(1/2 + I*t)=0, for every real t.
```

These theorems transfer an actual critical-line zero to a negative folded
zero. They do not assert that infinitely many such zeros exist.

`finitePF_xi_of_folded_locallyUniformLimit` now instantiates the general
analytic PF-limit theorem for this actual entire function. Its remaining
premises are construction of real polynomial approximants that converge
locally uniformly to `foldedXi`, and finite-PF nonnegativity of those
approximants. Their degrees are unrestricted. Taylor identification is no
longer a supplied premise.

## Remaining work toward all-shift order-three strictness

The [strictness argument](STRICT_FINITE_PF_FROM_REAL_ZEROS_2026_10_06.md) still
needs Lean proofs of:

1. The positive center value `xiCompleted(1/2)>0` in the real normalization.
2. The genus-zero canonical product and the real, conjugate-paired partial
   products, including the same construction after finite zero extraction.
3. The zero-free sector and polynomial sector-to-PF theorem.
4. Hardy's infinitude of critical-line zeros and finite factor extraction.

The third input is the classical result stated as Theorem B in
[Katkova's primary paper](https://arxiv.org/html/math/0505174), rechecked on
2026-10-06. The printed sector parameter supports the conservative PF43
baseline already documented in the repository. No claim of PF44 or of a
new sector theorem is made here.

The code search found no Schoenberg sector-to-PF theorem or Hardy infinitude
theorem in the current Mathlib checkout. `Mathlib.Analysis.Complex.Hadamard`
is the three-lines theorem; its filename must not be mistaken for a
canonical-product theorem. The available zeta-zero module proves discreteness
and finiteness in compact sets, which does not imply existence of infinitely
many critical-line zeros.

The next substantive proof is one of these remaining analytic inputs, not
a larger Python scan of shifts. The uniform prime integral estimate remains
verified separately; the intermediate Weil gap and the unbounded theta
curvature/budget are still open.

Verification and exact source hashes are recorded in the
[Xi Taylor ledger](prime_spectral/verification_2026_10_06_xi_taylor/manifest.json).
Earlier ledgers remain unchanged as snapshots of their own proof scopes.
