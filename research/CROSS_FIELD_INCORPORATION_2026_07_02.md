# Cross-Field Incorporation Review

**Date:** 2026-07-02
**Status:** feasibility review and Lean contract map; not a proof of RH.

## Executive verdict

The useful question is not "can elliptic curves, combinatorics, or geometry solve
RH by analogy?"  The useful question is:

> Can any outside field prove the concrete order-3 weighted-moment determinant
> inequality now isolated in `Reinmann/XiMomentKernel.lean`?

The current frontier target is:

```lean
MomentToeplitzOrder3Positive M
```

where `M n` is Pólya's even-moment sequence for the xi Fourier kernel and the
actual determinant is built from

```lean
weightedMoment M n = M n / (2n)!
```

The new Lean module `Reinmann/CrossFieldBridges.lean` registers four candidate
outside routes:

- `WeilHodgeOrder3Witness`
- `CombinatorialOrder3Witness`
- `EuclideanConvexityOrder3Witness`
- `HyperbolicSpectralOrder3Witness`

Each route must independently imply `MomentToeplitzOrder3Positive M`.  Anything
weaker is only decorative; anything equivalent to RH must be labeled as such.

## 1. Elliptic curves and algebraic geometry

### What transfers

The strongest successful RH analogy is the function-field story: for curves over
finite fields, including elliptic curves, the zeta function is controlled by
Frobenius eigenvalues.  The "RH" statement becomes a purity statement: eigenvalues
have the correct absolute value.  Weil's curve case and Deligne's higher-dimensional
proof are the real template.

Relevant references:

- James Milne, *The Riemann Hypothesis over Finite Fields: From Weil to the
  Present Day*: https://arxiv.org/abs/1509.00797
- Nicholas Katz, overview of Deligne's proof:
  https://web.math.princeton.edu/~nmk/old/DeligneRHOverview.pdf

### What it would mean here

To help our current problem, algebraic geometry must provide a model where the
order-3 weighted moment determinant is an intersection number or Hodge-Riemann
quadratic form.  Then positivity could come from hard Lefschetz / Hodge-Riemann,
not from zeta-zero assumptions.

Concrete target:

```lean
WeilHodgeOrder3Witness M
```

### Honest risk

There is no known variety, motive, Frobenius action, or cohomology group whose
trace data is exactly Pólya's xi-kernel weighted moments.  Without that object,
"elliptic curves" are only inspiration.  The actionable task is to search for a
cohomological realization of `weightedMoment M n`, not to invoke elliptic curves
generically.

Verdict: high conceptual value, high missing-object risk.

## 2. Combinatorics

### What transfers

This is the most immediately compatible field.  Our target is total positivity /
Pólya-frequency positivity, and those are already combinatorial themes.  Useful
subfields:

- Pólya-frequency sequences and infinite log-concavity.
- Planar network and lattice-path total positivity.
- Lorentzian polynomials and combinatorial Hodge theory.
- Matroid and valuated-matroid log-concavity.

Relevant references:

- Brändén-Chasse, *Infinite log-concavity for polynomial Pólya frequency
  sequences*: https://arxiv.org/abs/1405.6378
- Huh, *Combinatorics and Hodge theory*:
  https://web.math.princeton.edu/~huh/ICM2022.pdf
- Total positivity from lattice paths: https://arxiv.org/abs/2308.05167

### What it would mean here

Find a combinatorial model whose path weights or Lorentzian coefficients are

```text
M n / (2n)!
```

or whose minors specialize to the order-3 determinant in
`momentToeplitzOrder3_eq`.

Concrete target:

```lean
CombinatorialOrder3Witness M
```

### Honest risk

Ordinary moment positivity is Hankel positivity, which points in the wrong
direction.  The factorial denominator is doing the real work.  A valid
combinatorial model must encode that factorial slack structurally.

Verdict: best near-term route.  Search for lattice-path or Lorentzian
realizations of the factorial-weighted moment sequence.

## 3. Euclidean geometry and convexity

### What transfers

Euclidean convexity gives powerful inequalities for integrals and moments:
Brunn-Minkowski, Prékopa-Leindler, Alexandrov-Fenchel, and mixed-volume
log-concavity.  These theorems can prove log-concavity and ultra-log-concavity
when a measure has the right convexity properties.

### What it would mean here

The order-3 normalized ratio expression

```text
D_n = 1 - 2*x*z - y*w + x^2*w + y*z^2
```

would need to be bounded below by a convexity theorem applied to the xi-kernel
measure after factorial weighting.

Concrete target:

```lean
EuclideanConvexityOrder3Witness M
```

### Honest risk

Raw positive moments are log-convex, not log-concave.  Standard Euclidean moment
inequalities therefore push the wrong way unless the factorial normalization is
built directly into the geometric object.

Verdict: plausible only through a strengthened ultra-log-concavity or mixed-volume
interpretation of `M n / (2n)!`.

## 4. Non-Euclidean geometry and hyperbolic spectral theory

### What transfers

Selberg zeta functions on hyperbolic surfaces are the cleanest non-Euclidean
analogue: zeros are tied to Laplace spectrum and trace formula geometry.  This
connects geometry, closed geodesics, and spectral positivity.

Relevant reference point:

- Selberg zeta / hyperbolic surface zero distributions:
  https://arxiv.org/abs/1302.5928

### What it would mean here

We need a hyperbolic or trace-formula model whose spectral side produces the
weighted xi moment determinant and whose geometric side gives positivity.

Concrete target:

```lean
HyperbolicSpectralOrder3Witness M
```

### Honest risk

Selberg zeta has its own spectral operator.  The Riemann zeta does not currently
have a known self-adjoint geometric Laplacian model.  Without such a model,
non-Euclidean geometry becomes another Hilbert-Pólya restatement.

Verdict: valuable as a spectral design guide, but not a near-term route unless it
produces an explicit trace formula for the xi-kernel moments.

## 5. What to do next

### Priority A: combinatorial realization

Try to express the matrix

```text
[ weightedMoment M (m+i-j) ]
```

as a path matrix or coefficient matrix of a Lorentzian polynomial.  If that
works, total positivity could become a theorem from planar networks or
combinatorial Hodge theory.

### Priority B: algebraic-geometric positivity

Search for a cohomological object whose intersection pairing has determinant
equal to `momentToeplitzContigMinor M 3 (n+2)`.

### Priority C: convex asymptotics

Use the numerical hint

```text
D_n ~ constant / (n+1)^3
```

to prove an asymptotic lower bound for the normalized determinant.  This may be
more tractable than all-order total positivity.

## Bottom line

The best incorporation is not broad analogy.  It is this filtered plan:

1. Combinatorics first: PF, lattice paths, Lorentzian polynomials.
2. Algebraic geometry second: Hodge-Riemann/intersection positivity if a model is
   found.
3. Euclidean convexity third: only if it handles the factorial normalization.
4. Non-Euclidean geometry fourth: only if it yields an actual spectral trace
   model for the xi kernel.

The current Lean contracts make these standards explicit.  A cross-field idea
counts only if it supplies one of the registered witnesses in
`Reinmann/CrossFieldBridges.lean`.
