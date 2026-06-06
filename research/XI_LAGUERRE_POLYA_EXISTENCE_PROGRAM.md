# Xi Laguerre-Polya Existence Program

**Date:** 2026-06-06
**Status:** research program and proof target, not a proof of RH.

## Executive claim

The requested theorem,

> canonical scaled finite products over real paired roots converge locally to
> `Xi`,

is exactly the Laguerre-Polya membership assertion for `Xi`.  For the Riemann
xi function this is RH-level mathematics: proving it without assuming RH would
prove that all nontrivial zeta zeros lie on the critical line.

Therefore the honest next step is not to assert the existence theorem.  The
next step is to identify a new independent mechanism that would force it.  The
most concrete candidate is the **Aperture Closure Program** below.

## Literature review

### 1. Pólya-Jensen criterion

Pólya proved that RH is equivalent to hyperbolicity of all Jensen polynomials
attached to the Taylor coefficients of the xi function at the symmetry point.
The modern formulation is:

1. write
   `xi(1/2 + z) = Σ gamma(n) z^(2n) / n!`;
2. define `J_{d,n}(X) = Σ_{j=0}^d binom(d,j) gamma(n+j) X^j`;
3. RH is equivalent to hyperbolicity of every `J_{d,n}`.

This is already encoded in Lean as `PolyaJensenBridge`.

### 2. What is already known unconditionally

Griffin-Ono-Rolen-Zagier prove asymptotic hyperbolicity: for each fixed degree
`d`, the Jensen polynomials eventually become hyperbolic as the shift `n`
grows.  Their proof models normalized Jensen polynomials by Hermite
polynomials.  The later xi-specific work of Griffin-Ono-Rolen-Thorner-Tripp-
Wagner makes parts of this effective and relates finite zero verification for
derivatives of xi to hyperbolicity ranges.

Csordas-Norfolk-Varga and Csordas-Varga-Vincze prove low-degree and inequality
fragments: Turan and Laguerre-type inequalities, plus applications to xi.  These
are strong finite rungs, not a full all-`d,n` proof.

O'Sullivan gives a modified Jensen criterion using Hermite-polynomial
combinations and sharper asymptotics.  This matters because the natural
asymptotic object is not raw monic finite products but a normalized Hermite
limit.

### 3. de Bruijn-Newman dynamics

de Bruijn-Newman theory studies a heat-flow deformation `H_t` of `Xi`.
RH is equivalent to the de Bruijn-Newman constant satisfying `Lambda <= 0`.
Rodgers-Tao proved Newman's complementary conjecture `Lambda >= 0`, using zero
dynamics and local spacing information.  This does not prove RH, but it gives
the strongest known dynamical evidence that any proof must control local
zero motion at the threshold.

### 4. Consequence for this repo

The repo's `XiLaguerrePolyaScaledFiniteTarget` is the correct Lean target, but
it is not a lemma one should expect to prove from ordinary functional equation
symmetry.  Symmetry gives evenness and paired principal-value cancellation at
the origin.  It does not force real-rooted approximants.  The missing input must
control zero locations, coefficient total positivity, or heat-flow stability.

## New theory: Aperture Closure

### Intuition

Known results nearly close the Jensen/Laguerre-Polya route in two directions:

1. **Tail direction:** for fixed `d`, high shifts `n` are hyperbolic.
2. **Low-degree direction:** for fixed small `d`, all shifts `n` are hyperbolic
   or satisfy strong Turan/Laguerre inequalities.

The unresolved region is an infinite wedge:

```text
degree d
^
|        unknown aperture
|       /
|      /
|     /     known eventually in n for fixed d
|    /
|   /
|  /________________________> shift n
   known low-degree strip
```

The Aperture Closure Program proposes a new theorem that collapses this wedge:
the same normalization that makes high-shift Jensen polynomials converge to
Hermite polynomials should also produce a monotone hyperbolicity barrier in
`d/n` once the finite low-degree boundary and Turan curvature are known.

### Proposed theorem A: Hermite aperture barrier

Let `gamma(n)` be the xi coefficient sequence and let `Jhat_{d,n}` be the
Griffin-Ono-Rolen-Zagier normalized Jensen polynomial.  There should exist a
computable barrier function `B(d)` with the following properties:

1. `Jhat_{d,n}` is a small Hermite perturbation for `n >= B(d)`.
2. For `n < B(d)`, hyperbolicity is forced by a finite family of Laguerre
   inequalities of order at most `O(B(d))`.
3. These finite Laguerre inequalities are implied by a single positivity
   statement for the xi heat-flow kernel at `t = 0`.

If true, this converts the infinite all-`d,n` Jensen condition into a finite
positivity aperture for each degree plus a uniform barrier theorem.

### Proposed theorem B: heat-flow aperture monotonicity

Define the Jensen discriminant deficit

`D_{d,n} = distance(Jhat_{d,n}, Hyperbolic_d)`

in a coefficient-space metric natural for Hermite normalization.  The desired
monotonicity is:

`D_{d,n+1} <= q_{d,n} D_{d,n}` with `0 <= q_{d,n} < 1`

outside a computable finite aperture.

This is not known.  It is the new mathematical payload.  The reason it is
plausible is that the normalized coefficient ratios already exhibit Hermite
asymptotics, while de Bruijn-Newman dynamics supplies a separate zero-flow
language where local equilibrium is rigid.

### Proposed theorem C: total-positivity kernel criterion

Let `Phi(u)` be the xi Fourier kernel in the de Bruijn-Newman representation.
Instead of proving real-rootedness of the canonical products directly, prove
that the moment kernel induced by `Phi` is `TP_infty` after the xi normalization.
By the Edrei-Schoenberg philosophy, total positivity would imply
Laguerre-Polya membership, hence the existence of real-rooted finite
approximants.

This is the cleanest non-circular target because it is a statement about a
positive kernel/moment matrix, not a statement about zeta zeros.

## Formalization plan

### Lean target 1: normalized approximant shape

Already present:

- `xiEvenScaledProduct`
- `XiLaguerrePolyaScaledFiniteWitness`
- `XiLaguerrePolyaScaledFiniteTarget`

Next refinement:

```lean
structure CanonicalXiProductWitness where
  witness : XiLaguerrePolyaScaledFiniteWitness
  normalizedAtZero :
    forall n, witness.approximants n 0 = Xi 0
  rootWindowExhaustive :
    Prop
```

The field `rootWindowExhaustive` should later say that `zeroPairs n` are not
arbitrary real roots; they are the first `n` canonical xi zero parameters under
a verified enumeration/order.

### Lean target 2: aperture closure contract

```lean
def HermiteApertureClosure : Prop :=
  XiLaguerrePolyaScaledFiniteTarget -> AllJensenHyperbolic
```

This is currently represented by `XiLaguerrePolyaClosureBridge`.  The next
formal step is to split it into:

1. finite-product convergence implies Laguerre-Polya membership;
2. Laguerre-Polya membership implies Jensen hyperbolicity;
3. Jensen hyperbolicity plus `PolyaJensenBridge` implies RH.

### Lean target 3: total positivity matrix

Define finite Hankel matrices of the signed xi moment coefficients:

`mu_n = (-1)^n XiCoeff n`

`H_N(i,j) = mu_{i+j}` for `0 <= i,j <= N`.

The sign is not optional.  A real-rooted even Hadamard product has the shape
`C * product_k (1 - t^2/tau_k^2)`, so the raw Taylor coefficients in `t^(2n)`
alternate.  The moment-like positive sequence is `mu_n`, not the raw
`XiCoeff n`.

Then define:

`XiTotalPositiveFinite := forall N, every minor of H_N is nonnegative`.

The new analytic theorem would be:

`XiTotalPositiveFinite -> XiLaguerrePolyaScaledFiniteTarget`.

This gives a concrete bridge from coefficient positivity to real-rooted
approximants.

**Lean status:** this is now formalized in
`Reinmann/XiTotalPositivity.lean` as:

- `XiMomentCoeff n = (-1)^n * XiCoeff n`;
- `XiHankelMatrix N m`;
- `XiHankelDet N m`;
- `XiHankelTotalPositive`;
- `XiHankelDet_one`;
- `xiMomentCoeff_nonneg_of_hankelTotalPositive`;
- `XiHankelDet_two`;
- `xiMomentCoeff_logConvex_of_hankelTotalPositive`;
- `XiHankelTPToMomentBridge`;
- `XiMomentToScaledFiniteBridge`;
- `xiHankelTPToScaledFiniteBridge_of_moment_bridges`;
- `XiHankelTPToScaledFiniteBridge`;
- `XiTotalPositivityApertureWitness`;
- `riemannHypothesis_of_xiTotalPositivityAperture`.

The first target is contiguous Hankel total positivity, not full arbitrary-minor
total positivity.  This is deliberate: it gives a concrete Stieltjes-moment
style foothold that can be strengthened later if the contiguous version is too
weak.

The raw unsigned target is retained in Lean as `XiRawHankelTotalPositive`, but
only as an obstruction marker: it is the wrong sign convention for the expected
real-rooted product.

The bridge is now split into two frontier theorems:

1. `XiHankelTPToMomentBridge`: signed Hankel positivity gives a genuine moment
   representation.  The current placeholder representation is intentionally
   weak and should be replaced by a positive Borel/Stieltjes measure when the
   measure-theory layer is built.
2. `XiMomentToScaledFiniteBridge`: the moment/kernel representation produces
   normalized finite real-rooted approximants.  This is the
   Edrei-Schoenberg/Laguerre-Polya step.

Lean proves that these two bridges imply the previous one-stage bridge via
`xiHankelTPToScaledFiniteBridge_of_moment_bridges`.

## CORRECTION (2026-06-06): Toeplitz, not Hankel — the right total-positivity machine

The Hankel route above is the wrong machine, and finding the *correct* one is the
new analytic content delivered here.

**The error.** The Hamburger/Stieltjes moment problem (positive-semidefinite
**Hankel** matrices `[μ_{i+j}]`) characterizes sequences `μ_n = ∫ x^n dν`. Their
generating function is a Cauchy/Stieltjes transform — a function *with poles*,
never an entire product. Hankel positivity forces **log-convexity**
`μ_n² ≤ μ_{n-1}μ_{n+1}`. But a genuine Laguerre–Pólya product
`C·∏(1 − t²/τ_k²)` has **log-concave** normalized coefficients (Newton/Turán).
The proven Csordas–Norfolk–Varga Turán inequalities for Ξ are
`b_n² ≥ b_{n-1}b_{n+1}` — the *opposite* curvature. So `XiHankelTotalPositive`
contradicts the known truth except in degenerate (log-affine) cases.

**The correction.** The total-positivity object for an *entire* LP function is the
**Toeplitz** matrix `[a_{i-j}]` — the **Pólya frequency (PF) sequence** condition,
characterized by the **Aissen–Edrei–Schoenberg–Whitney theorem** (1951):

> `(a_n)` (with `a_n = 0` for `n < 0`) is PF (all minors of `[a_{i-j}] ≥ 0`) iff
> `∑ a_n z^n = e^{γz} ∏_i(1+α_i z) / ∏_j(1−β_j z)`, `γ, α_i, β_j ≥ 0`.

With no poles this is exactly a Laguerre–Pólya function with nonpositive real
zeros. Writing `Ξ(t)=F(t²)`, RH ⟺ `F(−u)=∑ XiMomentCoeff_n u^n` is LP with
negative real zeros ⟺ **`XiMomentCoeff` is a Pólya frequency sequence**.

PF sequences are **log-concave**: the `2×2` Toeplitz minor is
`μ_{n+1}² − μ_n μ_{n+2} ≥ 0`, which is *exactly* the Turán determinant — the
correct curvature, matching CNV.

**Lean status (`Reinmann/XiToeplitzPositivity.lean`, verified, std axioms):**

- `XiToeplitzEntry`, `XiToeplitzTotalPositive` — full PF condition (all minors of
  the infinite Toeplitz matrix over arbitrary strictly-monotone index selections).
- `xiMomentCoeff_nonneg_of_toeplitzTP` — `1×1` minors ⟹ `μ_n ≥ 0`.
- `XiToeplitzMinor2`, `xiToeplitzMinor2_eq` — the `2×2` minor equals the unsigned
  log-concavity determinant `XiCoeff(n+1)² − XiCoeff n · XiCoeff(n+2)`.
- `xiToeplitzMinor2_nonneg_iff_turan2` — `2×2` minor `≥ 0` ⟺ `XiTuran2 n`.
- `xiTuran2All_of_toeplitzTP` — PF positivity ⟹ *all* Turán inequalities; the
  corrected route subsumes the proven CNV rung.
- `XiToeplitzTPToScaledFiniteBridge` — the Edrei–ASW payload (a universal theorem
  about sequences, **not** RH).
- `riemannHypothesis_of_xiToeplitzPositivity` — PF positivity + Edrei–ASW bridge
  + LP closure + Pólya–Jensen ⟹ RH.

**The honest frontier now.** The `2×2` Toeplitz minor (= Turán `d=2`) is a
*theorem* (CNV). The remaining new mathematics is exactly the order-`≥3` Toeplitz
minor positivity of `XiMomentCoeff` (equivalently the higher Laguerre
inequalities). The bridge `XiToeplitzTPToScaledFiniteBridge` is classical
(Edrei–ASW), so the entire RH-hard content is concentrated in proving the
higher-order PF minors — a single, sign-correct, falsifiable positivity target,
unlike the mis-signed Hankel demand.

## Why this is not yet a proof

The hard step is exactly one of the following:

1. prove total positivity of the xi kernel;
2. prove the Hermite aperture barrier uniformly in `d`;
3. prove heat-flow aperture monotonicity at `t = 0`.

Each one would be a major new theorem.  None follows from the functional
equation or ordinary conjugation symmetry alone.

## Immediate experiments

1. Numerically build normalized Jensen polynomials from high-precision xi
   coefficients and map the unknown aperture in `(d,n)`.
2. Compute Hankel minors of `XiMomentCoeff` for moderate sizes and look for a
   total-positivity pattern or first obstruction.
3. Compare aperture-boundary polynomials against Hermite perturbation theory:
   identify whether failures, if any, concentrate near multiple-root
   degeneracies.
4. Attempt a Lean finite theorem: if a finite coefficient segment is
   Pólya-frequency of order `d`, then the associated Jensen polynomial is
   hyperbolic.

## Verdict

The best new route is not "construct canonical products directly."  Direct
construction is equivalent to knowing the zeros are real.  The best route is:

```text
xi Fourier kernel positivity
    -> total positivity / aperture closure
    -> normalized finite real-rooted approximants
    -> Jensen hyperbolicity
    -> RH
```

This is genuinely new mathematics if the first arrow is proved.  It is also
falsifiable: finite Hankel minors and normalized Jensen apertures can be tested
immediately, while the Lean side already knows how to consume the final target.
