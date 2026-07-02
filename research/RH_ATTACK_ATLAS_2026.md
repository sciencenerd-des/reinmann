# RH Attack Atlas

**Date:** 2026-06-06
**Status:** proof-search map, not a proof of RH.

This atlas extends `RH_SOLUTION_STRUCTURES.md`.  The rule is strict: an attack is
useful only if it imports an independent mathematical handle, not merely another
RH-equivalent restatement of the zero set.

**Lean registry:** `Reinmann/RHAttackBridges.lean` now packages each route below
as a named witness contract and proves that any completed witness implies
`RiemannHypothesis`.  This is a verified reduction registry, not a completed
proof.

## Tier 1 — Most actionable

### A. Jensen / Laguerre-Polya uniform hyperbolicity

**External handle:** finite polynomial real-rootedness.

**Verified foothold:** `Xi`, `Xi_even`, `XiCoeff`, `JensenPoly`,
`AllJensenHyperbolic`, `PolyaJensenBridge`, and the `d = 2` Turan/discriminant
fragment in `Reinmann/JensenProgram.lean`.

**Open theorem needed:** upgrade eventual hyperbolicity of Jensen polynomials to
all `d,n`.

**Next concrete move:** formalize normalized Jensen polynomials and connect
quadratic hyperbolicity directly to the discriminant of `JensenPoly 2 n`.

### B. Speiser / zeta-prime zero-free route

**External handle:** zeros of the derivative, Gauss-Lucas style geometry, and
logarithmic-derivative electrostatics.

**Verified foothold:** `deriv_riemannZeta_conj`, `deriv_riemannZeta_zero_conj`,
`SpeiserLeftHalfZeroFree`, and now `SpeiserBridge` in
`Reinmann/ZetaPrimeSymmetry.lean`.

**Open theorem needed:** prove `SpeiserLeftHalfZeroFree` directly, likely by
showing a left-half `ζ′` zero would force a forbidden local zero geometry of `ζ`.

**Verified finite model:** `Reinmann/FiniteGaussLucas.lean` proves the finite
log-derivative identity
`P_Z'(s) / P_Z(s) = Σ_{ρ ∈ Z} (s - ρ)⁻¹` away from the cloud.  It also proves the
robust same-height geometry theorem: any finite cloud built from mirror pairs
`1/2 ± a + iγ` has a derivative zero at the shared center `1/2 + iγ`.

**Remaining analytic jump:** prove derivative convergence for the canonical
completed-zeta Hadamard product approximants.  The abstract transfer theorem
`deriv_eq_zero_of_deriv_tendsto_finiteCritical` is already formalized: if the
finite-product derivative zeros converge to the derivative of the limiting
function, then the limiting derivative vanishes.

**Zeta-specific transfer contract:** `Reinmann/HadamardZetaTransfer.lean`
packages the missing analytic theorem as
`CompletedZetaHadamardApproximationAt` and
`FiniteCriticalHadamardSpeiserWitness`.  From such a witness, Lean proves
`deriv completedRiemannZeta₀ (1/2 + iγ) = 0`.  What remains unproved is the
classical infinite-product analysis showing that the chosen finite zero-product
approximants are canonical and derivative-convergent to `completedRiemannZeta₀`,
plus the finite cancellation theorem showing those global truncations have a
derivative zero at the chosen center.  The local same-height mirror theorem alone
does not prove that cancellation, because canonical truncations include zeros at
other heights.

**Obstruction found:** `otherHeight_mirrorPair_field_at_center_eq_I` proves a
single mirror pair at height `1` contributes the nonzero field `I` at the center
`1/2`.  Therefore the global finite cancellation theorem is not a formal
consequence of mirror symmetry alone; it would require a genuinely new
cross-height cancellation mechanism.

**New finite cancellation law:** `symmetricOtherHeight_mirrorPair_fields_cancel`
proves the correct algebraic replacement: paired layers at heights `γ + δ` and
`γ - δ` with the same horizontal offset cancel at the center `1/2 + iγ`.  The
Hadamard/Speiser path therefore needs a symmetric principal-value ordering of
canonical truncations around the target height.  This is now named as
`PrincipalValueCrossHeightCancellationTarget`.

**Product-level finite theorem:** `deriv_principalValueBlockProduct_center_eq_zero`
proves that any finite product of such symmetric principal-value blocks has a
derivative zero at `1/2 + iγ`.  The strongest concrete open target is now
`PrincipalValueBlockHadamardTarget`: show canonical completed-zeta truncations
can be arranged as these balanced blocks while preserving derivative convergence.

**Target obstruction:** `conjugatePair_not_heightBalancedAround_one` proves that
even the simple conjugate cloud `{i, -i}` is not height-balanced around target
height `1`.  Canonical zeta truncations have natural conjugate symmetry around
height `0`, not around an arbitrary `γ`.  Therefore
`PrincipalValueBlockHadamardTarget` is likely too strong as a global all-height
claim; it would need a new zeta-specific rebalancing theorem, not just canonical
Hadamard convergence.

**Pivot to the Ξ-plane:** `Reinmann/XiPlanePrincipalValue.lean` moves the
principal-value idea to the real critical-line coordinate `t`, where the
functional equation gives the natural symmetry `t ↦ -t`.  It proves that every
finite even product over paired roots `±τ` has derivative zero at `t = 0`, and
packages the cleaner target `XiEvenHadamardTarget`: construct canonical
Ξ-Hadamard approximants as even finite products with derivative convergence.
This avoids the arbitrary-height rebalancing obstruction in the `s`-plane.

### C. de Bruijn-Newman heat-flow rigidity

**External handle:** PDE / heat-flow dynamics of the xi function.

**Verified foothold:** fiber energy, centroid identity, and energy-gap detection
of off-line zeros.

**Open theorem needed:** a Lyapunov functional proving the Newman constant is
`≤ 0`; Rodgers-Tao already gives `≥ 0`, so this would force equality.

**Next concrete move:** define an abstract `HeatFlowXiWitness` with an
energy-dissipation axiom as a named hypothesis, then prove it implies RH through
the existing fiber-energy criterion.  The final deduction is now captured by
`HeatFlowEnergyRigidityWitness`.

## Tier 2 — Strong but heavier

### D. Weil explicit formula positivity

**External handle:** positivity of a distribution on test functions.

**Known bridge:** Weil's positivity criterion is RH-equivalent.

**Repo foothold:** no complete explicit-formula module yet; fiber energy gives a
target quantity that an explicit-formula test family could try to detect.

**Open theorem needed:** construct a test function family whose Weil positivity
collapses exactly to nonnegative fiber-energy deficits.

**Lean contract:** `WeilExplicitFormulaWitness`.

### E. de Branges / Hermite-Biehler spaces

**External handle:** Hilbert spaces of entire functions and Hermite-Biehler
interlacing.

**Repo foothold:** `Ξ` real/even and derivative symmetries of `Λ₀`.

**Open theorem needed:** construct an entire function `E = A - iB` whose
Hermite-Biehler property is independently provable and whose real/imaginary
parts encode `Ξ`.

**Lean contract:** `DeBrangesHermiteBiehlerWitness`.

### F. Pseudo-Hermitian / PT-symmetric operator route

**External handle:** operator metric positivity.

**Repo foothold:** Hilbert-Polya witness packaging, `zetaInvolution`, and
critical-line fixed-point theorems.

**Open theorem needed:** construct a positive metric `η` and an `η`-self-adjoint
operator whose spectrum faithfully encodes zeta zeros.

**Lean contract:** `OperatorMetricPositivityWitness`.

## Tier 3 — Experimental or model-building

### G. Horizontal argument principle

**External handle:** winding of `x ↦ ζ(x+iγ)` and `ζ'/ζ` phase.

**Repo foothold:** `componentwiseRolleForZetaZeros_proved` discharges generic
calculus.  The remaining target is exactly
`NoComponentwiseCriticalPairBetweenZetaZeros`.

**Risk:** arbitrary complex curves do not satisfy the needed exclusion.  The
missing theorem must use zeta-specific phase information.

### H. Hadamard-product finite truncation limits

**External handle:** uniform convergence of finite zero-product approximants.

**Repo foothold:** zero-fiber and symmetry modules identify the exact collision
shape.

**Open theorem needed:** a stable finite-product theorem saying same-height
off-line pairs force derivative/electrostatic defects persisting in the limit.

**Updated obstruction:** the s-plane version cannot be obtained from ordinary
conjugation symmetry.  A mirror pair at another height contributes a nonzero
field at a target center, and conjugate heights are balanced around `0`, not
around arbitrary `γ`.

**Ξ-plane pivot:** `Reinmann/XiPlanePrincipalValue.lean` moves the finite
principal-value mechanism to the real critical-line coordinate `t`, where the
functional equation gives the natural pairing `t ↦ -t`.  Lean now verifies:

- each paired factor `(t - τ)(t + τ)` is even;
- finite products over paired roots are even;
- the paired principal-value field
  `(t - τ)⁻¹ + (t + τ)⁻¹` cancels at `t = 0`;
- finite sums of those paired fields also cancel at `t = 0`.

This is the correct replacement for height-balancing, but it is not yet RH.
The useful target is now the normalized
`XiLaguerrePolyaScaledFiniteTarget`: construct canonical finite real-rooted
even products, with scalar Hadamard normalizations, converging to `Ξ`.  The
unscaled target was too rigid because canonical Ξ-products require a leading
normalization factor.  This target feeds back into the Jensen/Laguerre--Pólya
spine, whereas the weaker derivative-at-origin target only recovers an expected
consequence of evenness.

**Verified implication chain:** Lean now records the exact final deduction:
`XiLaguerrePolyaScaledFiniteTarget`, plus the closure theorem
`XiLaguerrePolyaClosureBridge`, plus `PolyaJensenBridge`, implies
`RiemannHypothesis`.  The unified route registry also contains
`XiFiniteRealRootedApproximationWitness`, so this route is auditable alongside
the Jensen, Speiser, heat-flow, Weil/de Branges, and operator routes.

**Current hard gap:** prove the actual existence theorem for canonical scaled
finite real-rooted Ξ-products, and prove the closure bridge from that convergence
to Jensen hyperbolicity.  This is the RH-level Laguerre--Pólya content and is
not discharged by the finite algebra alone.

**New theory note:** `research/XI_LAGUERRE_POLYA_EXISTENCE_PROGRAM.md` proposes
an Aperture Closure Program: combine high-shift Hermite asymptotics, low-degree
Turan/Laguerre inequalities, heat-flow monotonicity, and total positivity of the
xi Fourier kernel to force `XiLaguerrePolyaScaledFiniteTarget` without directly
assuming real zeros.

**New Lean contract:** `Reinmann/XiTotalPositivity.lean` now defines the signed
moment sequence `XiMomentCoeff n = (-1)^n * XiCoeff n`, contiguous Hankel
determinants of that sequence, and packages the aperture route as
`XiTotalPositivityApertureWitness`.  Lean proves
`riemannHypothesis_of_xiTotalPositivityAperture`: if Hankel positivity, the
total-positivity-to-scaled-products bridge, the Laguerre--Pólya closure bridge,
and the Pólya--Jensen bridge are supplied, RH follows.

The raw unsigned Hankel target is retained only as `XiRawHankelTotalPositive`,
because raw `XiCoeff` is expected to alternate signs under a real-rooted even
product.

### I. Prime-side explicit formula contradiction

**External handle:** arithmetic discreteness of primes.

**Idea:** same-height off-line pairs produce oscillatory terms with identical
frequency but different damping.  Try to build a prime-counting test where this
frequency degeneracy violates a sign or variance bound.

**Risk:** known explicit-formula error terms are probably too weak without a new
test-family construction.

## Exhaustive conclusion

The best current ordering is:

1. Jensen uniform hyperbolicity.
2. Ξ-plane finite real-rooted approximation / Laguerre--Pólya closure.
3. Speiser/zeta-prime electrostatics.
4. de Bruijn-Newman energy rigidity.
5. Weil/de Branges positivity.
6. Operator metric positivity.
7. Horizontal argument principle as a local model.

The repo has already made real Lean progress on (1), (2), and (7).  The next
highest-value verified step is to strengthen the Ξ-plane target from finite
principal-value cancellation to normalized finite real-rooted convergence.  The
Speiser route remains valuable as a model, but its s-plane Hadamard truncation
route now has a verified height-balance obstruction.
