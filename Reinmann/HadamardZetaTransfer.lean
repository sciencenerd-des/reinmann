/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.FiniteGaussLucas
import Reinmann.CompletedZetaConj

/-!
# Completed-Zeta Hadamard Transfer Contract

This file isolates the exact infinite-product theorem needed after the finite
Gauss--Lucas model.

The robust finite geometry is already proved in `FiniteGaussLucas`: every finite
same-height mirror-paired cloud has a derivative zero at the shared critical-line
center.  To transfer any such finite critical geometry to the completed zeta
function, one needs a genuine Hadamard-product theorem for canonical finite
zero-product approximants:

`deriv Pₙ(c) → deriv completedRiemannZeta₀(c)`.

That theorem is not available in the current repo/mathlib stack.  We therefore
package it as a named, auditable witness and prove the final transfer from the
analytic input plus finite critical geometry to the zeta-side derivative zero.

Important correction: canonical completed-zeta Hadamard truncations are global
zero-products, not generally same-height mirror-pair products.  The finite
same-height theorem is a local model.  A valid zeta transfer must separately
prove that the chosen canonical truncations have derivative zero at the center,
or prove an equivalent cancellation statement for all other zero layers.
-/

noncomputable section

open Complex
open Filter Topology

namespace Reinmann

/-- A canonical completed-zeta Hadamard approximation at one center.

`approximants` are the finite zero-product approximants.  The field `canonical`
records the external fact that these are the actual canonical completed-zeta
Hadamard truncations, rather than arbitrary functions.  The mathematically hard
field is `derivConverges`: derivative convergence at the center to
`completedRiemannZeta₀`. -/
structure CompletedZetaHadamardApproximationAt where
  approximants : ℕ → ℂ → ℂ
  center : ℂ
  canonical : Prop
  hcanonical : canonical
  derivConverges :
    Tendsto (fun n : ℕ => deriv (approximants n) center) atTop
      (𝓝 (deriv completedRiemannZeta₀ center))

/-- If canonical completed-zeta Hadamard approximants have finite critical
geometry at a center, derivative convergence transfers that critical point to
`completedRiemannZeta₀`. -/
theorem deriv_completedZeta₀_eq_zero_of_hadamardApproximationAt
    (w : CompletedZetaHadamardApproximationAt)
    (hfiniteCritical : ∀ n : ℕ, deriv (w.approximants n) w.center = 0) :
    deriv completedRiemannZeta₀ w.center = 0 :=
  deriv_eq_zero_of_deriv_tendsto_finiteCritical w.derivConverges hfiniteCritical

/-- The same transfer specialized to the critical-line center at height `γ`. -/
theorem deriv_completedZeta₀_criticalLinePoint_eq_zero_of_hadamardApproximationAt
    {γ : ℝ} (w : CompletedZetaHadamardApproximationAt)
    (hcenter : w.center = criticalLinePoint γ)
    (hfiniteCritical : ∀ n : ℕ, deriv (w.approximants n) w.center = 0) :
    deriv completedRiemannZeta₀ (criticalLinePoint γ) = 0 := by
  rw [← hcenter]
  exact deriv_completedZeta₀_eq_zero_of_hadamardApproximationAt w hfiniteCritical

/-- A finite-critical Hadamard/Speiser witness at height `γ`.

This packages the exact desired pipeline:

1. the approximants are canonical completed-zeta Hadamard truncations;
2. a separate finite-geometry theorem proves each approximant has a derivative
   zero at `1/2 + iγ`;
3. the canonical Hadamard derivative convergence transfers those zeros to
   `completedRiemannZeta₀`.

The nontrivial payloads are `hadamard.derivConverges` and `finiteCritical`.
The earlier same-height mirror-pair theorem can supply `finiteCritical` only for
approximants that really factor into same-height mirror-pair layers at this
center. -/
structure FiniteCriticalHadamardSpeiserWitness (γ : ℝ) where
  offsets : ℕ → Finset ℝ
  hadamard : CompletedZetaHadamardApproximationAt
  center_eq : hadamard.center = criticalLinePoint γ
  finiteCritical : ∀ n : ℕ, deriv (hadamard.approximants n) hadamard.center = 0

/-- A same-height Hadamard/Speiser witness forces a completed-zeta derivative
zero at the corresponding critical-line point. -/
theorem deriv_completedZeta₀_eq_zero_of_finiteCriticalHadamardSpeiserWitness
    {γ : ℝ} (w : FiniteCriticalHadamardSpeiserWitness γ) :
    deriv completedRiemannZeta₀ (criticalLinePoint γ) = 0 := by
  apply deriv_completedZeta₀_criticalLinePoint_eq_zero_of_hadamardApproximationAt
    (w := w.hadamard) w.center_eq
  exact w.finiteCritical

/-- The exact open analytic target: produce canonical completed-zeta Hadamard
approximants at height `γ` whose finite truncations have a derivative zero at
`1/2 + iγ` and whose derivatives converge to `completedRiemannZeta₀`.

This is a named target, not a theorem claimed here. -/
def CompletedZetaHadamardDerivativeConvergenceTarget (γ : ℝ) : Prop :=
  Nonempty (FiniteCriticalHadamardSpeiserWitness γ)

/-! ## Principal-value cross-height cancellation target -/

/-- A local same-height mirror cloud can explain one finite critical point.  A
canonical completed-zeta Hadamard truncation also contains zeros at other
heights.  This target names the additional cancellation theorem needed before
the local finite model can be applied to canonical global truncations. -/
def OtherHeightCancellationTarget : Prop :=
  ∀ γ : ℝ, CompletedZetaHadamardDerivativeConvergenceTarget γ

/-- A sharper version of the other-height target: canonical truncations must be
organized as symmetric principal values around the target height.  The finite
algebraic reason this is plausible is
`symmetricOtherHeight_mirrorPair_fields_cancel`; the hard zeta-specific part is
showing that canonical Hadamard truncations can be put in such a balanced
ordering and that the limiting derivative is preserved. -/
structure PrincipalValueCrossHeightCancellationWitness (γ : ℝ) where
  hadamard : CompletedZetaHadamardApproximationAt
  center_eq : hadamard.center = criticalLinePoint γ
  balancedFiniteCritical :
    ∀ n : ℕ, deriv (hadamard.approximants n) hadamard.center = 0

/-- Principal-value cross-height cancellation plus Hadamard derivative
convergence gives the completed-zeta derivative zero at the target height. -/
theorem deriv_completedZeta₀_eq_zero_of_principalValueCrossHeightCancellation
    {γ : ℝ} (w : PrincipalValueCrossHeightCancellationWitness γ) :
    deriv completedRiemannZeta₀ (criticalLinePoint γ) = 0 := by
  apply deriv_completedZeta₀_criticalLinePoint_eq_zero_of_hadamardApproximationAt
    (w := w.hadamard) w.center_eq
  exact w.balancedFiniteCritical

/-- The refined open target for the Hadamard/Speiser path. -/
def PrincipalValueCrossHeightCancellationTarget : Prop :=
  ∀ γ : ℝ, Nonempty (PrincipalValueCrossHeightCancellationWitness γ)

/-- A stronger constructive witness: every finite approximant is explicitly a
product of principal-value mirror blocks. -/
structure PrincipalValueBlockHadamardWitness (γ : ℝ) where
  blocks : ℕ → Finset (ℝ × ℝ)
  hadamard : CompletedZetaHadamardApproximationAt
  center_eq : hadamard.center = criticalLinePoint γ
  approximants_eq :
    ∀ n : ℕ, hadamard.approximants n = principalValueBlockProduct (blocks n) γ

/-- If canonical Hadamard approximants can be represented as finite products of
principal-value blocks, derivative convergence transfers the finite critical
points to `completedRiemannZeta₀`. -/
theorem deriv_completedZeta₀_eq_zero_of_principalValueBlockHadamardWitness
    {γ : ℝ} (w : PrincipalValueBlockHadamardWitness γ) :
    deriv completedRiemannZeta₀ (criticalLinePoint γ) = 0 := by
  apply deriv_completedZeta₀_criticalLinePoint_eq_zero_of_hadamardApproximationAt
    (w := w.hadamard) w.center_eq
  intro n
  have hcrit := deriv_principalValueBlockProduct_center_eq_zero (w.blocks n) γ
  rw [w.approximants_eq n, w.center_eq]
  exact hcrit

/-- The most concrete open target produced by the finite algebraic analysis. -/
def PrincipalValueBlockHadamardTarget : Prop :=
  ∀ γ : ℝ, Nonempty (PrincipalValueBlockHadamardWitness γ)

end Reinmann
