/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Order.Filter.Basic

/-!
# Finite Gauss--Lucas / Log-Derivative Surrogate

This module is the finite model for the Speiser/electrostatic attack.

For a finite zero cloud `Z`, the monic product

`P_Z(s) = ∏ ρ ∈ Z, (s - ρ)`

has logarithmic derivative

`P_Z'(s) / P_Z(s) = ∑ ρ ∈ Z, 1 / (s - ρ)`

away from the cloud.  Thus zeros of `P_Z'` off the cloud are exactly equilibrium
points of the finite Coulomb field.  This is the finite object we want before
taking a Hadamard-product limit for zeta.

We also prove the smallest same-height critical geometry: two zeros mirrored
across the critical line force the midpoint `1/2 + iγ` to be a critical point of
their quadratic product.
-/

noncomputable section

open Complex
open Filter Topology
open scoped BigOperators

namespace Reinmann

/-! ## Finite zero-cloud product and field -/

/-- The monic finite product attached to a zero cloud. -/
def finiteZeroProduct (Z : Finset ℂ) (s : ℂ) : ℂ :=
  ∏ ρ ∈ Z, (s - ρ)

/-- The finite electrostatic/log-derivative field of a zero cloud. -/
def finiteZeroField (Z : Finset ℂ) (s : ℂ) : ℂ :=
  ∑ ρ ∈ Z, (s - ρ)⁻¹

/-- Away from the zero cloud, no finite-product factor vanishes. -/
theorem finiteZeroProduct_factor_ne_zero {Z : Finset ℂ} {s ρ : ℂ}
    (hρ : ρ ∈ Z) (hs : s ∉ Z) : s - ρ ≠ 0 := by
  intro h
  apply hs
  have hs_eq : s = ρ := sub_eq_zero.mp h
  simpa [hs_eq] using hρ

/-- The logarithmic derivative of a finite zero product is the finite
electrostatic field. -/
theorem logDeriv_finiteZeroProduct {Z : Finset ℂ} {s : ℂ} (hs : s ∉ Z) :
    logDeriv (finiteZeroProduct Z) s = finiteZeroField Z s := by
  unfold finiteZeroProduct finiteZeroField
  rw [logDeriv_prod]
  · refine Finset.sum_congr rfl ?_
    intro ρ hρ
    simp [logDeriv_apply]
  · intro ρ hρ
    exact finiteZeroProduct_factor_ne_zero hρ hs
  · intro ρ hρ
    fun_prop

/-- If the finite product is nonzero, its log-derivative is `P'/P`. -/
theorem logDeriv_finiteZeroProduct_eq_deriv_div {Z : Finset ℂ} {s : ℂ} :
    logDeriv (finiteZeroProduct Z) s =
      deriv (finiteZeroProduct Z) s / finiteZeroProduct Z s :=
  rfl

/-- At any nonzero point of the product, a derivative zero is an electrostatic
equilibrium: the finite field vanishes. -/
theorem finiteZeroField_eq_zero_of_deriv_eq_zero {Z : Finset ℂ} {s : ℂ}
    (hs : s ∉ Z) (hderiv : deriv (finiteZeroProduct Z) s = 0) :
    finiteZeroField Z s = 0 := by
  have hprod_ne : finiteZeroProduct Z s ≠ 0 := by
    unfold finiteZeroProduct
    rw [Finset.prod_ne_zero_iff]
    intro ρ hρ
    exact finiteZeroProduct_factor_ne_zero hρ hs
  have hlog := logDeriv_finiteZeroProduct (Z := Z) hs
  rw [logDeriv_finiteZeroProduct_eq_deriv_div, hderiv, zero_div] at hlog
  exact hlog.symm

/-! ## Same-height mirrored pair -/

/-- The point mirrored across the critical line at the same height. -/
def criticalMirror (s : ℂ) : ℂ :=
  (1 : ℂ) - s.re + I * s.im

/-- A point and its critical-line mirror have midpoint `1/2 + i Im(s)`. -/
theorem midpoint_self_criticalMirror (s : ℂ) :
    (s + criticalMirror s) / 2 = (1 / 2 : ℂ) + I * s.im := by
  apply Complex.ext
  · simp [criticalMirror, div_eq_mul_inv]
  · simp [criticalMirror, div_eq_mul_inv]
    ring

/-- The quadratic product attached to a same-height critical-line mirror pair. -/
def mirrorPairProduct (s z : ℂ) : ℂ :=
  (z - s) * (z - criticalMirror s)

/-- The finite field of a mirrored pair vanishes at the midpoint. -/
theorem mirrorPair_field_midpoint_eq_zero (s : ℂ) :
    ((s + criticalMirror s) / 2 - s)⁻¹ +
      ((s + criticalMirror s) / 2 - criticalMirror s)⁻¹ = 0 := by
  have hneg :
      (s + criticalMirror s) / 2 - criticalMirror s =
        -((s + criticalMirror s) / 2 - s) := by
    ring
  rw [hneg, inv_neg]
  abel

/-- A same-height mirror pair forces a critical point at its midpoint for the
quadratic product.  This is the finite Gauss--Lucas/Speiser toy geometry:
off-line mirrored zeros create a derivative zero on the critical line. -/
theorem deriv_mirrorPairProduct_midpoint_eq_zero (s : ℂ) :
    deriv (mirrorPairProduct s) ((s + criticalMirror s) / 2) = 0 := by
  have hderiv :
      HasDerivAt (mirrorPairProduct s)
        (((s + criticalMirror s) / 2 - criticalMirror s) +
          ((s + criticalMirror s) / 2 - s))
        ((s + criticalMirror s) / 2) := by
    unfold mirrorPairProduct
    simpa [one_mul, mul_one, add_comm] using
      (((hasDerivAt_id ((s + criticalMirror s) / 2)).sub_const s).mul
        ((hasDerivAt_id ((s + criticalMirror s) / 2)).sub_const (criticalMirror s)))
  rw [hderiv.deriv]
  ring

/-! ## Robust same-height mirror clouds -/

/-- The center of the horizontal line at height `γ` on the critical line. -/
def criticalLinePoint (γ : ℝ) : ℂ :=
  (1 / 2 : ℂ) + I * γ

/-- A point at height `γ` with horizontal offset `a` from the critical line. -/
def offLinePoint (γ a : ℝ) : ℂ :=
  ((1 / 2 + a : ℝ) : ℂ) + I * γ

/-- The midpoint of an off-line point and its critical-line mirror is the
critical-line point at the same height. -/
theorem midpoint_offLinePoint_criticalMirror (γ a : ℝ) :
    (offLinePoint γ a + criticalMirror (offLinePoint γ a)) / 2 =
      criticalLinePoint γ := by
  rw [midpoint_self_criticalMirror]
  apply Complex.ext
  · simp [criticalLinePoint]
  · simp [criticalLinePoint, offLinePoint]

/-- The product attached to an arbitrary finite same-height mirror-paired cloud.
Each offset `a` contributes the pair
`1/2 + a + iγ` and `1/2 - a + iγ`. -/
def mirrorPairedCloudProduct (A : Finset ℝ) (γ : ℝ) (z : ℂ) : ℂ :=
  ∏ a ∈ A, mirrorPairProduct (offLinePoint γ a) z

/-- Robust finite geometry theorem: any finite same-height cloud built from
mirror pairs has a derivative zero at the shared critical-line center. -/
theorem deriv_mirrorPairedCloudProduct_center_eq_zero (A : Finset ℝ) (γ : ℝ) :
    deriv (mirrorPairedCloudProduct A γ) (criticalLinePoint γ) = 0 := by
  unfold mirrorPairedCloudProduct
  rw [deriv_fun_finsetProd]
  · apply Finset.sum_eq_zero
    intro a ha
    have hfactor :
        deriv (mirrorPairProduct (offLinePoint γ a)) (criticalLinePoint γ) = 0 := by
      rw [← midpoint_offLinePoint_criticalMirror γ a]
      exact deriv_mirrorPairProduct_midpoint_eq_zero (offLinePoint γ a)
    simp [hfactor]
  · intro a ha
    unfold mirrorPairProduct
    fun_prop

/-- Other-height mirror pairs do not cancel at a chosen center in general.

This concrete computation blocks the naive claim that global completed-zeta
Hadamard truncations automatically inherit the same-height cancellation theorem:
at the center `1/2`, the mirror pair at height `1` and offset `1` contributes
the nonzero field `I`. -/
theorem otherHeight_mirrorPair_field_at_center_ne_zero :
    ((criticalLinePoint 0 - offLinePoint 1 1)⁻¹ +
      (criticalLinePoint 0 - criticalMirror (offLinePoint 1 1))⁻¹) ≠ 0 := by
  norm_num [criticalLinePoint, offLinePoint, criticalMirror, Complex.ext_iff, Complex.normSq]

/-- The same obstruction with its exact value. -/
theorem otherHeight_mirrorPair_field_at_center_eq_I :
    ((criticalLinePoint 0 - offLinePoint 1 1)⁻¹ +
      (criticalLinePoint 0 - criticalMirror (offLinePoint 1 1))⁻¹) = I := by
  norm_num [criticalLinePoint, offLinePoint, criticalMirror, Complex.ext_iff, Complex.normSq]

/-- Symmetric other-height mirror layers cancel at the chosen center.

This is the finite algebraic shape that a valid principal-value Hadamard
truncation would need: a layer at height `γ + δ` and the corresponding layer at
height `γ - δ`, with the same horizontal offset, have total field zero at
`1/2 + iγ`. -/
theorem symmetricOtherHeight_mirrorPair_fields_cancel (γ δ a : ℝ) :
    ((criticalLinePoint γ - offLinePoint (γ + δ) a)⁻¹ +
      (criticalLinePoint γ - criticalMirror (offLinePoint (γ + δ) a))⁻¹) +
    ((criticalLinePoint γ - offLinePoint (γ - δ) a)⁻¹ +
      (criticalLinePoint γ - criticalMirror (offLinePoint (γ - δ) a))⁻¹) = 0 := by
  apply Complex.ext
  · simp [criticalLinePoint, offLinePoint, criticalMirror, Complex.normSq]
    ring_nf
  · simp [criticalLinePoint, offLinePoint, criticalMirror, Complex.normSq]
    ring_nf

/-- The four-zero principal-value block attached to heights `γ ± δ` and
horizontal offset `a`. -/
def principalValueMirrorBlock (γ δ a : ℝ) (z : ℂ) : ℂ :=
  mirrorPairProduct (offLinePoint (γ + δ) a) z *
    mirrorPairProduct (offLinePoint (γ - δ) a) z

/-- A symmetric principal-value four-zero block has a derivative zero at the
target center.  This is the product-level version of
`symmetricOtherHeight_mirrorPair_fields_cancel`. -/
theorem deriv_principalValueMirrorBlock_center_eq_zero (γ δ a : ℝ) :
    deriv (principalValueMirrorBlock γ δ a) (criticalLinePoint γ) = 0 := by
  have hderiv : HasDerivAt (principalValueMirrorBlock γ δ a)
      (((criticalLinePoint γ - criticalMirror (offLinePoint (γ + δ) a)) +
          (criticalLinePoint γ - offLinePoint (γ + δ) a)) *
        mirrorPairProduct (offLinePoint (γ - δ) a) (criticalLinePoint γ) +
        mirrorPairProduct (offLinePoint (γ + δ) a) (criticalLinePoint γ) *
          ((criticalLinePoint γ - criticalMirror (offLinePoint (γ - δ) a)) +
            (criticalLinePoint γ - offLinePoint (γ - δ) a)))
      (criticalLinePoint γ) := by
    unfold principalValueMirrorBlock
    apply HasDerivAt.mul
    · unfold mirrorPairProduct
      simpa [one_mul, mul_one, add_comm] using
        (((hasDerivAt_id (criticalLinePoint γ)).sub_const (offLinePoint (γ + δ) a)).mul
          ((hasDerivAt_id (criticalLinePoint γ)).sub_const
            (criticalMirror (offLinePoint (γ + δ) a))))
    · unfold mirrorPairProduct
      simpa [one_mul, mul_one, add_comm] using
        (((hasDerivAt_id (criticalLinePoint γ)).sub_const (offLinePoint (γ - δ) a)).mul
          ((hasDerivAt_id (criticalLinePoint γ)).sub_const
            (criticalMirror (offLinePoint (γ - δ) a))))
  rw [hderiv.deriv]
  apply Complex.ext
  · simp [criticalLinePoint, offLinePoint, criticalMirror, mirrorPairProduct, Complex.normSq]
    ring_nf
  · simp [criticalLinePoint, offLinePoint, criticalMirror, mirrorPairProduct, Complex.normSq]
    ring_nf

/-- A finite product of principal-value mirror blocks.  The index carries both
the height offset `δ` and horizontal offset `a`. -/
def principalValueBlockProduct (B : Finset (ℝ × ℝ)) (γ : ℝ) (z : ℂ) : ℂ :=
  ∏ b ∈ B, principalValueMirrorBlock γ b.1 b.2 z

/-- Any finite product of symmetric principal-value blocks has a derivative zero
at the target critical-line center. -/
theorem deriv_principalValueBlockProduct_center_eq_zero
    (B : Finset (ℝ × ℝ)) (γ : ℝ) :
    deriv (principalValueBlockProduct B γ) (criticalLinePoint γ) = 0 := by
  unfold principalValueBlockProduct
  rw [deriv_fun_finsetProd]
  · apply Finset.sum_eq_zero
    intro b hb
    have hfactor :
        deriv (principalValueMirrorBlock γ b.1 b.2) (criticalLinePoint γ) = 0 :=
      deriv_principalValueMirrorBlock_center_eq_zero γ b.1 b.2
    simp [hfactor]
  · intro b hb
    unfold principalValueMirrorBlock mirrorPairProduct
    fun_prop

/-! ## Height-balance obstruction -/

/-- A finite cloud is height-balanced around `γ` if every point has a partner
whose imaginary coordinate is reflected across the horizontal line at height
`γ`.  Principal-value block products have this shape by construction. -/
def HeightBalancedAround (γ : ℝ) (Z : Finset ℂ) : Prop :=
  ∀ z ∈ Z, ∃ w ∈ Z, w.im = 2 * γ - z.im

/-- The two conjugate heights `±1` are not a principal-value height pair around
target height `1`.  This is the finite obstruction to arranging ordinary
conjugate-symmetric truncations as principal-value blocks around an arbitrary
target height. -/
theorem conjugateHeights_not_principalValuePair_around_one :
    ¬ ∃ δ : ℝ, ((I : ℂ).im = (1 : ℝ) + δ ∧ ((-I : ℂ).im = (1 : ℝ) - δ)) := by
  rintro ⟨δ, hpos, hneg⟩
  norm_num at hpos hneg
  linarith

/-- The concrete two-point conjugate cloud `{i, -i}` is not height-balanced
around target height `1`. -/
theorem conjugatePair_not_heightBalancedAround_one :
    ¬ HeightBalancedAround 1 ({I, -I} : Finset ℂ) := by
  intro hbal
  have hnegI : (-I : ℂ) ∈ ({I, -I} : Finset ℂ) := by simp
  rcases hbal (-I) hnegI with ⟨w, hw, hwim⟩
  have htarget : w.im = 3 := by
    norm_num at hwim ⊢
    exact hwim
  have hw_cases : w = I ∨ w = -I := by
    simpa using hw
  rcases hw_cases with rfl | rfl
  · norm_num at htarget
  · norm_num at htarget

/-! ## Abstract Hadamard-limit transfer -/

/-- Abstract derivative-limit transfer: if finite products have derivative zero
at a point and their derivatives converge there to the derivative of a limiting
function, then the limiting function has derivative zero at that point.

This is the exact analytic bridge needed for the zeta/Hadamard stage.  The hard
external work is proving the derivative convergence for the canonical completed
zeta product approximants. -/
theorem deriv_eq_zero_of_deriv_tendsto_finiteCritical
    {F : ℂ → ℂ} {P : ℕ → ℂ → ℂ} {c : ℂ}
    (hlim : Tendsto (fun n : ℕ => deriv (P n) c) atTop (𝓝 (deriv F c)))
    (hcrit : ∀ n : ℕ, deriv (P n) c = 0) :
    deriv F c = 0 := by
  have hzero : Tendsto (fun n : ℕ => deriv (P n) c) atTop (𝓝 (0 : ℂ)) := by
    simp [hcrit]
  exact tendsto_nhds_unique hlim hzero

/-- A named Hadamard-product transfer witness for the Speiser route.  Supplying
`derivConverges` for zeta's canonical finite zero products is the infinite
product theorem still missing from the program. -/
structure HadamardDerivativeTransferWitness where
  limitFunction : ℂ → ℂ
  approximants : ℕ → ℂ → ℂ
  center : ℂ
  derivConverges :
    Tendsto (fun n : ℕ => deriv (approximants n) center) atTop
      (𝓝 (deriv limitFunction center))
  finiteCritical : ∀ n : ℕ, deriv (approximants n) center = 0

/-- Any Hadamard derivative-transfer witness carries finite critical geometry to
the limiting function. -/
theorem deriv_limitFunction_eq_zero_of_hadamardDerivativeTransfer
    (w : HadamardDerivativeTransferWitness) :
    deriv w.limitFunction w.center = 0 :=
  deriv_eq_zero_of_deriv_tendsto_finiteCritical w.derivConverges w.finiteCritical

end Reinmann
