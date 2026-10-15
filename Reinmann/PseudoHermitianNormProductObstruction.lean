/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.PseudoHermitianPacketNorm
import Reinmann.PseudoHermitianIsotropy

/-!
# The norm-product sufficient criterion is not necessary

A real length-two Jordan block is symmetric for the nondegenerate swap form.
Unit-mass packets have arbitrarily small ordinary residual and zero paired
residual, but their state/residual norm product is at least 1/2. Thus the
norm-product criterion must not replace the weaker paired-defect objective.
-/

noncomputable section
open Complex
open scoped ComplexConjugate

namespace Reinmann.NormProductObstruction
open PseudoHermitianIsotropy

def jordanAction : E →ₗ[ℂ] E where
  toFun x := (x.2, 0)
  map_add' := by intro x y; ext <;> simp
  map_smul' := by intro a x; ext <;> simp [smul_eq_mul]

theorem jordan_form_symmetric (x y : E) :
    swapForm.η (jordanAction x) y = swapForm.η x (jordanAction y) := by
  simp [swapForm, jordanAction]

theorem jordan_paired_residual_zero (x : E) :
    swapForm.toScalarHomogeneousForm.defect x (jordanAction x) = 0 := by
  exact sub_eq_zero.mpr (jordan_form_symmetric x x)

theorem jordan_norm (x : E) : ‖jordanAction x‖ = ‖x.2‖ := by
  simp [jordanAction, Prod.norm_def, norm_nonneg]

theorem mass_le_twice_norm_product (x : E) :
    ‖swapForm.η x x‖ ≤ 2 * ‖x‖ * ‖jordanAction x‖ := by
  have hx : ‖x.1‖ ≤ ‖x‖ := by
    rw [Prod.norm_def]
    exact le_max_left _ _
  calc
    _ ≤ ‖x.1 * conj x.2‖ + ‖x.2 * conj x.1‖ := norm_add_le _ _
    _ = 2 * ‖x.1‖ * ‖x.2‖ := by simp only [norm_mul, norm_conj]; ring
    _ ≤ 2 * ‖x‖ * ‖x.2‖ := by gcongr
    _ = _ := by rw [jordan_norm]

theorem unit_mass_norm_product_lower (x : E) (hmass : ‖swapForm.η x x‖ = 1) :
    1 / 2 ≤ ‖x‖ * ‖jordanAction x‖ := by
  have h := mass_le_twice_norm_product x
  rw [hmass] at h
  linarith

/-- Exact paired control can accommodate this Jordan block even though the
stronger norm-product sufficient condition fails at every unit-mass state. -/
theorem exists_unit_mass_small_residual_and_fixed_norm_product {τ : ℝ} (hτ : 0 < τ) :
    ∃ x : E, x ≠ 0 ∧ swapForm.η x x = 1 ∧ ‖jordanAction x‖ < τ ∧
      swapForm.toScalarHomogeneousForm.defect x (jordanAction x) = 0 ∧
      1 / 2 ≤ ‖x‖ * ‖jordanAction x‖ := by
  have heig : jordanAction ((1, 0) : E) = (0 : ℂ) • ((1, 0) : E) := by
    simp [jordanAction]
  have hB : swapForm.η ((1, 0) : E) ((0, 1) : E) ≠ 0 := by simp [swapForm]
  obtain ⟨x, hx, hm, hr⟩ := PacketMass.exists_unit_mass_small_residual
    swapForm swapForm_hermitian jordanAction heig eigenvector_isotropic hB hτ
  refine ⟨x, hx, hm, ?_, jordan_paired_residual_zero x, ?_⟩
  · simpa using hr
  · exact unit_mass_norm_product_lower x (by rw [hm, norm_one])

end Reinmann.NormProductObstruction
