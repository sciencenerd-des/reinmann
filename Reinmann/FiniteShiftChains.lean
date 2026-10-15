/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Support-sensitive translation chain bounds

These Hilbert-space inequalities give both pointwise fiber estimates and
integrated L² chain estimates. `SupportTranslation` proves the support-to-fiber
decomposition, and `SupportPrimeForm` proves the uniform prime integral bound.
The archimedean Weil specialization and intermediate spectral gap remain open.
-/
noncomputable section
namespace Reinmann.FiniteShiftChains
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Weighted Young inequality for the absolute inner product. -/
theorem weighted_edge (x y : H) (t : ℝ) (ht : 0 ≤ t) :
    2 * t * |inner ℝ x y| ≤ t ^ 2 * ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  have h := mul_le_mul_of_nonneg_left (abs_real_inner_le_norm x y)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) ht)
  nlinarith [sq_nonneg (t * ‖x‖ - ‖y‖)]

/-- A two-point translation chain costs one, rather than two, times its energy. -/
theorem chain_two (x y : H) :
    2 * |inner ℝ x y| ≤ ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  simpa using weighted_edge x y 1 (by norm_num)

/-- Sharp three-point chain constant. Zero padding covers shorter chains. -/
theorem chain_three (x₀ x₁ x₂ : H) :
    2 * (|inner ℝ x₀ x₁| + |inner ℝ x₁ x₂|) ≤
      Real.sqrt 2 * (‖x₀‖ ^ 2 + ‖x₁‖ ^ 2 + ‖x₂‖ ^ 2) := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsq : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hmul : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := by nlinarith [hsq]
  have h₀ := weighted_edge x₀ x₁ (Real.sqrt 2) (le_of_lt hs)
  have h₁ := weighted_edge x₂ x₁ (Real.sqrt 2) (le_of_lt hs)
  rw [hsq] at h₀ h₁
  rw [real_inner_comm x₁ x₂] at h₁
  apply (mul_le_mul_iff_left₀ hs).mp
  calc
    _ = 2 * Real.sqrt 2 * (|inner ℝ x₀ x₁| + |inner ℝ x₁ x₂|) := by ring
    _ ≤ 2 * (‖x₀‖ ^ 2 + ‖x₁‖ ^ 2 + ‖x₂‖ ^ 2) := by linarith
    _ = _ := by calc
      _ = (Real.sqrt 2 * Real.sqrt 2) *
          (‖x₀‖ ^ 2 + ‖x₁‖ ^ 2 + ‖x₂‖ ^ 2) := by rw [hmul]
      _ = _ := by ring

/-- Sharp five-point chain constant, retaining the common middle-coordinate energy. -/
theorem chain_five (x₀ x₁ x₂ x₃ x₄ : H) :
    2 * (|inner ℝ x₀ x₁| + |inner ℝ x₁ x₂| +
      |inner ℝ x₂ x₃| + |inner ℝ x₃ x₄|) ≤
      Real.sqrt 3 * (‖x₀‖ ^ 2 + ‖x₁‖ ^ 2 + ‖x₂‖ ^ 2 + ‖x₃‖ ^ 2 + ‖x₄‖ ^ 2) := by
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hsq : Real.sqrt 3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  have hmul : Real.sqrt 3 * Real.sqrt 3 = (3 : ℝ) := by nlinarith [hsq]
  have hh : (Real.sqrt 3 / 2) ^ 2 = (3 / 4 : ℝ) := by rw [div_pow, hsq]; norm_num
  have h₀ := weighted_edge x₀ x₁ (Real.sqrt 3) (le_of_lt hs)
  have h₁ := weighted_edge x₂ x₁ (Real.sqrt 3 / 2) (by positivity)
  have h₂ := weighted_edge x₂ x₃ (Real.sqrt 3 / 2) (by positivity)
  have h₃ := weighted_edge x₄ x₃ (Real.sqrt 3) (le_of_lt hs)
  rw [hsq] at h₀ h₃
  rw [hh] at h₁ h₂
  rw [real_inner_comm x₁ x₂] at h₁
  rw [real_inner_comm x₃ x₄] at h₃
  apply (mul_le_mul_iff_left₀ hs).mp
  calc
    _ = 2 * Real.sqrt 3 * (|inner ℝ x₀ x₁| + |inner ℝ x₁ x₂| +
        |inner ℝ x₂ x₃| + |inner ℝ x₃ x₄|) := by ring
    _ ≤ 3 * (‖x₀‖ ^ 2 + ‖x₁‖ ^ 2 + ‖x₂‖ ^ 2 + ‖x₃‖ ^ 2 + ‖x₄‖ ^ 2) := by linarith
    _ = _ := by calc
      _ = (Real.sqrt 3 * Real.sqrt 3) *
          (‖x₀‖ ^ 2 + ‖x₁‖ ^ 2 + ‖x₂‖ ^ 2 + ‖x₃‖ ^ 2 + ‖x₄‖ ^ 2) := by rw [hmul]
      _ = _ := by ring

section Integrated
open MeasureTheory
open scoped ENNReal
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The L² norm is the integral of the pointwise squared norm. -/
theorem l2_energy (f : Lp H 2 μ) :
    ‖f‖ ^ 2 = ∫ s, ‖f s‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

/-- Two integrated fibers: all integrability is supplied by their L² membership. -/
theorem integrated_chain_two (f₀ f₁ : Lp H 2 μ) :
    2 * |∫ s, inner ℝ (f₀ s) (f₁ s) ∂μ| ≤
      (∫ s, ‖f₀ s‖ ^ 2 ∂μ) + (∫ s, ‖f₁ s‖ ^ 2 ∂μ) := by
  simpa only [L2.inner_def, l2_energy] using chain_two f₀ f₁

/-- Three integrated fibers retain the sharp √2 constant. -/
theorem integrated_chain_three (f₀ f₁ f₂ : Lp H 2 μ) :
    2 * (|∫ s, inner ℝ (f₀ s) (f₁ s) ∂μ| +
      |∫ s, inner ℝ (f₁ s) (f₂ s) ∂μ|) ≤
      Real.sqrt 2 * ((∫ s, ‖f₀ s‖ ^ 2 ∂μ) +
        (∫ s, ‖f₁ s‖ ^ 2 ∂μ) + (∫ s, ‖f₂ s‖ ^ 2 ∂μ)) := by
  simpa only [L2.inner_def, l2_energy] using chain_three f₀ f₁ f₂

/-- Five integrated fibers retain the sharp √3 constant, uniformly in the measure. -/
theorem integrated_chain_five (f₀ f₁ f₂ f₃ f₄ : Lp H 2 μ) :
    2 * (|∫ s, inner ℝ (f₀ s) (f₁ s) ∂μ| +
      |∫ s, inner ℝ (f₁ s) (f₂ s) ∂μ| +
      |∫ s, inner ℝ (f₂ s) (f₃ s) ∂μ| +
      |∫ s, inner ℝ (f₃ s) (f₄ s) ∂μ|) ≤
      Real.sqrt 3 * ((∫ s, ‖f₀ s‖ ^ 2 ∂μ) +
        (∫ s, ‖f₁ s‖ ^ 2 ∂μ) + (∫ s, ‖f₂ s‖ ^ 2 ∂μ) +
        (∫ s, ‖f₃ s‖ ^ 2 ∂μ) + (∫ s, ‖f₄ s‖ ^ 2 ∂μ)) := by
  simpa only [L2.inner_def, l2_energy] using chain_five f₀ f₁ f₂ f₃ f₄
end Integrated

end Reinmann.FiniteShiftChains
