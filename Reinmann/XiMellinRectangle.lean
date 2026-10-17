/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.XiMellinRemainder

/-!
# Uniform actual-Xi Mellin tail on a closed low-zero rectangle

This controls the shared integral truncation error, not the finite-theta
summation or quadrature error, and does not assert zero exclusion.
-/
noncomputable section
namespace Reinmann

/-- The norm prefactor is uniform on the entire closed rectangle. -/
theorem norm_mul_norm_sub_one_le_rectangle {s : ℂ} {H : ℝ}
    (hl : 0 ≤ s.re) (hu : s.re ≤ 1) (hi : |s.im| ≤ H) :
    ‖s‖ * ‖s - 1‖ ≤ 1 + H ^ 2 := by
  have hH : 0 ≤ H := (abs_nonneg _).trans hi
  have him : s.im ^ 2 ≤ H ^ 2 := by
    have hp := mul_nonneg (sub_nonneg.mpr hi) (add_nonneg hH (abs_nonneg s.im))
    nlinarith [sq_abs s.im]
  have hre : s.re ^ 2 ≤ 1 := by nlinarith [sq_nonneg (s.re - 1)]
  have hre' : (s.re - 1) ^ 2 ≤ 1 := by nlinarith [sq_nonneg s.re]
  have hnorm : ‖s‖ ^ 2 ≤ 1 + H ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith
  have hnorm' : ‖s - 1‖ ^ 2 ≤ 1 + H ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
      sub_zero]
    nlinarith
  nlinarith [sq_nonneg (‖s‖ - ‖s - 1‖)]

/-- A proved uniform upper bound, with no external interval certificate. -/
theorem xiMellinRemainder_norm_le_rectangle {T H : ℝ} (hT : 1 ≤ T)
    {s : ℂ} (hl : 0 ≤ s.re) (hu : s.re ≤ 1) (hi : |s.im| ≤ H) :
    ‖xiMellinRemainder T s‖ ≤ 2 * (1 + H ^ 2) * Real.exp (-T) := by
  have h := xiMellinRemainder_norm_le hT (s := s) (by linarith) (by linarith)
  have hp := norm_mul_norm_sub_one_le_rectangle hl hu hi
  calc
    ‖xiMellinRemainder T s‖ ≤ 2 * ‖s‖ * ‖s - 1‖ * Real.exp (-T) := h
    _ ≤ 2 * (1 + H ^ 2) * Real.exp (-T) := by
      exact mul_le_mul_of_nonneg_right (by nlinarith) (Real.exp_pos _).le

/-- The bound applies to the actual Xi-minus-truncation error. -/
theorem xiMellinTruncation_error_le_rectangle {T H : ℝ} (hT : 1 ≤ T)
    {s : ℂ} (hl : 0 ≤ s.re) (hu : s.re ≤ 1) (hi : |s.im| ≤ H) :
    ‖xiCompleted s - xiMellinTruncation T s‖ ≤
      2 * (1 + H ^ 2) * Real.exp (-T) := by
  rw [← xiMellinRemainder_eq_sub hT]
  exact xiMellinRemainder_norm_le_rectangle hT hl hu hi

/-- The rational height used by the named finite-PF input. -/
theorem xiMellinTruncation_error_le_low_rectangle {T : ℝ} (hT : 1 ≤ T)
    {s : ℂ} (hl : 0 ≤ s.re) (hu : s.re ≤ 1) (hi : |s.im| ≤ (141 / 10 : ℝ)) :
    ‖xiCompleted s - xiMellinTruncation T s‖ ≤
      (19981 / 50 : ℝ) * Real.exp (-T) := by
  have h := xiMellinTruncation_error_le_rectangle hT hl hu hi
  norm_num at h ⊢
  exact h

end Reinmann
