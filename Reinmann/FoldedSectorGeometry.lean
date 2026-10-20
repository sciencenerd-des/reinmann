/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.QuasiRHInputs
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! Convert a width-to-height tangent bound into the closed argument sector
of a squared zero. No zeta zero or Hadamard-product assertion is assumed here. -/
noncomputable section
namespace Reinmann.FoldedSectorGeometry

/-- Squaring a point close to the imaginary axis places it in the required
closed sector about the negative real axis. The point must be nonzero. -/
theorem arg_square_sector {v : ℂ} (hv : v ≠ 0) {theta : ℝ}
    (h0 : 0 ≤ theta) (htheta : theta ≤ Real.pi / 4)
    (hwidth : |v.re| ≤ |v.im| * Real.tan theta) :
    Real.pi - 2 * theta ≤ |Complex.arg (v ^ 2)| := by
  have hc : 0 < Real.cos theta :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hs : 0 ≤ Real.sin theta :=
    Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [Real.pi_pos])
  rw [Real.tan_eq_sin_div_cos, ← mul_div_assoc] at hwidth
  have hm := (le_div_iff₀ hc).mp hwidth
  have hsq : (|v.re| * Real.cos theta) ^ 2 ≤ (|v.im| * Real.sin theta) ^ 2 :=
    (sq_le_sq₀ (mul_nonneg (abs_nonneg _) hc.le)
      (mul_nonneg (abs_nonneg _) hs)).2 hm
  rw [mul_pow, mul_pow, sq_abs, sq_abs] at hsq
  have hn : ‖v ^ 2‖ = v.re ^ 2 + v.im ^ 2 := by
    rw [norm_pow, Complex.sq_norm, Complex.normSq_apply]
    ring
  have hnpos : 0 < v.re ^ 2 + v.im ^ 2 := by
    rw [← hn]
    exact norm_pos_iff.mpr (pow_ne_zero 2 hv)
  have hre : (v ^ 2).re = v.re ^ 2 - v.im ^ 2 := by
    simp only [pow_two, Complex.mul_re]
  have hsc := congrArg (fun x : ℝ => v.im ^ 2 * x) (Real.sin_sq_add_cos_sq theta)
  have hcos : Real.cos |Complex.arg (v ^ 2)| ≤ Real.cos (Real.pi - 2 * theta) := by
    rw [Real.cos_abs, Complex.cos_arg (pow_ne_zero 2 hv), hre, hn,
      Real.cos_pi_sub, Real.cos_two_mul]
    apply (div_le_iff₀ hnpos).2
    nlinarith
  exact (Real.strictAntiOn_cos.le_iff_ge
    ⟨abs_nonneg _, Complex.abs_arg_le_pi _⟩
    ⟨by linarith [Real.pi_pos], by linarith⟩).mp hcos

/-- The exact rank-m angle convention used by the existing Xi interface. -/
theorem arg_folded_sector {m : ℕ} (hm : 0 < m) {s : ℂ} (hs : s ≠ 1 / 2)
    (hwidth : |s.re - 1 / 2| ≤ |s.im| * Real.tan (pfHalfAngle m)) :
    Real.pi - Real.pi / ((m : ℝ) + 1) ≤ |Complex.arg ((s - 1 / 2) ^ 2)| := by
  have h := arg_square_sector (sub_ne_zero.mpr hs) (pfHalfAngle_pos m).le
    (pfHalfAngle_le_quarter hm) (by simpa using hwidth)
  have hd : 2 * pfHalfAngle m = Real.pi / ((m : ℝ) + 1) := by
    unfold pfHalfAngle
    have hm0 : (m : ℝ) + 1 ≠ 0 := ne_of_gt (by positivity)
    field_simp [hm0]
  rwa [hd] at h

end Reinmann.FoldedSectorGeometry
