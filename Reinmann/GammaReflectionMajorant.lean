/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal

The Beta comparison is adapted from OpenAI math, GammaBetaComparison.lean,
Git blob 9d30e92d96e42bc7b996799d87acab1bf3ead172 (Apache-2.0).
-/
import Reinmann.GammaHeightMajorant
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Reflection controls a product, not either factor separately. On Re z = 1/2
the factors have equal norms. The Beta comparison supplies the additional
one-sided control for moving to other real parts. -/
noncomputable section
namespace Reinmann.GammaReflectionMajorant
open Complex MeasureTheory Set Finset

private theorem beta_real_integral_eq (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (∫ t : ℝ in (0 : ℝ)..1, t^(x-1)*(1-t)^(y-1)) =
      Real.Gamma x*Real.Gamma y/Real.Gamma (x+y) := by
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  have he : (∫ t : ℝ in (0 : ℝ)..1, ((t^(x-1)*(1-t)^(y-1) : ℝ) : ℂ)) =
      Complex.betaIntegral (x : ℂ) (y : ℂ) := by
    unfold Complex.betaIntegral
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    simp only [Complex.ofReal_mul, Complex.ofReal_cpow ht.1,
      Complex.ofReal_cpow (sub_nonneg.mpr ht.2), Complex.ofReal_sub, Complex.ofReal_one]
  rw [he, Complex.betaIntegral_eq_Gamma_mul_div _ _ (by simpa using hx) (by simpa using hy)]
  simp only [Complex.ofReal_div, Complex.ofReal_mul, ← Complex.ofReal_add, Complex.Gamma_ofReal]

theorem beta_norm_le_real (s : ℂ) {d : ℝ} (hs : 0 < s.re) (hd : 0 < d) :
    ‖Complex.betaIntegral s (d : ℂ)‖ ≤
      Real.Gamma s.re*Real.Gamma d/Real.Gamma (s.re+d) := by
  rw [← beta_real_integral_eq s.re d hs hd]
  unfold Complex.betaIntegral
  apply (intervalIntegral.norm_integral_le_integral_norm (by norm_num : (0 : ℝ) ≤ 1)).trans_eq
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  dsimp only
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht.1]
  have hp : 0 < 1-t := sub_pos.mpr ht.2
  rw [show (1 : ℂ)-(t : ℂ) = ((1-t : ℝ) : ℂ) by push_cast; rfl,
    Complex.norm_cpow_eq_rpow_re_of_pos hp]
  simp

theorem gamma_real_shift_ratio_bound (s : ℂ) {d : ℝ} (hs : 0 < s.re) (hd : 0 < d) :
    ‖Complex.Gamma s‖/‖Complex.Gamma (s+(d : ℂ))‖ ≤
      Real.Gamma s.re/Real.Gamma (s.re+d) := by
  have h := beta_norm_le_real s hs hd
  have hg : 0 < Real.Gamma d := Real.Gamma_pos_of_pos hd
  rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ hs (by simpa using hd),
    norm_div, norm_mul, Complex.Gamma_ofReal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hg] at h
  apply (mul_le_mul_iff_right₀ hg).mp
  convert h using 1 <;> ring

/-- A usable one-sided bound; its denominator is nonzero by positive real part. -/
theorem gamma_norm_le_shifted_anchor (s : ℂ) {d : ℝ} (hs : 0 < s.re) (hd : 0 < d) :
    ‖Complex.Gamma s‖ ≤
      (Real.Gamma s.re/Real.Gamma (s.re+d))*‖Complex.Gamma (s+(d : ℂ))‖ := by
  have hp : 0 < ‖Complex.Gamma (s+(d : ℂ))‖ := norm_pos_iff.mpr
    (Complex.Gamma_ne_zero_of_re_pos (by simp only [Complex.add_re, Complex.ofReal_re]; linarith))
  exact (div_le_iff₀ hp).mp (gamma_real_shift_ratio_bound s hs hd)

/-- The genuine reflection consequence, before any one-sided comparison. -/
theorem gamma_reflection_norm_product (z : ℂ) :
    ‖Complex.Gamma z‖*‖Complex.Gamma (1-star z)‖ =
      Real.pi/‖Complex.sin (Real.pi*z)‖ := by
  have h := congrArg norm (Complex.Gamma_mul_Gamma_one_sub z)
  have hg : ‖Complex.Gamma (1-star z)‖ = ‖Complex.Gamma (1-z)‖ := by
    have he : 1-star z = star (1-z) := by simp
    rw [he]
    simpa using congrArg norm (Complex.Gamma_conj (1-z))
  rw [hg]
  simpa only [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos] using h

/-- Exact reflection identity on the half line. -/
theorem gamma_half_norm_sq (y : ℝ) :
    ‖Complex.Gamma ((1/2 : ℂ)+(y : ℂ)*Complex.I)‖^2 =
      Real.pi/Real.cosh (Real.pi*y) := by
  let z : ℂ := (1/2 : ℂ)+(y : ℂ)*Complex.I
  have hstar : 1-star z = z := by
    apply Complex.ext <;> norm_num [z]
  have hsin : Complex.sin (Real.pi*z) = (Real.cosh (Real.pi*y) : ℂ) := by
    have he : (Real.pi : ℂ)*z = (Real.pi/2 : ℂ)+((Real.pi*y : ℝ) : ℂ)*Complex.I := by
      dsimp [z]
      push_cast
      ring
    rw [he, Complex.sin_add_mul_I]
    simp only [Complex.sin_pi_div_two, Complex.cos_pi_div_two, one_mul, zero_mul,
      add_zero, ← Complex.ofReal_cosh]
  have h := gamma_reflection_norm_product z
  rw [hstar, hsin, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.cosh_pos _)] at h
  simpa only [pow_two, z] using h

/-- Exponential decay, with an explicit constant and no Stirling input. -/
theorem gamma_half_norm_sq_le_exp (y : ℝ) :
    ‖Complex.Gamma ((1/2 : ℂ)+(y : ℂ)*Complex.I)‖^2 ≤
      2*Real.pi*Real.exp (-Real.pi*|y|) := by
  have habs : |Real.pi*y| = Real.pi*|y| := by rw [abs_mul, abs_of_pos Real.pi_pos]
  have hc : Real.cosh (Real.pi*|y|) = Real.cosh (Real.pi*y) := by
    rw [← habs, Real.cosh_abs]
  have hcosh : Real.exp (Real.pi*|y|)/2 ≤ Real.cosh (Real.pi*y) := by
    have h : 2*Real.cosh (Real.pi*|y|) =
        Real.exp (Real.pi*|y|)+Real.exp (-(Real.pi*|y|)) := by
      apply Complex.ofReal_injective
      simpa using Complex.two_cosh ((Real.pi*|y| : ℝ) : ℂ)
    rw [hc] at h
    linarith [Real.exp_pos (-(Real.pi*|y|))]
  rw [gamma_half_norm_sq]
  apply (div_le_iff₀ (Real.cosh_pos _)).mpr
  have h := mul_le_mul_of_nonneg_left hcosh
    (mul_nonneg (by positivity : 0 ≤ 2*Real.pi) (Real.exp_pos (-Real.pi*|y|)).le)
  have he : Real.exp (Real.pi*|y|)*Real.exp (-Real.pi*|y|) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have hm : 2*Real.pi*Real.exp (-Real.pi*|y|)*(Real.exp (Real.pi*|y|)/2) =
      Real.pi := by
    calc
      _ = Real.pi*(Real.exp (Real.pi*|y|)*Real.exp (-Real.pi*|y|)) := by ring
      _ = _ := by rw [he, mul_one]
  rwa [hm] at h

theorem gamma_half_norm_le_sqrt_exp (y : ℝ) :
    ‖Complex.Gamma ((1/2 : ℂ)+(y : ℂ)*Complex.I)‖ ≤
      Real.sqrt (2*Real.pi*Real.exp (-Real.pi*|y|)) := by
  apply (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
  exact gamma_half_norm_sq_le_exp y

/-- The second exact anchor used by the external strip-bound pilot. -/
theorem gamma_one_norm_sq (y : ℝ) (hy : y ≠ 0) :
    ‖Complex.Gamma (1+(y : ℂ)*Complex.I)‖^2 =
      Real.pi*|y|/|Real.sinh (Real.pi*y)| := by
  let z : ℂ := (y : ℂ)*Complex.I
  have hz : z ≠ 0 := by
    intro h
    have hm := congrArg Complex.im h
    apply hy
    simpa [z] using hm
  have hline : 1-star z = 1+z := by simp [z]
  have hrec : ‖Complex.Gamma (1+z)‖ = |y| *‖Complex.Gamma z‖ := by
    have h := congrArg norm (Complex.Gamma_add_one z hz)
    simpa [add_comm, z, norm_mul, Complex.norm_real, Real.norm_eq_abs] using h
  have hsin : Complex.sin (Real.pi*z) = (Real.sinh (Real.pi*y) : ℂ)*Complex.I := by
    have he : (Real.pi : ℂ)*z = ((Real.pi*y : ℝ) : ℂ)*Complex.I := by
      dsimp [z]
      push_cast
      ring
    rw [he, Complex.sin_mul_I, ← Complex.ofReal_sinh]
  have h := gamma_reflection_norm_product z
  rw [hline, hsin, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs] at h
  calc
    _ = |y| *(‖Complex.Gamma z‖*‖Complex.Gamma (1+z)‖) := by rw [hrec]; ring
    _ = _ := by rw [h]; ring

end Reinmann.GammaReflectionMajorant
