/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Gaussian truncation of the actual theta kernel, uniformly for t ≥ 1.
This is independent of the Mellin integral truncation and quadrature errors. -/
noncomputable section
namespace Reinmann
open HurwitzZeta Finset

def thetaFinite (N : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ range N, 2 * Real.exp (-Real.pi * (n+1 : ℝ)^2 * t)

theorem theta_shifted_term_bound {t : ℝ} (ht : 1 ≤ t) (N n : ℕ) :
    Real.exp (-Real.pi * (N+n+1 : ℝ)^2 * t) ≤
      Real.exp (-Real.pi * (N+1 : ℝ)^2 * t) * (1/2 : ℝ)^n := by
  have ht0 : 0 ≤ t := by linarith
  have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hs : (N+1 : ℝ)^2 + n ≤ (N+n+1 : ℝ)^2 := by nlinarith
  have he : Real.exp (-t) ≤ (1/2 : ℝ) := by
    have h1 : 2 < Real.exp 1 := by
      linarith [Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)]
    have h2 := Real.exp_le_exp.mpr ht
    rw [Real.exp_neg, ← one_div]
    apply (div_le_iff₀ (Real.exp_pos t)).mpr
    linarith
  calc
    Real.exp (-Real.pi * (N+n+1 : ℝ)^2 * t) ≤
        Real.exp (-Real.pi * (N+1 : ℝ)^2 * t - n*t) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hs (mul_nonneg (by positivity : 0 ≤ Real.pi) ht0),
        mul_le_mul_of_nonneg_right hpi (mul_nonneg hn ht0)]
    _ = Real.exp (-Real.pi * (N+1 : ℝ)^2 * t) * Real.exp (-t)^n := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.exp_pos _).le he _)
      (Real.exp_pos _).le

/-- The error is the actual omitted theta series, with Gaussian rather than
merely geometric decay in the number of retained terms. -/
theorem thetaFinite_error_bounds {t : ℝ} (ht : 1 ≤ t) (N : ℕ) :
    0 ≤ cosKernel 0 t - 1 - thetaFinite N t ∧
    cosKernel 0 t - 1 - thetaFinite N t ≤
      4 * Real.exp (-Real.pi * (N+1 : ℝ)^2 * t) := by
  have hs : HasSum (fun n : ℕ => 2 * Real.exp (-Real.pi * (n+1 : ℝ)^2 * t))
      (cosKernel 0 t - 1) := by
    simpa using hasSum_nat_cosKernel₀ 0 (by linarith : 0 < t)
  have htail : HasSum (fun n : ℕ => 2 * Real.exp (-Real.pi * (n+N+1 : ℝ)^2 * t))
      (cosKernel 0 t - 1 - thetaFinite N t) := by
    simpa only [Nat.cast_add, thetaFinite] using (hasSum_nat_add_iff' N).mpr hs
  have hg := hasSum_geometric_two.mul_left
    (2 * Real.exp (-Real.pi * (N+1 : ℝ)^2 * t))
  constructor
  · exact HasSum.nonneg (fun n => by positivity) htail
  · have h := hasSum_le (fun n => by
      have hb := theta_shifted_term_bound ht N n
      rw [add_comm (N : ℝ) (n : ℝ)] at hb
      nlinarith) htail hg
    nlinarith

theorem thetaFinite_error_le_uniform {t : ℝ} (ht : 1 ≤ t) (N : ℕ) :
    |cosKernel 0 t - 1 - thetaFinite N t| ≤
      4 * Real.exp (-Real.pi * (N+1 : ℝ)^2) := by
  obtain ⟨h0,h1⟩ := thetaFinite_error_bounds ht N
  rw [abs_of_nonneg h0]
  apply h1.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  have hmul := mul_le_mul_of_nonneg_left ht
    (mul_nonneg Real.pi_pos.le (sq_nonneg (N+1 : ℝ)))
  nlinarith only [hmul]

/-- The theta cutoff error remains uniform after the actual Mellin weight.
Both parameters s/2 and (1-s)/2 on the critical rectangle satisfy this half-plane bound. -/
theorem thetaFinite_weighted_error_le {t : ℝ} (ht : 1 ≤ t) (N : ℕ)
    {s : ℂ} (hs : s.re ≤ 1) :
    ‖(t : ℂ)^(s-1) • ((cosKernel 0 t-1-thetaFinite N t : ℝ) : ℂ)‖ ≤
      4 * Real.exp (-Real.pi * (N+1 : ℝ)^2) := by
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < t),
    Complex.norm_real, Real.norm_eq_abs]
  have hw : t^(s-1).re ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht
    (by simpa using sub_nonpos.mpr hs)
  calc
    _ ≤ 1 * |cosKernel 0 t-1-thetaFinite N t| :=
      mul_le_mul_of_nonneg_right hw (abs_nonneg _)
    _ ≤ _ := by simpa using thetaFinite_error_le_uniform ht N

/-- Finite-interval integrated theta error, separate from the truncation at T. -/
theorem thetaFinite_integrated_error_le {T : ℝ} (hT : 1 ≤ T) (N : ℕ)
    {s : ℂ} (hs : s.re ≤ 1) :
    ‖∫ t in (1 : ℝ)..T,
      (t : ℂ)^(s-1) • ((cosKernel 0 t-1-thetaFinite N t : ℝ) : ℂ)‖ ≤
      (4 * Real.exp (-Real.pi * (N+1 : ℝ)^2)) * (T-1) := by
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun t : ℝ => (t : ℂ)^(s-1) •
      ((cosKernel 0 t-1-thetaFinite N t : ℝ) : ℂ))
    (a := 1) (b := T) (fun t ht =>
      thetaFinite_weighted_error_le (by
        rw [Set.uIoc_of_le hT] at ht
        exact ht.1.le) N hs)
  simpa only [abs_of_nonneg (sub_nonneg.mpr hT)] using hb

end Reinmann
