/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.XiLocalCauchy
import Reinmann.UniformXiRemainders
import Reinmann.CertifiedComplexInputs

/-! Explicit evaluator bounds for the new finite-height boxes. The old height-14.1
certificate is unchanged. Gamma's existing bounds are height-independent; the
Xi majorant and the larger zeta error budget below are proved up to height 32. -/
noncomputable section
namespace Reinmann.FiniteBandBounds
open Metric Finset Complex
open RegularizedEulerMaclaurin EulerMaclaurinAnalytic

theorem unit_circle_bound {c z : ℂ}
    (hl : (1 / 2 : ℝ) ≤ c.re) (hu : c.re ≤ 1) (hi : |c.im| ≤ (32 : ℝ))
    (hz : z ∈ sphere c 1) : ‖xiCompleted z‖ ≤ 1000 := by
  have hd : ‖z - c‖ = 1 := mem_sphere_iff_norm.mp hz
  have hr : |z.re - c.re| ≤ 1 := by
    simpa only [Complex.sub_re, hd] using Complex.abs_re_le_norm (z - c)
  have hb := abs_le.mp hr
  have hci := abs_le.mp hi
  have hc : ‖c‖ ≤ 33 := by
    have hs : ‖c‖ ^ 2 = c.re ^ 2 + c.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    nlinarith [norm_nonneg c, sq_nonneg (c.re - 1)]
  have hc1 : ‖c - 1‖ ≤ 33 := by
    have hs : ‖c - 1‖ ^ 2 = (c.re - 1) ^ 2 + c.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
      ring
    nlinarith [norm_nonneg (c - 1), sq_nonneg c.re]
  have hz0 : ‖z‖ ≤ 34 := by
    calc
      ‖z‖ = ‖(z - c) + c‖ := by congr 1; ring
      _ ≤ ‖z - c‖ + ‖c‖ := norm_add_le _ _
      _ ≤ 34 := by rw [hd]; linarith
  have hz1 : ‖z - 1‖ ≤ 34 := by
    calc
      ‖z - 1‖ = ‖(z - c) + (c - 1)‖ := by congr 1; ring
      _ ≤ ‖z - c‖ + ‖c - 1‖ := norm_add_le _ _
      _ ≤ 34 := by rw [hd]; linarith
  have he : Real.exp (-1) ≤ (2 / 5 : ℝ) := by
    have hb : (5 / 2 : ℝ) ≤ Real.exp 1 := by
      have h := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)
      norm_num at h
      linarith
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 5 / 2) hb
    simpa only [Real.exp_neg, one_div, inv_div, inv_one] using h
  have hp : ‖z‖ * ‖z - 1‖ ≤ 1156 :=
    (mul_le_mul hz0 hz1 (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have h := XiLocalCauchy.xi_norm_le (z := z) (by linarith [hb.1]) (by linarith [hb.2])
  have hm := mul_le_mul_of_nonneg_left he (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    (mul_nonneg (norm_nonneg z) (norm_nonneg (z - 1))))
  nlinarith

/-- Actual Taylor coefficients on each such circle have a uniform Cauchy bound. -/
theorem coefficient_bound {c : ℂ}
    (hl : (1 / 2 : ℝ) ≤ c.re) (hu : c.re ≤ 1) (hi : |c.im| ≤ (32 : ℝ))
    (n : ℕ) : ‖iteratedDeriv n xiCompleted c‖ ≤ n.factorial * 1000 := by
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n
    (by norm_num : (0 : ℝ) < 1) differentiable_xiCompleted.diffContOnCl
    (fun z hz => unit_circle_bound hl hu hi hz)
  simpa using h

/-- The normalized ordinary Taylor coefficients used by the Arb pilot. -/
theorem taylor_coefficient_bound {c : ℂ}
    (hl : (1 / 2 : ℝ) ≤ c.re) (hu : c.re ≤ 1) (hi : |c.im| ≤ (32 : ℝ))
    (n : ℕ) : ‖iteratedDeriv n xiCompleted c / (n.factorial : ℂ)‖ ≤ 1000 := by
  rw [norm_div, Complex.norm_natCast]
  apply (div_le_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos n))).mpr
  exact (coefficient_bound hl hu hi n).trans_eq (by ring)


/-- Norm bounds on unit disks around centres in the height-32 quarter. -/
theorem disk_norm_bounds {c s : ℂ} (hc : c ∈ XiAdaptiveTiles.quarter 32)
    (hs : ‖s-c‖ ≤ 1) : ‖s‖ ≤ 34 ∧ ‖s-1‖ ≤ 34 := by
  obtain ⟨hl, hu, hi0, hi⟩ := hc
  have hcn : ‖c‖ ≤ 33 := by
    have hsq : ‖c‖ ^ 2 = c.re ^ 2 + c.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    nlinarith [norm_nonneg c, sq_nonneg (c.re-1)]
  have hc1 : ‖c-1‖ ≤ 33 := by
    have hsq : ‖c-1‖ ^ 2 = (c.re-1)^2+c.im^2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
      ring
    nlinarith [norm_nonneg (c-1), sq_nonneg c.re]
  constructor
  · calc ‖s‖ = ‖(s-c)+c‖ := by rw [sub_add_cancel]
         _ ≤ ‖s-c‖+‖c‖ := norm_add_le _ _
         _ ≤ 34 := by linarith
  · calc ‖s-1‖ = ‖(s-c)+(c-1)‖ := by congr 1; ring
         _ ≤ ‖s-c‖+‖c-1‖ := norm_add_le _ _
         _ ≤ 34 := by linarith

/-- The Gamma norm estimate has no imaginary-height assumption. -/
theorem gamma_norm_on_disk {c s : ℂ} (hl : (1/2:ℝ) ≤ c.re) (hu : c.re ≤ 1)
    (hs : ‖s-c‖ ≤ 1) : ‖gammaFactor s‖ ≤ 2 :=
  UniformXiRemainders.gamma_norm_le_two
    (UniformXiRemainders.disk_re_bounds hl hu hs).1
    (UniformXiRemainders.disk_re_bounds hl hu hs).2

/-- The unchanged 4e-14 Gamma coefficient error is valid at every height. -/
theorem gamma_coefficient_error_le {c : ℂ} (hl : (1/2:ℝ) ≤ c.re) (hu : c.re ≤ 1)
    (n : ℕ) :
    ‖iteratedDeriv n gammaFactor c / (n.factorial:ℂ) -
      iteratedDeriv n UniformXiRemainders.gammaApprox c / (n.factorial:ℂ)‖ ≤
      (4/10^14:ℝ) := UniformXiRemainders.gamma_coefficient_error_le hl hu n

private theorem rising_norm_le {s : ℂ} (hs : ‖s‖ ≤ 34) (n : ℕ) :
    ‖(ascPochhammer ℂ n).eval s‖ ≤ ∏ j ∈ range n, ((34 : ℝ) + j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval, norm_mul, prod_range_succ]
    apply mul_le_mul ih _ (norm_nonneg _) (by positivity)
    exact (norm_add_le s (n : ℂ)).trans (by simpa using add_le_add_right hs (n : ℝ))

theorem zetaError_norm_le {c s : ℂ} (hc : c ∈ XiAdaptiveTiles.quarter 32)
    (hs : ‖s - c‖ ≤ 1) : ‖UniformXiRemainders.zetaError s‖ ≤ (1 / 5000 : ℝ) := by
  have hre := (UniformXiRemainders.disk_re_bounds hc.1 hc.2.1 hs).1
  have hn := disk_norm_bounds hc hs
  have hpos : 0 < s.re + 11 := by linarith
  have hR := EulerMaclaurinTail.remainder_norm_le (by linarith : -11 < s.re)
    (by norm_num : (0 : ℝ) < 27)
  have hP := rising_norm_le hn.1 12
  have ha := div_le_div_of_nonneg_right hP (Nat.cast_nonneg (α := ℝ) (12 : ℕ).factorial)
  have hexp : (27 : ℝ) ^ (-s.re - 11) ≤ (27 : ℝ) ^ (-10 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hb : (6112 / 15015 : ℝ) * (27 : ℝ) ^ (-s.re - 11) / (s.re + 11) ≤
      (6112 / 15015 : ℝ) * (27 : ℝ) ^ (-10 : ℝ) / (21 / 2) := by
    calc
      _ ≤ (6112 / 15015 : ℝ) * (27 : ℝ) ^ (-10 : ℝ) / (s.re + 11) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hexp (by norm_num)) hpos.le
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
  have htail := hR.trans (mul_le_mul ha hb (by positivity)
    (by positivity : 0 ≤ (∏ j ∈ range 12, ((34 : ℝ) + j)) / ((12 : ℕ).factorial : ℝ)))
  rw [UniformXiRemainders.zetaError, regularZeta_eq_model_add_remainder (by linarith : -11 < s.re) 27
    (by norm_num), add_sub_cancel_left, norm_mul]
  apply (mul_le_mul hn.2 htail (norm_nonneg _) (by norm_num)).trans
  norm_num [Real.rpow_neg, Real.rpow_natCast, prod_range_succ]

/-- The same 2e-4 budget works for every centre, including height zero. -/
theorem zeta_coefficient_error_le {c : ℂ} (hc : c ∈ XiAdaptiveTiles.quarter 32)
    (n : ℕ) :
    ‖iteratedDeriv n regularZeta c / (n.factorial : ℂ) -
      iteratedDeriv n (fun z => regularModel z 27) c / (n.factorial : ℂ)‖ ≤
      (1 / 5000 : ℝ) := by
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n
    (by norm_num : (0 : ℝ) < 1) UniformXiRemainders.zetaError_differentiable.diffContOnCl
    (fun z hz => zetaError_norm_le hc (mem_sphere_iff_norm.mp hz).le)
  have heq : iteratedDeriv n UniformXiRemainders.zetaError c = iteratedDeriv n regularZeta c -
      iteratedDeriv n (fun z => regularModel z 27) c := by
    exact iteratedDeriv_fun_sub (regularZeta_differentiable.analyticAt c).contDiffAt
      ((regularModel_differentiable 27 (by norm_num)).analyticAt c).contDiffAt
  rw [heq] at h
  simp only [one_pow, div_one] at h
  rw [← sub_div, norm_div, Complex.norm_natCast]
  exact (div_le_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos n))).mpr (h.trans_eq (by ring))

/-- A larger proved log-series disk for the shifted Gamma factor. -/
theorem log_series_error {z : ℂ} (hz : ‖z‖ ≤ 4 / 5) :
    ‖Complex.log (1 + z) - Complex.logTaylor 160 z‖ ≤ (1 / 10 ^ 15 : ℝ) := by
  have hlt : ‖z‖ < 1 := lt_of_le_of_lt hz (by norm_num)
  have hi : (1 - ‖z‖)⁻¹ ≤ (5 : ℝ) := by
    rw [inv_le_comm₀ (by linarith : 0 < 1 - ‖z‖) (by norm_num : (0 : ℝ) < 5)]
    norm_num
    linarith
  calc
    _ ≤ ‖z‖ ^ 160 * (1 - ‖z‖)⁻¹ / 160 := by
      convert Complex.norm_log_sub_logTaylor_le 159 hlt using 1 <;> norm_num
    _ ≤ (4 / 5 : ℝ) ^ 160 * 5 / 160 := by gcongr
    _ ≤ _ := by norm_num

theorem log_series_contains {z : ℂ} {a : CertifiedTaylorModel.Disk} (hz : ‖z‖ ≤ 4 / 5)
    (ha : CertifiedTaylorModel.Contains a (Complex.logTaylor 160 z)) :
    CertifiedTaylorModel.Contains
      (CertifiedTaylorModel.inflate a (1 / 10 ^ 15) (by norm_num)) (Complex.log (1 + z)) :=
  CertifiedTaylorModel.contains_inflate (by norm_num) ha (by
    convert log_series_error hz using 1 <;> norm_num)

end Reinmann.FiniteBandBounds
