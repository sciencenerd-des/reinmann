/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.XiLocalCauchy
import Reinmann.XiFiniteTheta
import Reinmann.EnclosureRules
import Mathlib.Analysis.Complex.ExponentialBounds

/-! A deliberately coarse first evaluator certificate at the genuine centre 1/2.
It retains one theta term on [1,4], encloses the exp/log midpoint evaluation,
and includes quadrature variation, the omitted theta terms and the infinite
Mellin tail. This is one tile, not a zero-free rectangle certificate. -/
noncomputable section
namespace Reinmann.XiFirstTile
open Set MeasureTheory HurwitzZeta Metric

private theorem exp_neg_nat_le (n : ℕ) :
    Real.exp (-(n : ℝ)) ≤ (1 / 2 : ℝ) ^ n := by
  have h : Real.exp (-1) ≤ (1 / 2 : ℝ) := by
    rw [Real.exp_neg, ← one_div]
    apply (div_le_iff₀ (Real.exp_pos 1)).mpr
    linarith [Real.exp_one_gt_two]
  have he : Real.exp (-(n : ℝ)) = Real.exp (-1) ^ n := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [he]
  exact pow_le_pow_left₀ (Real.exp_pos _).le h n

def finiteIntegrand (t : ℝ) : ℂ :=
  ((2 * Real.exp (-Real.pi * t) * Real.exp (Real.log t * (-3 / 4)) : ℝ) : ℂ)

/-- The actual one-term theta/Mellin integrand, including its real-power branch. -/
theorem finiteIntegrand_eq {t : ℝ} (ht : 0 < t) :
    finiteIntegrand t = (t : ℂ) ^ ((1 / 4 : ℂ) - 1) • (thetaFinite 1 t : ℂ) := by
  have hc := Complex.ofReal_cpow ht.le (-3 / 4 : ℝ)
  rw [Real.rpow_def_of_pos ht] at hc
  have hc' : ((Real.exp (Real.log t * (-3 / 4)) : ℝ) : ℂ) = (t : ℂ) ^ (-3 / 4 : ℂ) := by
    convert hc using 1 <;> norm_num
  clear hc
  simp only [finiteIntegrand, thetaFinite, Finset.sum_range_one, Nat.cast_zero,
    zero_add, one_pow, mul_one, smul_eq_mul]
  rw [show (1 / 4 : ℂ) - 1 = -3 / 4 by norm_num, ← hc']
  push_cast
  ring

/-- Every value in the quadrature panel is enclosed, not just its midpoint. -/
theorem finiteIntegrand_bound {t : ℝ} (ht : 1 ≤ t) :
    ‖finiteIntegrand t‖ ≤ 1 / 4 := by
  have hlog : 0 ≤ Real.log t := Real.log_nonneg ht
  have hw : Real.exp (Real.log t * (-3 / 4)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith
  have he : Real.exp (-Real.pi * t) ≤ (1 / 8 : ℝ) := by
    apply (Real.exp_le_exp.mpr (show - Real.pi * t ≤ -(3 : ℝ) by
      nlinarith [Real.pi_gt_three])).trans
    convert exp_neg_nat_le 3 using 1 <;> norm_num
  simp only [finiteIntegrand, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity)]
  nlinarith [Real.exp_pos (-Real.pi * t), Real.exp_pos (Real.log t * (-3 / 4))]

/-- Proved exp/log sample enclosure for the panel midpoint 5/2. -/
theorem midpoint_sample : ‖finiteIntegrand (5 / 2) - (1 / 100 : ℂ)‖ ≤ 13 / 50 := by
  calc
    _ ≤ ‖finiteIntegrand (5 / 2)‖ + ‖(1 / 100 : ℂ)‖ := norm_sub_le _ _
    _ ≤ 1 / 4 + 1 / 100 := by
      exact add_le_add (finiteIntegrand_bound (by norm_num)) (by norm_num)
    _ = _ := by norm_num

theorem finiteIntegrand_integrable : IntervalIntegrable finiteIntegrand volume 1 4 := by
  have hl : ContinuousOn Real.log (uIcc (1 : ℝ) 4) := by
    apply Real.continuousOn_log.mono
    intro t ht
    rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 4)] at ht
    exact ne_of_gt (by linarith [ht.1])
  apply ContinuousOn.intervalIntegrable
  apply Complex.continuous_ofReal.comp_continuousOn
  apply ContinuousOn.mul
  · exact continuousOn_const.mul (Real.continuous_exp.comp_continuousOn
      (continuousOn_const.mul continuousOn_id))
  · exact Real.continuous_exp.comp_continuousOn (hl.mul_const _)

/-- A one-panel enclosure rule with explicit variation on all of [1,4]. -/
theorem finite_quadrature :
    ‖(∫ t in (1 : ℝ)..4, finiteIntegrand t) - (3 / 100 : ℂ)‖ ≤ 39 / 50 := by
  have h := EnclosureRules.integral_tile_error finiteIntegrand_integrable
    (v := (1 / 100 : ℂ)) (ε := 13 / 50) (by
      intro t ht
      rw [uIoc_of_le (by norm_num : (1 : ℝ) ≤ 4)] at ht
      calc
        _ ≤ ‖finiteIntegrand t‖ + ‖(1 / 100 : ℂ)‖ := norm_sub_le _ _
        _ ≤ 1 / 4 + 1 / 100 := add_le_add (finiteIntegrand_bound ht.1.le) (by norm_num)
        _ = _ := by norm_num)
  norm_num at h ⊢
  exact h

private def upperIntegrand (t : ℝ) : ℂ :=
  (t : ℂ) ^ ((1 / 4 : ℂ) - 1) • thetaCenterUpper t

private theorem upper_integrable : IntervalIntegrable upperIntegrand volume 1 4 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (1 : ℝ) ≤ 4)]
  exact (thetaCenterUpper_mellinConvergent (1 / 4 : ℂ)).mono_set
    (by intro t ht; exact lt_trans (by norm_num) ht.1)

/-- Exact decomposition of the genuine Mellin transform, with its actual tail. -/
private theorem mellin_split : mellin thetaCenterUpper (1 / 4) =
    (∫ t in (1 : ℝ)..4, upperIntegrand t) + thetaUpperMellinRemainder 4 (1 / 4) := by
  have hf : IntegrableOn upperIntegrand (Ioi 0) := thetaCenterUpper_mellinConvergent _
  have h := setIntegral_union (Ioc_disjoint_Ioi_same : Disjoint (Ioc (1 : ℝ) 4) (Ioi 4))
    measurableSet_Ioi (hf.mono_set (by intro t ht; exact lt_trans (by norm_num) ht.1))
    (hf.mono_set (by intro t ht; exact lt_trans (by norm_num : (0 : ℝ) < 4) ht))
  rw [Ioc_union_Ioi_eq_Ioi (by norm_num : (1 : ℝ) ≤ 4)] at h
  rw [intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 4)]
  change mellin thetaCenterUpper (1 / 4) = _ + ∫ t in Ioi (4 : ℝ), upperIntegrand t
  rw [thetaCenterUpper_mellin_eq_integral]
  convert h using 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp [upperIntegrand]
  have hu : thetaCenterUpper t = (hurwitzEvenFEPair 0).f_modif t := by
    simp [thetaCenterUpper, ht]
  rw [hu]

private theorem theta_error :
    ‖(∫ t in (1 : ℝ)..4, upperIntegrand t) - (∫ t in (1 : ℝ)..4, finiteIntegrand t)‖ ≤ 3 / 1024 := by
  rw [← intervalIntegral.integral_sub upper_integrable finiteIntegrand_integrable]
  have h := thetaFinite_integrated_error_le (T := 4) (by norm_num) 1
    (s := (1 / 4 : ℂ)) (by norm_num)
  have heq : (∫ t in (1 : ℝ)..4, upperIntegrand t - finiteIntegrand t) =
      ∫ t in (1 : ℝ)..4, (t : ℂ) ^ ((1 / 4 : ℂ) - 1) •
        ((cosKernel 0 t - 1 - thetaFinite 1 t : ℝ) : ℂ) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [] with t ht
    rw [uIoc_of_le (by norm_num : (1 : ℝ) ≤ 4)] at ht
    dsimp [upperIntegrand]
    rw [thetaCenterUpper_eq ht.1, finiteIntegrand_eq (by linarith [ht.1]),
      smul_eq_mul, Complex.ofReal_sub]
    push_cast
    ring
  rw [heq]
  apply h.trans
  have he : Real.exp (-Real.pi * (1 + 1 : ℝ) ^ 2) ≤ 1 / 4096 := by
    apply (Real.exp_le_exp.mpr (show - Real.pi * (1 + 1 : ℝ) ^ 2 ≤ -(12 : ℝ) by
      nlinarith [Real.pi_gt_three])).trans
    convert exp_neg_nat_le 12 using 1 <;> norm_num
  norm_num at he ⊢
  linarith

/-- A complete centre enclosure: theta cutoff, quadrature, sample, and Mellin tail. -/
theorem centre_enclosure :
    ‖xiCompleted (1 / 2) - (397 / 800 : ℂ)‖ ≤ 3 / 20 := by
  have htail := thetaUpperMellinRemainder_norm_le (T := 4) (s := (1 / 4 : ℂ))
    (by norm_num) (by norm_num)
  have he : Real.exp (-4) ≤ (1 / 16 : ℝ) := by convert exp_neg_nat_le 4 using 1 <;> norm_num
  have hM : ‖mellin thetaCenterUpper (1 / 4) - (3 / 100 : ℂ)‖ ≤
      3 / 1024 + 39 / 50 + 1 / 4 := by
    rw [mellin_split]
    calc
      _ = ‖((∫ t in (1 : ℝ)..4, upperIntegrand t) - (∫ t in (1 : ℝ)..4, finiteIntegrand t)) + ((∫ t in (1 : ℝ)..4, finiteIntegrand t) - (3 / 100 : ℂ)) + thetaUpperMellinRemainder 4 (1 / 4)‖ := by congr 1; ring
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add theta_error finite_quadrature)) le_rfl)
      _ ≤ _ := by linarith
  have hid : xiCompleted (1 / 2) - (397 / 800 : ℂ) =
      -(1 / 8 : ℂ) * (mellin thetaCenterUpper (1 / 4) - (3 / 100 : ℂ)) := by
    unfold xiCompleted
    rw [completedRiemannZeta₀_center_eq_mellin]
    ring
  rw [hid, norm_mul]
  norm_num only [norm_neg, norm_div, norm_one, Complex.norm_ofNat]
  linarith

/-- A local derivative bound on the small bottom tile, from actual Xi. -/
theorem local_derivative {w : ℂ} (hw : ‖w - (1 / 2 : ℂ)‖ ≤ 1 / 4) :
    ‖deriv xiCompleted w‖ ≤ 10 := by
  have hb (z : ℂ) (hz : z ∈ sphere w (1 / 2)) : ‖xiCompleted z‖ ≤ 5 := by
    have hd : ‖z - w‖ = 1 / 2 := mem_sphere_iff_norm.mp hz
    have hdc : ‖z - (1 / 2 : ℂ)‖ ≤ 3 / 4 := by
      calc
        _ = ‖(z - w) + (w - (1 / 2 : ℂ))‖ := by congr 1; ring
        _ ≤ ‖z - w‖ + ‖w - (1 / 2 : ℂ)‖ := norm_add_le _ _
        _ ≤ _ := by rw [hd]; linarith
    have hr : |z.re - 1 / 2| ≤ 3 / 4 := by
      simpa using (Complex.abs_re_le_norm (z - (1 / 2 : ℂ))).trans hdc
    have hrs := abs_le.mp hr
    have hn : ‖z‖ ≤ 3 / 2 := by
      calc
        _ = ‖(z - (1 / 2 : ℂ)) + (1 / 2 : ℂ)‖ := by congr 1; ring
        _ ≤ ‖z - (1 / 2 : ℂ)‖ + ‖(1 / 2 : ℂ)‖ := norm_add_le _ _
        _ ≤ _ := by norm_num at *; linarith
    have hn1 : ‖z - 1‖ ≤ 3 / 2 := by
      calc
        _ = ‖(z - (1 / 2 : ℂ)) - (1 / 2 : ℂ)‖ := by congr 1; ring
        _ ≤ ‖z - (1 / 2 : ℂ)‖ + ‖(1 / 2 : ℂ)‖ := norm_sub_le _ _
        _ ≤ _ := by norm_num at *; linarith
    have h := XiLocalCauchy.xi_norm_le (z := z) (by linarith) (by linarith)
    have he : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    have hp := mul_le_mul hn hn1 (norm_nonneg (z - 1)) (by norm_num : (0 : ℝ) ≤ 3 / 2)
    have he' := mul_le_mul_of_nonneg_left he
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (mul_nonneg (norm_nonneg z) (norm_nonneg (z - 1))))
    nlinarith
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 1
    (by norm_num : (0 : ℝ) < 1 / 2) differentiable_xiCompleted.diffContOnCl hb
  norm_num at h
  exact h

/-- One actual closed complex tile is certified end to end. This does not
cover the critical rectangle or discharge ZetaNoLowStripZero. -/
theorem first_tile_nonzero {z : ℂ} (hz : ‖z - (1 / 2 : ℂ)‖ ≤ 1 / 100) :
    xiCompleted z ≠ 0 := by
  have hv : ‖xiCompleted z - xiCompleted (1 / 2)‖ ≤ 10 * ‖z - (1 / 2 : ℂ)‖ := by
    apply EnclosureRules.variation_of_deriv (convex_closedBall (1 / 2 : ℂ) (1 / 4))
      (fun w _ => differentiable_xiCompleted w)
      (fun w hw => local_derivative (mem_closedBall_iff_norm.mp hw))
      (by simp)
      (mem_closedBall_iff_norm.mpr (by linarith))
  exact EnclosureRules.tile_nonzero (by norm_num) centre_enclosure hz hv
    (by norm_num : (3 / 20 : ℝ) + 10 * (1 / 100) < ‖(397 / 800 : ℂ)‖)

end Reinmann.XiFirstTile
