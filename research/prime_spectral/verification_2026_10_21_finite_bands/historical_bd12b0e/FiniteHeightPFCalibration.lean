/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.XiHadamardProduct

/-! Conditional finite-height calibration. This does not certify a new rectangle.
Zeros on the critical line are allowed in the height band. -/
namespace Reinmann.FiniteHeightPFCalibration
open Real

/-- Every strip zero up to height T lies in a strip of half-width delta. -/
def LowHeightWidth (delta T : ℝ) : Prop :=
  ∀ s : ℂ, IsCriticalStripZero s → |s.im| ≤ T → |s.re - 1 / 2| ≤ delta

theorem angleBound_of_two_bands {delta T gamma : ℝ} {m : ℕ}
    (hm : 0 < m) (hgamma : 0 < gamma) (hT : 0 ≤ T)
    (hlow : ZetaNoLowStripZero gamma) (hband : LowHeightWidth delta T)
    (hnear : delta ≤ gamma * pfHalfAngle m)
    (hfar : (1 / 2 : ℝ) ≤ T * pfHalfAngle m) : XiFoldedZeroAngleBound m := by
  intro s hs
  have htheta := pfHalfAngle_pos m
  have htan : pfHalfAngle m ≤ tan (pfHalfAngle m) :=
    (lt_tan htheta (pfHalfAngle_lt_half_pi hm)).le
  by_cases ht : |s.im| ≤ T
  · have hi := hlow s hs
    exact (hband s hs ht).trans (hnear.trans
      (mul_le_mul hi htan htheta.le (hgamma.le.trans hi)))
  · have hi : T ≤ |s.im| := (lt_of_not_ge ht).le
    exact (abs_re_sub_half_le_half hs).trans (hfar.trans
      (mul_le_mul hi htan htheta.le (hT.trans hi)))

/-- A half-width 9/40 up to height 32 suffices, given the first-zero bound 14.1.
The width hypothesis is an explicit remaining certificate obligation. -/
theorem finitePF97_of_low_height_width
    (hlow : ZetaNoLowStripZero (141 / 10))
    (hband : LowHeightWidth (9 / 40) 32) : FinitePF XiMomentCoeff 97 := by
  apply XiHadamardProduct.katkovaSectorBridge 97 (by norm_num)
  apply angleBound_of_two_bands (m := 97) (gamma := 141 / 10)
    (delta := 9 / 40) (T := 32) (by norm_num) (by norm_num) (by norm_num) hlow hband
  · unfold pfHalfAngle
    have := pi_gt_d4
    norm_num
    linarith
  · unfold pfHalfAngle
    have := pi_gt_d4
    norm_num
    linarith

end Reinmann.FiniteHeightPFCalibration
