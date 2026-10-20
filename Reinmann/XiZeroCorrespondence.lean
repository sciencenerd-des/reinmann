/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.XiGenusZeroSector
import Reinmann.XiDividedDifference

/-! The zeros of actual entire Xi, and hence folded Xi, correspond to zeta
zeros in the open critical strip. No RH or simple-zero assumption is used. -/
noncomputable section
namespace Reinmann.XiZeroCorrespondence
open Complex

/-- The endpoint value at 1 and classical zeta nonvanishing include the line Re=1. -/
theorem xi_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : xiCompleted s ≠ 0 := by
  by_cases h1 : s = 1
  · subst s
    norm_num
  have h0 : s ≠ 0 := by
    intro h
    norm_num [h] at hs
  have hLambda : completedRiemannZeta s ≠ 0 := by
    intro h
    apply riemannZeta_ne_zero_of_one_le_re hs
    rw [riemannZeta_def_of_ne_zero h0, h, zero_div]
  rw [xiCompleted_eq_product h0 h1]
  exact mul_ne_zero (div_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h1)) (by norm_num)) hLambda

/-- The functional equation transfers right-half-plane nonvanishing to Re≤0. -/
theorem xi_ne_zero_of_re_nonpos {s : ℂ} (hs : s.re ≤ 0) : xiCompleted s ≠ 0 := by
  rw [← XiDividedDifference.xi_one_sub s]
  apply xi_ne_zero_of_one_le_re
  simp only [Complex.sub_re, Complex.one_re]
  linarith

/-- Actual entire Xi has exactly the zeta zeros in the open critical strip. -/
theorem xi_zero_iff {s : ℂ} : xiCompleted s = 0 ↔ IsCriticalStripZero s := by
  constructor
  · intro hz
    have hpos : 0 < s.re := lt_of_not_ge (fun h => xi_ne_zero_of_re_nonpos h hz)
    have hlt : s.re < 1 := lt_of_not_ge (fun h => xi_ne_zero_of_one_le_re h hz)
    have h0 : s ≠ 0 := by simpa using ne_neg_nat_of_re_pos hpos 0
    have h1 : s ≠ 1 := ne_one_of_re_lt_one hlt
    have hp := hz
    rw [xiCompleted_eq_product h0 h1] at hp
    have hLambda : completedRiemannZeta s = 0 :=
      (mul_eq_zero.mp hp).resolve_left
        (div_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h1)) (by norm_num))
    exact ⟨by rw [riemannZeta_def_of_ne_zero h0, hLambda, zero_div], hpos, hlt⟩
  · rintro ⟨hz, hpos, hlt⟩
    have h0 : s ≠ 0 := by simpa using ne_neg_nat_of_re_pos hpos 0
    have h1 : s ≠ 1 := ne_one_of_re_lt_one hlt
    have hGamma := Gammaℝ_ne_zero_of_re_pos hpos
    rw [riemannZeta_def_of_ne_zero h0] at hz
    have hLambda : completedRiemannZeta s = 0 := (div_eq_zero_iff.mp hz).resolve_right hGamma
    rw [xiCompleted_eq_product h0 h1, hLambda, mul_zero]

/-- The chosen square root of a folded zero gives an actual strip zero. -/
theorem folded_zero_strip {z : ℂ} (hz : foldedXi z = 0) :
    IsCriticalStripZero (1 / 2 + Complex.sqrt z) := by
  apply xi_zero_iff.mp
  rwa [← foldedXi_eq_sqrt]

/-- Every folded zero, including its exact coordinate, comes from a strip zero. -/
theorem folded_zero_iff {z : ℂ} : foldedXi z = 0 ↔
    ∃ s : ℂ, IsCriticalStripZero s ∧ z = (s - 1 / 2) ^ 2 := by
  constructor
  · intro hz
    refine ⟨1 / 2 + Complex.sqrt z, folded_zero_strip hz, ?_⟩
    simpa using (complex_sqrt_sq z).symm
  · rintro ⟨s, hs, rfl⟩
    rw [foldedXi_sq]
    change xiCompleted (1 / 2 + (s - 1 / 2)) = 0
    simpa using xi_zero_iff.mpr hs

end Reinmann.XiZeroCorrespondence
