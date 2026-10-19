/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.CertifiedTaylorComposition
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.SpecificLimits.Normed

/-! Derivative bounds from eight nonconstant ordinary coefficients and a proved
unit-circle coefficient majorant. This rule does not assume a zero-free region. -/
noncomputable section
namespace Reinmann.TaylorDerivativeTail
open Finset CertifiedTaylorModel CertifiedTaylorComposition

theorem derivative_bound {f : ℂ → ℂ} (hf : Differentiable ℂ f) {c z : ℂ} {M r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) (hz : ‖z-c‖ ≤ r)
    (hM : ∀ n, ‖coefficient f c n‖ ≤ M) :
    ‖deriv f z‖ ≤
      (∑ n ∈ range 8, ((n+1 : ℕ) : ℝ)*‖coefficient f c (n+1)‖*r^n) +
      M*r^8*(r/(1-r)^2+9/(1-r)) := by
  let t : ℕ → ℂ := fun n => ((n+1 : ℕ) : ℂ)*coefficient f c (n+1)*(z-c)^n
  have hd : Differentiable ℂ (deriv f) := fun w => (hf.analyticAt w).deriv.differentiableAt
  have hs : HasSum t (deriv f z) := by
    convert Complex.hasSum_taylorSeries_of_entire hd c z using 1
    funext n
    dsimp [t]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [← coefficient_deriv]
    simp only [coefficient, smul_eq_mul, div_eq_mul_inv]
    ring
  have htnorm (n : ℕ) : ‖t n‖ =
      ((n+1 : ℕ) : ℝ)*‖coefficient f c (n+1)‖*‖z-c‖^n := by
    simp only [t, norm_mul, norm_pow, Complex.norm_natCast]
  have ht (n : ℕ) : ‖t n‖ ≤ ((n+1 : ℕ) : ℝ)*‖coefficient f c (n+1)‖*r^n := by
    rw [htnorm]
    gcongr
  have hnorm : ‖r‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_pos hr0] using hr1
  have hgeo := hasSum_geometric_of_norm_lt_one hnorm
  have hnat := hasSum_coe_mul_geometric_of_norm_lt_one hnorm
  have hg : HasSum (fun k : ℕ => M*r^8*((k : ℝ)+9)*r^k)
      (M*r^8*(r/(1-r)^2+9/(1-r))) := by
    convert (hnat.add (hgeo.mul_left 9)).mul_left (M*r^8) using 1
    · funext k
      ring
  have htail : HasSum (fun k : ℕ => t (k+8))
      (deriv f z-∑ n ∈ range 8, t n) := (hasSum_nat_add_iff' 8).mpr hs
  have hbound (k : ℕ) : ‖t (k+8)‖ ≤ M*r^8*((k : ℝ)+9)*r^k := by
    calc
      _ ≤ ((k+8+1 : ℕ) : ℝ)*‖coefficient f c (k+8+1)‖*r^(k+8) := ht (k+8)
      _ ≤ ((k+8+1 : ℕ) : ℝ)*M*r^(k+8) := by gcongr; exact hM _
      _ = _ := by rw [pow_add]; push_cast; ring
  have htailnorm := htail.norm_le_of_bounded hg hbound
  have hhead : ‖∑ n ∈ range 8, t n‖ ≤
      ∑ n ∈ range 8, ((n+1 : ℕ) : ℝ)*‖coefficient f c (n+1)‖*r^n :=
    (norm_sum_le _ _).trans (sum_le_sum (fun n _ => ht n))
  calc
    _ = ‖(∑ n ∈ range 8, t n)+(deriv f z-∑ n ∈ range 8, t n)‖ := by congr 1; ring
    _ ≤ ‖∑ n ∈ range 8, t n‖+‖deriv f z-∑ n ∈ range 8, t n‖ := norm_add_le _ _
    _ ≤ _ := add_le_add hhead htailnorm

end Reinmann.TaylorDerivativeTail
