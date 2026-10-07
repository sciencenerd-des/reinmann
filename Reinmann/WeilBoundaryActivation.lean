/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Algebra for a proposed boundary-regularity approach to prime activation

These are general inequalities, not a new Weil positivity theorem. In
particular, no Weil eigenfunction boundary estimate, endpoint trace limit,
integral asymptotic, support-uniform estimate, or novelty claim is asserted.
The accompanying research note supplies the written conditional overlap
argument and records the analytic obligations and prior-art collisions.
-/
noncomputable section
namespace Reinmann.WeilBoundaryActivation

/-- An attained global minimum on an explicitly specified normalized class. -/
structure Minimizer {α : Type*} (Q : α → ℝ) (Eligible : α → Prop)
    (f : α) (eigen : ℝ) : Prop where
  eligible : Eligible f
  attained : Q f = eigen
  minimizing : ∀ g, Eligible g → eigen ≤ Q g

/-- Only the two actual minimizers are evaluated; no operator-norm bound on V. -/
theorem activation_bracket {α : Type*} {Q V : α → ℝ}
    {Eligible : α → Prop} {f₀ f₁ : α} {eigen₀ eigen₁ : ℝ}
    (h₀ : Minimizer Q Eligible f₀ eigen₀)
    (h₁ : Minimizer (fun f => Q f + V f) Eligible f₁ eigen₁) :
    eigen₀ + V f₁ ≤ eigen₁ ∧ eigen₁ ≤ eigen₀ + V f₀ := by
  constructor
  · calc
      eigen₀ + V f₁ ≤ Q f₁ + V f₁ := by linarith [h₀.minimizing f₁ h₁.eligible]
      _ = eigen₁ := h₁.attained
  · calc
      eigen₁ ≤ Q f₀ + V f₀ := h₁.minimizing f₀ h₀.eligible
      _ = eigen₀ + V f₀ := by rw [h₀.attained]

/-- A shared activation coefficient transfers through variational bracketing.
Boundary control must hold for BOTH actual minimizers. -/
theorem activation_coefficient_error {α : Type*} {Q V : α → ℝ}
    {Eligible : α → Prop} {f₀ f₁ : α} {eigen₀ eigen₁ v η : ℝ}
    (h₀ : Minimizer Q Eligible f₀ eigen₀)
    (h₁ : Minimizer (fun f => Q f + V f) Eligible f₁ eigen₁)
    (hv₀ : |V f₀ - v| ≤ η) (hv₁ : |V f₁ - v| ≤ η) :
    |eigen₁ - eigen₀ - v| ≤ η := by
  obtain ⟨hlo, hhi⟩ := activation_bracket h₀ h₁
  obtain ⟨hv₀lo, hv₀hi⟩ := abs_le.mp hv₀
  obtain ⟨hv₁lo, hv₁hi⟩ := abs_le.mp hv₁
  apply abs_le.mpr
  constructor <;> linarith

/-- The absolute variant does not require a common nonzero coefficient. -/
theorem activation_absolute_bound {α : Type*} {Q V : α → ℝ}
    {Eligible : α → Prop} {f₀ f₁ : α} {eigen₀ eigen₁ η : ℝ}
    (h₀ : Minimizer Q Eligible f₀ eigen₀)
    (h₁ : Minimizer (fun f => Q f + V f) Eligible f₁ eigen₁)
    (hv₀ : |V f₀| ≤ η) (hv₁ : |V f₁| ≤ η) :
    |eigen₁ - eigen₀| ≤ η := by
  simpa using activation_coefficient_error (v := 0) h₀ h₁
    (by simpa using hv₀) (by simpa using hv₁)

/-- Pointwise bounds for the elementary logarithmic boundary model kernel. -/
theorem reciprocal_sqrt_bounds (L u v : ℝ) (hL : 0 < L)
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    2 / (2 * L + u + v) ≤ 1 / Real.sqrt ((L + u) * (L + v)) ∧
      1 / Real.sqrt ((L + u) * (L + v)) ≤ 1 / L := by
  have hA : 0 < (L + u) * (L + v) := mul_pos (by linarith) (by linarith)
  have hr : 0 < Real.sqrt ((L + u) * (L + v)) := Real.sqrt_pos.2 hA
  have hs : 0 < 2 * L + u + v := by linarith
  have hsq := Real.sq_sqrt hA.le
  have hsmall : L ≤ Real.sqrt ((L + u) * (L + v)) := by
    nlinarith [mul_nonneg hu hv, mul_nonneg hL.le hu, mul_nonneg hL.le hv]
  have hlarge : 2 * Real.sqrt ((L + u) * (L + v)) ≤ 2 * L + u + v := by
    nlinarith [sq_nonneg (u - v)]
  constructor
  · exact (div_le_div_iff₀ hs hr).mpr (by nlinarith)
  · exact one_div_le_one_div_of_le hL hsmall

/-- Rate implied by the written integral bounds 1/(L+1) ≤ J(L) ≤ 1/L.
This theorem takes those bounds as inputs; it does not formalize the integral. -/
theorem normalized_kernel_error (L J : ℝ) (hL : 0 < L)
    (hlo : 1 / (L + 1) ≤ J) (hhi : J ≤ 1 / L) :
    0 ≤ 1 - L * J ∧ 1 - L * J ≤ 1 / (L + 1) := by
  have hup : J * L ≤ 1 := (le_div_iff₀ hL).mp hhi
  have hdown : 1 ≤ J * (L + 1) := (div_le_iff₀ (by linarith : 0 < L + 1)).mp hlo
  constructor
  · linarith
  · apply (le_div_iff₀ (by linarith : 0 < L + 1)).mpr
    nlinarith

def activationScale (δ : ℝ) : ℝ := δ / Real.log (1 / δ)

theorem activationScale_pos {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ < 1) :
    0 < activationScale δ := by
  apply div_pos hδ
  apply Real.log_pos
  exact (lt_div_iff₀ hδ).mpr (by simpa using hδ₁)

/-- Elementary geometric-series error used in the comparison-kernel estimate. -/
theorem geometric_exponential_error (y : ℝ) (hy : 0 < y) :
    0 ≤ Real.exp y / (Real.exp y - 1) - 1 / y ∧
      Real.exp y / (Real.exp y - 1) - 1 / y ≤ 1 := by
  have he : 0 < Real.exp y := Real.exp_pos y
  have he₁ : 1 < Real.exp y := Real.one_lt_exp_iff.mpr hy
  have hd : 0 < Real.exp y - 1 := by linarith
  have hplus := Real.add_one_le_exp y
  have hminus := Real.add_one_le_exp (-y)
  have hprod : (1 - y) * Real.exp y ≤ 1 := by
    calc
      (1 - y) * Real.exp y ≤ Real.exp (-y) * Real.exp y := by
        exact mul_le_mul_of_nonneg_right (by linarith) he.le
      _ = 1 := by rw [← Real.exp_add]; simp
  constructor
  · have hfrac : 1 / y ≤ Real.exp y / (Real.exp y - 1) := by
      apply (div_le_div_iff₀ hy hd).mpr
      nlinarith
    linarith
  · have hfrac : 1 / (Real.exp y - 1) ≤ 1 / y :=
      one_div_le_one_div_of_le hy (by linarith)
    have hid : Real.exp y / (Real.exp y - 1) - 1 / y =
        1 + 1 / (Real.exp y - 1) - 1 / y := by
      field_simp
      ring
    rw [hid]
    linarith

/-- Bound for the positive expression equal to the absolute archimedean
remainder kernel at x>0. The Fourier/kernel identification is written analysis. -/
theorem archimedean_remainder_allowance (x : ℝ) (hx : 0 < x) :
    0 ≤ Real.exp (-x / 2) *
      (Real.exp (2 * x) / (Real.exp (2 * x) - 1) - 1 / (2 * x) +
        (1 - Real.exp (-x / 2)) / (2 * x)) ∧
    Real.exp (-x / 2) *
      (Real.exp (2 * x) / (Real.exp (2 * x) - 1) - 1 / (2 * x) +
        (1 - Real.exp (-x / 2)) / (2 * x)) ≤ 5 / 4 := by
  have h2x : 0 < 2 * x := by linarith
  obtain ⟨hAlo, hAhi⟩ := geometric_exponential_error (2 * x) h2x
  have he : 0 < Real.exp (-x / 2) := Real.exp_pos _
  have he₁ : Real.exp (-x / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hBlo : 0 ≤ (1 - Real.exp (-x / 2)) / (2 * x) :=
    div_nonneg (by linarith) h2x.le
  have hBhi : (1 - Real.exp (-x / 2)) / (2 * x) ≤ 1 / 4 := by
    apply (div_le_iff₀ h2x).mpr
    linarith [Real.add_one_le_exp (-x / 2)]
  constructor
  · exact mul_nonneg he.le (add_nonneg hAlo hBlo)
  · calc
      _ ≤ 1 * (Real.exp (2 * x) / (Real.exp (2 * x) - 1) - 1 / (2 * x) +
          (1 - Real.exp (-x / 2)) / (2 * x)) :=
        mul_le_mul_of_nonneg_right he₁ (add_nonneg hAlo hBlo)
      _ ≤ 5 / 4 := by linarith

end Reinmann.WeilBoundaryActivation
