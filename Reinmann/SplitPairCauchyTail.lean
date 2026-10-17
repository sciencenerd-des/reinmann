/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Cauchy bounds for the analytic remainder after finitely many poles are removed.
The analytic remainder must be constructed separately; this module does not
assume its coefficient decay, nor assert a genus-zero factorization theorem. -/
noncomputable section
namespace Reinmann.SplitPairCauchyTail
open Metric Filter

/-- Ordinary Taylor coefficients, with the factorial divided out. -/
def coefficient (g : ℂ → ℂ) (n : ℕ) : ℂ :=
  iteratedDeriv n g 0 / (n.factorial : ℂ)

/-- These are the coefficients of the actual analytic function. -/
theorem coefficient_hasSum {g : ℂ → ℂ} {R : ℝ}
    (hg : DifferentiableOn ℂ g (ball 0 R)) {z : ℂ} (hz : z ∈ ball 0 R) :
    HasSum (fun n => coefficient g n * z^n) (g z) := by
  have h := Complex.hasSum_taylorSeries_on_ball hg hz
  simpa only [coefficient, sub_zero, smul_eq_mul, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc] using h

/-- An actual circle bound proves the coefficient tail bound. -/
theorem coefficient_norm_le {g : ℂ → ℂ} {R C : ℝ} (hR : 0 < R)
    (hg : DiffContOnCl ℂ g (ball 0 R))
    (hC : ∀ z ∈ sphere 0 R, ‖g z‖ ≤ C) (n : ℕ) :
    ‖coefficient g n‖ ≤ C / R^n := by
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR hg hC
  have hn : 0 < (n.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
  unfold coefficient
  rw [norm_div, Complex.norm_natCast]
  calc
    ‖iteratedDeriv n g 0‖ / (n.factorial : ℝ) ≤
        ((n.factorial : ℝ)*C/R^n)/(n.factorial : ℝ) :=
      div_le_div_of_nonneg_right h hn.le
    _ = C/R^n := by field_simp <;> ring

/-- Exponentially decaying coefficient errors in any smaller normalization radius. -/
theorem normalized_coefficient_norm_le {g : ℂ → ℂ} {R C : ℝ} (hR : 0 < R)
    (hg : DiffContOnCl ℂ g (ball 0 R))
    (hC : ∀ z ∈ sphere 0 R, ‖g z‖ ≤ C) (d : ℂ) (n : ℕ) :
    ‖coefficient g n * d^n‖ ≤ C * (‖d‖/R)^n := by
  rw [norm_mul, norm_pow]
  calc
    ‖coefficient g n‖ * ‖d‖^n ≤ (C/R^n)*‖d‖^n :=
      mul_le_mul_of_nonneg_right (coefficient_norm_le hR hg hC n) (by positivity)
    _ = _ := by rw [div_pow]; ring

theorem normalized_coefficient_tendsto_zero {g : ℂ → ℂ} {R C : ℝ} (hR : 0 < R)
    (hg : DiffContOnCl ℂ g (ball 0 R))
    (hC : ∀ z ∈ sphere 0 R, ‖g z‖ ≤ C) {d : ℂ} (hd : ‖d‖ < R) :
    Tendsto (fun n => coefficient g n * d^n) atTop (nhds 0) := by
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (div_nonneg (norm_nonneg d) hR.le) ((div_lt_one hR).mpr hd)).const_mul C
  apply squeeze_zero_norm (fun n => normalized_coefficient_norm_le hR hg hC d n)
  simpa only [mul_zero] using ht

/-- The finite-pole coefficient decomposition produces a proved Cauchy tail;
an asymptotic remainder bound is not an input. -/
theorem finite_pole_coefficient_error {ι : Type*} [Fintype ι]
    {h : ℕ → ℂ} {c z : ι → ℂ} {g : ℂ → ℂ} {R C : ℝ}
    (heq : ∀ n, h n = (∑ i, c i * z i^n) + coefficient g n)
    (hR : 0 < R) (hg : DiffContOnCl ℂ g (ball 0 R))
    (hC : ∀ w ∈ sphere 0 R, ‖g w‖ ≤ C) (n : ℕ) :
    ‖h n - ∑ i, c i * z i^n‖ ≤ C/R^n := by
  rw [heq, add_sub_cancel_left]
  exact coefficient_norm_le hR hg hC n

/-- Subtracting the principal part at an actual simple zero gives an explicit
analytic germ, constructed from divided differences. No removable remainder
is assumed. Other zeros may still be poles of this germ away from a. -/
theorem simple_pole_analytic_remainder {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {a : ℂ} (ha : F a = 0) (hderiv : deriv F a ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧ ∀ z : ℂ, z ≠ a →
      (F z)⁻¹ - (deriv F a)⁻¹/(z-a) = g z := by
  let D := dslope F a
  have hD : Differentiable ℂ D := by
    have h := (Complex.differentiableOn_dslope
      (by simp : (Set.univ : Set ℂ) ∈ nhds a)).mpr hF.differentiableOn
    exact fun z => h.differentiableAt (by simp)
  let U := {z : ℂ | D z ≠ 0}
  have hUopen : IsOpen U := by
    have hclosed : IsClosed {z : ℂ | D z = 0} :=
      isClosed_eq hD.continuous continuous_const
    exact hclosed.isOpen_compl
  have haU : a ∈ U := by simpa only [U, Set.mem_setOf_eq, D, dslope_same] using hderiv
  have hUa : U ∈ nhds a := hUopen.mem_nhds haU
  let G := fun z => (D z)⁻¹
  have hG : DifferentiableOn ℂ G U := fun z hz =>
    ((hD z).inv hz).differentiableWithinAt
  let g := dslope G a
  have hg : AnalyticAt ℂ g a :=
    ((Complex.differentiableOn_dslope hUa).mpr hG).analyticAt hUa
  refine ⟨g, hg, ?_⟩
  intro z hza
  have hfactor : (z-a)*D z = F z := by
    simpa only [D, smul_eq_mul] using sub_smul_dslope_of_zero ha z
  have hGa : G a = (deriv F a)⁻¹ := by simp only [G, D, dslope_same]
  change (F z)⁻¹ - (deriv F a)⁻¹/(z-a) = dslope G a z
  rw [dslope_of_ne _ hza, slope, hGa, ← hfactor]
  simp only [G, smul_eq_mul, mul_inv_rev, div_eq_mul_inv, vsub_eq_sub]
  ring

end Reinmann.SplitPairCauchyTail
