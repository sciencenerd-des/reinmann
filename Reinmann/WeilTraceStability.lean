/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.WeilRenewalTrace
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Explicit trace intervals and convergence gates for two minimizing states

The scalar estimates are proved. Actual endpoint profile intervals, the
renewal representation, and a spectral gap remain named external inputs.
No simplicity theorem at the prime thresholds is asserted here.
-/
noncomputable section
open Filter Topology
namespace Reinmann.WeilTraceStability
open Reinmann.WeilBoundaryActivation

/-- A validated quotient interval and forcing error give a trace interval. -/
theorem trace_enclosure {sample mass trace M lo hi : ℝ}
    (herr : |sample / mass - trace| ≤ 2 * M * mass)
    (hlo : lo ≤ sample / mass) (hhi : sample / mass ≤ hi) :
    lo - 2 * M * mass ≤ trace ∧ trace ≤ hi + 2 * M * mass := by
  obtain ⟨ha, hb⟩ := abs_le.mp herr
  constructor <;> linarith

/-- A phase-invariant distance needs coercivity on the FULL normalized class.
For a simple ground state with spectral gap gamma, the usual Hilbert-space
phase distance satisfies this inequality. Finite matrix gaps do not suffice. -/
def GapCoercivityHypothesis {α : Type*} (Q : α → ℝ) (Eligible : α → Prop)
    (f₀ : α) (eigen₀ gap : ℝ) (distance : α → α → ℝ) : Prop :=
  ∀ f, Eligible f → gap * distance f₀ f ^ 2 ≤ 2 * (Q f - eigen₀)

/-- Statewise prime errors, rather than a small global perturbation norm,
control the distance between the two actual minimizing states. -/
theorem two_minimizer_distance_sq {α : Type*} {Q V : α → ℝ}
    {Eligible : α → Prop} {f₀ f₁ : α} {eigen₀ eigen₁ gap η : ℝ}
    {distance : α → α → ℝ}
    (h₀ : Minimizer Q Eligible f₀ eigen₀)
    (h₁ : Minimizer (fun f => Q f + V f) Eligible f₁ eigen₁)
    (hgap : GapCoercivityHypothesis Q Eligible f₀ eigen₀ gap distance)
    (hg : 0 < gap) (hv₀ : |V f₀| ≤ η) (hv₁ : |V f₁| ≤ η) :
    distance f₀ f₁ ^ 2 ≤ 4 * η / gap := by
  have hco := hgap f₁ h₁.eligible
  obtain ⟨_, hupper⟩ := activation_bracket h₀ h₁
  obtain ⟨hv₀lo, hv₀hi⟩ := abs_le.mp hv₀
  obtain ⟨hv₁lo, hv₁hi⟩ := abs_le.mp hv₁
  apply (le_div_iff₀ hg).mpr
  have hat := h₁.attained
  nlinarith

/-- The explicit ratio error/gap is the convergence gate; no fixed gap
is hidden in this theorem. It also applies to distances from a cluster. -/
theorem distance_tendsto_zero_of_sq_bound {ι : Type*} {l : Filter ι}
    {distance ratio : ι → ℝ}
    (hd : ∀ᶠ x in l, 0 ≤ distance x)
    (hb : ∀ᶠ x in l, distance x ^ 2 ≤ 4 * ratio x)
    (hr : Tendsto ratio l (𝓝 0)) :
    Tendsto distance l (𝓝 0) := by
  have hs : Tendsto (fun x => distance x ^ 2) l (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall (fun x => sq_nonneg _)) hb
      (by simpa using hr.const_mul 4)
  have ha : Tendsto (fun x => |distance x|) l (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hs
  apply ha.congr'
  filter_upwards [hd] with x hx
  exact abs_of_nonneg hx

/-- Actual first and second FULL operator eigenvalues are external inputs.
The Arb certificates and written min--max argument are not imported as axioms. -/
def ThresholdSpectralEnclosureHypothesis (eigen₁ eigen₂ lower₂ upper₁ : ℝ) : Prop :=
  eigen₁ ≤ upper₁ ∧ lower₂ ≤ eigen₂

/-- Weakened rational bounds from the external prime-two certificate. -/
theorem threshold_two_gap {eigen₁ eigen₂ : ℝ}
    (h : ThresholdSpectralEnclosureHypothesis eigen₁ eigen₂
      (999 / 100000) (142 / 100000)) :
    (857 / 100000 : ℝ) ≤ eigen₂ - eigen₁ := by
  obtain ⟨ha, hb⟩ := h
  linarith

/-- Weakened rational bounds from the external prime-three certificate. -/
theorem threshold_three_gap {eigen₁ eigen₂ : ℝ}
    (h : ThresholdSpectralEnclosureHypothesis eigen₁ eigen₂
      (109 / 1000000000) (103 / 1000000000)) :
    (6 / 1000000000 : ℝ) ≤ eigen₂ - eigen₁ := by
  obtain ⟨ha, hb⟩ := h
  linarith

end Reinmann.WeilTraceStability
