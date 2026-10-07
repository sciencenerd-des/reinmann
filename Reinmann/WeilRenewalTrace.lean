/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.WeilBoundaryActivation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Normed.Group.Continuity

/-!
# Integral algebra for the proposed renewal endpoint trace

The weighted integral estimate below is proved. The Green representation,
renewal density, cutoff commutator, and actual Weil eigenfunction transfer
are written analysis, not theorems asserted by this module. Named inputs
are explicit structure fields rather than axioms or proof placeholders.
-/
noncomputable section
open MeasureTheory Filter Topology
namespace Reinmann.WeilRenewalTrace

/-- A positive weighted average inherits a uniform error, with actual
Bochner integrability obligations. This lemma is for real-valued data. -/
theorem weighted_average_error {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (w H : α → ℝ) (b ε : ℝ)
    (hw : Integrable w μ) (hwH : Integrable (fun s => w s * H s) μ)
    (hw₀ : ∀ᵐ s ∂μ, 0 ≤ w s) (hm : 0 < ∫ s, w s ∂μ)
    (herr : ∀ᵐ s ∂μ, |H s - b| ≤ ε) :
    |(∫ s, w s * H s ∂μ) / (∫ s, w s ∂μ) - b| ≤ ε := by
  have hi : Integrable (fun s => w s * (H s - b)) μ := by
    simpa only [mul_sub] using hwH.sub (hw.mul_const b)
  have hid : (∫ s, w s * (H s - b) ∂μ) =
      (∫ s, w s * H s ∂μ) - (∫ s, w s ∂μ) * b := by
    simp_rw [mul_sub]
    rw [integral_sub hwH (hw.mul_const b), integral_mul_const]
  have hbound : |∫ s, w s * (H s - b) ∂μ| ≤ (∫ s, w s ∂μ) * ε := by
    calc
      _ ≤ ∫ s, |w s * (H s - b)| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ s, w s * ε ∂μ := by
        apply integral_mono_ae hi.abs (hw.mul_const ε)
        filter_upwards [hw₀, herr] with s hs he
        rw [abs_mul, abs_of_nonneg hs]
        exact mul_le_mul_of_nonneg_left he hs
      _ = _ := integral_mul_const ε w
  have hquot : (∫ s, w s * H s ∂μ) / (∫ s, w s ∂μ) - b =
      (∫ s, w s * (H s - b) ∂μ) / (∫ s, w s ∂μ) := by
    rw [hid]
    field_simp
  rw [hquot, abs_div, abs_of_pos hm]
  exact (div_le_iff₀ hm).mpr (by simpa [mul_comm] using hbound)

/-- Analytic inputs needed for the normalized renewal convolution estimate.
For the written application, μ x is Lebesgue measure restricted to (0,x),
weight x s is v(x-s), and H is the inner forcing convolution. None of
these identifications is assumed implicitly. -/
structure RenewalTraceRepresentationHypothesis {α : Type*} [MeasurableSpace α]
    (μ : ℝ → Measure α) (weight H : ℝ → α → ℝ)
    (profile mass : ℝ → ℝ) (trace M r : ℝ) : Prop where
  radius_pos : 0 < r
  mass_pos : ∀ x, 0 < x → x < r → 0 < mass x
  weight_integrable : ∀ x, 0 < x → x < r → Integrable (weight x) (μ x)
  weighted_inner_integrable : ∀ x, 0 < x → x < r →
    Integrable (fun s => weight x s * H x s) (μ x)
  weight_nonneg : ∀ x, 0 < x → x < r → ∀ᵐ s ∂μ x, 0 ≤ weight x s
  mass_identity : ∀ x, 0 < x → x < r → (∫ s, weight x s ∂μ x) = mass x
  representation : ∀ x, 0 < x → x < r →
    profile x = ∫ s, weight x s * H x s ∂μ x
  inner_error : ∀ x, 0 < x → x < r →
    ∀ᵐ s ∂μ x, |H x s - trace| ≤ 2 * M * mass x

theorem renewal_trace_error {α : Type*} [MeasurableSpace α]
    {μ : ℝ → Measure α} {weight H : ℝ → α → ℝ}
    {profile mass : ℝ → ℝ} {trace M r : ℝ}
    (h : RenewalTraceRepresentationHypothesis μ weight H profile mass trace M r)
    {x : ℝ} (hx : 0 < x) (hxr : x < r) :
    |profile x / mass x - trace| ≤ 2 * M * mass x := by
  have hm := h.mass_identity x hx hxr
  have hp : 0 < ∫ s, weight x s ∂μ x := by rw [hm]; exact h.mass_pos x hx hxr
  have he := weighted_average_error (μ x) (weight x) (H x) trace (2 * M * mass x)
    (h.weight_integrable x hx hxr) (h.weighted_inner_integrable x hx hxr)
    (h.weight_nonneg x hx hxr) hp (h.inner_error x hx hxr)
  rwa [hm, ← h.representation x hx hxr] at he

/-- A vanishing renewal mass turns the quantitative bound into a trace limit.
The actual renewal mass asymptotic remains an analytic input. -/
theorem trace_limit_of_error {ι : Type*} {l : Filter ι}
    {profile mass : ι → ℝ} {trace C : ℝ}
    (hm : Tendsto mass l (𝓝 0))
    (he : ∀ᶠ x in l, |profile x / mass x - trace| ≤ C * mass x) :
    Tendsto (fun x => profile x / mass x) l (𝓝 trace) := by
  have hzero : Tendsto (fun x => |profile x / mass x - trace|) l (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall (fun x => abs_nonneg _)) he
      (by simpa using hm.const_mul C)
  exact tendsto_iff_dist_tendsto_zero.mpr (by simpa [Real.dist_eq] using hzero)

end Reinmann.WeilRenewalTrace
