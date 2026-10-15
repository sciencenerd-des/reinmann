/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.FiniteShiftChains
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Finite-support translation decomposition

Lebesgue translation invariance and adjacent interval partitions identify the
translation form with a finite chain of fibers. Support is an almost-everywhere
condition; endpoint values are retained as separate trace data, not set to zero.
-/
noncomputable section
namespace Reinmann.SupportTranslation
open MeasureTheory Filter Set
open scoped ENNReal
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

omit [InnerProductSpace ℝ H] in
theorem memLp_translate {f : ℝ → H} (hf : MemLp f 2 volume) (d : ℝ) :
    MemLp (fun x => f (x + d)) 2 volume := by
  simpa only [Function.comp_def] using
    hf.comp_measurePreserving (measurePreserving_add_right volume d)

omit [InnerProductSpace ℝ H] in
theorem integrable_energy {f : ℝ → H} (hf : MemLp f 2 volume) :
    Integrable (fun x => ‖f x‖ ^ 2) volume := hf.norm.integrable_sq

theorem integrable_real_inner {f g : ℝ → H} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) : Integrable (fun x => inner ℝ (f x) (g x)) volume := by
  have hi := L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)
  apply hi.congr
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  rw [hx, hy]

omit [InnerProductSpace ℝ H] in
/-- No value at the left endpoint is imposed: it is discarded only inside
Lebesgue integrals, by the proved no-atoms property. -/
theorem ae_support_Ioc_of_Icc {f : ℝ → H} {L : ℝ}
    (hs : ∀ᵐ x ∂volume, x ∉ Icc 0 L → f x = 0) :
    ∀ᵐ x ∂volume, x ∉ Ioc 0 L → f x = 0 := by
  filter_upwards [hs, volume.ae_ne (0 : ℝ)] with x hx hn hnot
  apply hx
  intro hi
  apply hnot
  exact ⟨lt_of_le_of_ne hi.1 (Ne.symm hn), hi.2⟩

/-- Translation of the base interval produces an exact finite partition.
This lemma is valid for every integrable scalar function and every real step. -/
theorem translated_interval_partition {g : ℝ → ℝ} (hg : Integrable g volume)
    (t : ℝ) (m : ℕ) :
    (∑ k ∈ Finset.range m, ∫ s in (0 : ℝ)..t, g (s + k * t)) =
      ∫ x in (0 : ℝ)..(m * t), g x := by
  have h := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k : ℕ => (k : ℝ) * t) (n := m)
    (fun _ _ => hg.intervalIntegrable)
  have he (k : ℕ) : (∫ s in (0 : ℝ)..t, g (s + k * t)) =
      ∫ x in ((k : ℝ) * t)..((k + 1 : ℕ) * t), g x := by
    rw [intervalIntegral.integral_comp_add_right]
    congr 1 <;> push_cast <;> ring
  simpa only [he, Nat.cast_zero, zero_mul] using h

omit [InnerProductSpace ℝ H] in
/-- Energy disintegration includes the support boundary as an a.e. condition. -/
theorem energy_disintegration {f : ℝ → H} (hf : MemLp f 2 volume)
    {t L : ℝ} (ht : 0 ≤ t) (m : ℕ) (hL : L ≤ m * t)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc 0 L → f x = 0) :
    (∑ k ∈ Finset.range m, ∫ s in (0 : ℝ)..t, ‖f (s + k * t)‖ ^ 2) =
      ∫ x, ‖f x‖ ^ 2 := by
  rw [translated_interval_partition (integrable_energy hf)]
  rw [intervalIntegral.integral_of_le (mul_nonneg (Nat.cast_nonneg m) ht)]
  apply setIntegral_eq_integral_of_ae_compl_eq_zero
  filter_upwards [ae_support_Ioc_of_Icc hs] with x hx hnot
  have hn : x ∉ Ioc 0 L := fun hi => hnot ⟨hi.1, hi.2.trans hL⟩
  simp [hx hn]

/-- The last correlation vanishes past `(m-1)t`; translation invariance
transports the a.e. support condition before using it. -/
theorem correlation_disintegration {f : ℝ → H} (hf : MemLp f 2 volume)
    {t L : ℝ} (ht : 0 ≤ t) (m : ℕ) (hm : 1 ≤ m) (hL : L ≤ m * t)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc 0 L → f x = 0) :
    (∑ k ∈ Finset.range (m - 1), ∫ s in (0 : ℝ)..t,
      inner ℝ (f (s + k * t)) (f (s + (k + 1 : ℕ) * t))) =
      ∫ x, inner ℝ (f x) (f (x + t)) := by
  have hi := integrable_real_inner hf (memLp_translate hf t)
  have he (s : ℝ) (k : ℕ) : s + (k + 1 : ℕ) * t = (s + k * t) + t := by
    push_cast; ring
  simp_rw [he]
  rw [translated_interval_partition hi]
  rw [intervalIntegral.integral_of_le (mul_nonneg (Nat.cast_nonneg (m - 1)) ht)]
  apply setIntegral_eq_integral_of_ae_compl_eq_zero
  have hs₀ := ae_support_Ioc_of_Icc hs
  have hs₁ := (measurePreserving_add_right volume t).quasiMeasurePreserving.ae hs₀
  filter_upwards [hs₀, hs₁] with x hx hy hnot
  by_cases hxpos : 0 < x
  · have hupper : ((m - 1 : ℕ) : ℝ) * t < x := by
      by_contra hn
      exact hnot ⟨hxpos, le_of_not_gt hn⟩
    have hmcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub hm]; norm_num
    have hn : x + t ∉ Ioc 0 L := by
      intro hmem
      rw [hmcast] at hupper
      nlinarith [hmem.2]
    rw [hy hn, inner_zero_right]
  · have hn : x ∉ Ioc 0 L := fun hmem => hxpos hmem.1
    rw [hx hn, inner_zero_left]

def ChainBound (m : ℕ) (C : ℝ) : Prop :=
  ∀ v : ℕ → H,
    2 * |∑ k ∈ Finset.range (m - 1), inner ℝ (v k) (v (k + 1))| ≤
      C * ∑ k ∈ Finset.range m, ‖v k‖ ^ 2

theorem chain_bound_one : ChainBound (H := H) 1 0 := by
  intro v
  simp

theorem chain_bound_two : ChainBound (H := H) 2 1 := by
  intro v
  simpa [Finset.sum_range_succ] using FiniteShiftChains.chain_two (v 0) (v 1)

theorem chain_bound_three : ChainBound (H := H) 3 (Real.sqrt 2) := by
  intro v
  have h := FiniteShiftChains.chain_three (v 0) (v 1) (v 2)
  have ha := abs_add_le (inner ℝ (v 0) (v 1)) (inner ℝ (v 1) (v 2))
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.reduceSub, Nat.reduceAdd] at *
  linarith

theorem chain_bound_five : ChainBound (H := H) 5 (Real.sqrt 3) := by
  intro v
  have h := FiniteShiftChains.chain_five (v 0) (v 1) (v 2) (v 3) (v 4)
  have h₁ := abs_add_le (inner ℝ (v 0) (v 1)) (inner ℝ (v 1) (v 2))
  have h₂ := abs_add_le (inner ℝ (v 0) (v 1) + inner ℝ (v 1) (v 2))
    (inner ℝ (v 2) (v 3))
  have h₃ := abs_add_le (inner ℝ (v 0) (v 1) + inner ℝ (v 1) (v 2) +
    inner ℝ (v 2) (v 3)) (inner ℝ (v 3) (v 4))
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.reduceSub, Nat.reduceAdd] at *
  linarith

/-- The actual translation estimate, uniformly in the support length and in
every admissible L² function. The chain premise is proved above for the
lengths needed on the 17–19 support cell. -/
theorem translation_bound {m : ℕ} {C : ℝ} (hchain : ChainBound (H := H) m C)
    {f : ℝ → H} (hf : MemLp f 2 volume) {t L : ℝ} (ht : 0 ≤ t)
    (hm : 1 ≤ m) (hL : L ≤ m * t)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc 0 L → f x = 0) :
    2 * |∫ x, inner ℝ (f x) (f (x + t))| ≤ C * ∫ x, ‖f x‖ ^ 2 := by
  have hE (k : ℕ) : Integrable (fun s => ‖f (s + k * t)‖ ^ 2) volume :=
    integrable_energy (memLp_translate hf (k * t))
  have hB := (integrable_finsetSum (Finset.range m) (fun k _ => hE k)).const_mul (C / 2)
  have hpoint (s : ℝ) :
      ‖∑ k ∈ Finset.range (m - 1),
        inner ℝ (f (s + k * t)) (f (s + (k + 1 : ℕ) * t))‖ ≤
      (C / 2) * ∑ k ∈ Finset.range m, ‖f (s + k * t)‖ ^ 2 := by
    have h := hchain (fun k => f (s + k * t))
    rw [Real.norm_eq_abs]
    linarith
  have hmajor := intervalIntegral.norm_integral_le_of_norm_le ht
    (Eventually.of_forall fun s _ => hpoint s) hB.intervalIntegrable
  rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum (fun k _ => (hE k).intervalIntegrable),
    energy_disintegration hf ht m hL hs] at hmajor
  have hI (k : ℕ) : Integrable (fun s =>
      inner ℝ (f (s + k * t)) (f (s + (k + 1 : ℕ) * t))) volume :=
    integrable_real_inner (memLp_translate hf (k * t))
      (memLp_translate hf ((k + 1 : ℕ) * t))
  rw [intervalIntegral.integral_finsetSum (fun k _ => (hI k).intervalIntegrable),
    correlation_disintegration hf ht m hm hL hs] at hmajor
  linarith

theorem translation_two {f : ℝ → H} (hf : MemLp f 2 volume)
    {t L : ℝ} (ht : 0 ≤ t) (hL : L ≤ 2 * t)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc 0 L → f x = 0) :
    2 * |∫ x, inner ℝ (f x) (f (x + t))| ≤ ∫ x, ‖f x‖ ^ 2 := by
  simpa using translation_bound chain_bound_two hf ht (by norm_num) hL hs

theorem translation_three {f : ℝ → H} (hf : MemLp f 2 volume)
    {t L : ℝ} (ht : 0 ≤ t) (hL : L ≤ 3 * t)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc 0 L → f x = 0) :
    2 * |∫ x, inner ℝ (f x) (f (x + t))| ≤ Real.sqrt 2 * ∫ x, ‖f x‖ ^ 2 := by
  exact translation_bound chain_bound_three hf ht (by norm_num) hL hs

theorem translation_five {f : ℝ → H} (hf : MemLp f 2 volume)
    {t L : ℝ} (ht : 0 ≤ t) (hL : L ≤ 5 * t)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc 0 L → f x = 0) :
    2 * |∫ x, inner ℝ (f x) (f (x + t))| ≤ Real.sqrt 3 * ∫ x, ‖f x‖ ^ 2 := by
  exact translation_bound chain_bound_five hf ht (by norm_num) hL hs

theorem translation_disjoint {f : ℝ → H} (hf : MemLp f 2 volume)
    {t L : ℝ} (ht : 0 ≤ t) (hL : L ≤ t)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc 0 L → f x = 0) :
    (∫ x, inner ℝ (f x) (f (x + t))) = 0 := by
  have h := translation_bound chain_bound_one hf ht (by norm_num) (by simpa using hL) hs
  simp only [zero_mul] at h
  have ha : |∫ x, inner ℝ (f x) (f (x + t))| = 0 := by
    have := abs_nonneg (∫ x, inner ℝ (f x) (f (x + t)))
    linarith
  exact abs_eq_zero.mp ha

end Reinmann.SupportTranslation
