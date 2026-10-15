/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.SupportTranslation
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.IsPrimePow
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

/-!
# Uniform support-dependent prime translation form

This module proves the paired autocorrelation normalization, completeness of
the prime-power list through 19, and a uniform bound for the resulting actual
integral form. It does not identify the archimedean Weil operator or prove its
intermediate spectral gap. No Fourier truncation is used in the bound.
-/
noncomputable section
namespace Reinmann.SupportPrimeForm
open MeasureTheory Filter Set
open scoped ENNReal
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def correlation (f : ℝ → H) (t : ℝ) : ℝ :=
  ∫ x, inner ℝ (f x) (f (x + t))

/-- The two shifts have the same real correlation, by translation invariance. -/
theorem correlation_neg (f : ℝ → H) (t : ℝ) :
    correlation f (-t) = correlation f t := by
  unfold correlation
  rw [← integral_add_right_eq_self (fun x => inner ℝ (f x) (f (x + -t))) t]
  simp only [add_neg_cancel_right]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => (real_inner_comm (f (x + t)) (f x)).symm

theorem paired_correlation (f : ℝ → H) (t : ℝ) :
    correlation f t + correlation f (-t) = 2 * correlation f t := by
  rw [correlation_neg]
  ring

/-- For complex scalars the real Hilbert correlation is exactly the real
part of the conjugated product used in the Weil prime term. -/
theorem complex_correlation (f : ℝ → ℂ) (t : ℝ) :
    correlation f t = ∫ x, (star (f x) * f (x + t)).re := by
  unfold correlation
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by simp [Complex.inner, mul_comm]

def complexCorrelation (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ x, star (f (x - t)) * f x

theorem complexCorrelation_translate (f : ℝ → ℂ) (t : ℝ) :
    complexCorrelation f t = ∫ x, star (f x) * f (x + t) := by
  unfold complexCorrelation
  rw [← integral_add_right_eq_self (fun x => star (f (x - t)) * f x) t]
  simp

theorem integrable_complex_product {f g : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) : Integrable (fun x => star (f x) * g x) volume := by
  have hi := L2.integrable_inner (𝕜 := ℂ) (hf.toLp f) (hg.toLp g)
  apply hi.congr
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  rw [hx, hy]
  exact RCLike.inner_apply' _ _

theorem complexCorrelation_re {f : ℝ → ℂ} (hf : MemLp f 2 volume) (t : ℝ) :
    (complexCorrelation f t).re = correlation f t := by
  rw [complexCorrelation_translate, complex_correlation]
  exact (integral_re
    (integrable_complex_product hf (SupportTranslation.memLp_translate hf t))).symm

theorem complexCorrelation_neg (f : ℝ → ℂ) (t : ℝ) :
    complexCorrelation f (-t) = star (complexCorrelation f t) := by
  calc
    _ = ∫ x, star (star (f x) * f (x + t)) := by
      unfold complexCorrelation
      simp only [sub_neg_eq_add]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by simp [mul_comm]
    _ = star (∫ x, star (f x) * f (x + t)) := by
      simpa only [← RCLike.star_def] using
        (integral_conj (f := fun x => star (f x) * f (x + t)) (μ := volume))
    _ = _ := congrArg star (complexCorrelation_translate f t).symm

/-- Full complex normalization of the paired prime term, with L² membership
providing the integrability needed to commute real part and integral. -/
theorem paired_complexCorrelation {f : ℝ → ℂ} (hf : MemLp f 2 volume) (t : ℝ) :
    complexCorrelation f t + complexCorrelation f (-t) =
      ((2 * correlation f t : ℝ) : ℂ) := by
  rw [complexCorrelation_neg]
  apply Complex.ext
  · simp [complexCorrelation_re hf t]
    ring
  · simp

def powers : Finset ℕ := {2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19}

/-- Kernel reduction of a finite decidable proposition, not an external
enumeration oracle. In particular 8, 9, 16 and the endpoint 19 are present. -/
theorem powers_complete : ∀ q ∈ Finset.range 20, IsPrimePow q ↔ q ∈ powers := by
  decide +kernel

theorem powers_subset_range : powers ⊆ Finset.range 20 := by
  intro q hq
  simp only [powers, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num

/-- The list is exactly the prime powers below the varying real cutoff,
not merely a selected collection of terms. -/
theorem mem_active_iff {C : ℝ} (hupper : C ≤ 19) (q : ℕ) :
    q ∈ powers.filter (fun q : ℕ => (q : ℝ) < C) ↔ IsPrimePow q ∧ (q : ℝ) < C := by
  constructor
  · intro hq
    obtain ⟨hm, hc⟩ := Finset.mem_filter.mp hq
    exact ⟨(powers_complete q (powers_subset_range hm)).mpr hm, hc⟩
  · rintro ⟨hp, hc⟩
    have hq20 : q < 20 := by
      have hr : (q : ℝ) < 20 := by linarith
      exact_mod_cast hr
    exact Finset.mem_filter.mpr
      ⟨(powers_complete q (Finset.mem_range.mpr hq20)).mp hp, hc⟩

def chainLength (q : ℕ) : ℕ :=
  if q = 2 then 5 else if q = 3 ∨ q = 4 then 3 else if q = 19 then 1 else 2

def chainConstant (q : ℕ) : ℝ :=
  if q = 2 then Real.sqrt 3 else if q = 3 ∨ q = 4 then Real.sqrt 2
    else if q = 19 then 0 else 1

def weight (q : ℕ) : ℝ := Real.log (q.minFac : ℝ) / Real.sqrt (q : ℝ)

/-- The exact algebraic-logarithmic allowance; no decimal rounding is built
into this definition. The endpoint 19 has zero allowance. -/
def allowance : ℝ := ∑ q ∈ powers, weight q * chainConstant q

def primeForm (C : ℝ) (f : ℝ → H) : ℝ :=
  ∑ q ∈ powers.filter (fun q : ℕ => (q : ℝ) < C),
    weight q * (correlation f (Real.log q) + correlation f (-Real.log q))

def complexPrimeForm (C : ℝ) (f : ℝ → ℂ) : ℂ :=
  ∑ q ∈ powers.filter (fun q : ℕ => (q : ℝ) < C),
    (weight q : ℂ) * (complexCorrelation f (Real.log q) + complexCorrelation f (-Real.log q))

theorem complexPrimeForm_eq {f : ℝ → ℂ} (hf : MemLp f 2 volume) (C : ℝ) :
    complexPrimeForm C f = (primeForm C f : ℂ) := by
  unfold complexPrimeForm primeForm
  simp_rw [paired_complexCorrelation hf, paired_correlation]
  push_cast
  rfl

/-- Exact agreement with the constant evaluated separately by Arb. -/
theorem allowance_eq : allowance =
    Real.sqrt 3 * Real.log 2 / Real.sqrt 2 +
      Real.sqrt 2 * (Real.log 3 / Real.sqrt 3 + Real.log 2 / 2) +
      Real.log 5 / Real.sqrt 5 + Real.log 7 / Real.sqrt 7 +
      Real.log 2 / Real.sqrt 8 + Real.log 3 / 3 +
      Real.log 11 / Real.sqrt 11 + Real.log 13 / Real.sqrt 13 +
      Real.log 2 / 4 + Real.log 17 / Real.sqrt 17 := by
  norm_num [allowance, powers, weight, chainConstant]
  ring

theorem primeForm_eq_prime_power_sum {C : ℝ} (hupper : C ≤ 19) (f : ℝ → H) :
    primeForm C f =
      ∑ q ∈ (Finset.range 20).filter (fun q : ℕ => IsPrimePow q ∧ (q : ℝ) < C),
        weight q * (correlation f (Real.log q) + correlation f (-Real.log q)) := by
  classical
  have he : powers.filter (fun q : ℕ => (q : ℝ) < C) =
      (Finset.range 20).filter (fun q : ℕ => IsPrimePow q ∧ (q : ℝ) < C) := by
    ext q
    rw [mem_active_iff hupper, Finset.mem_filter]
    constructor
    · intro hq
      have hr : (q : ℝ) < 20 := by linarith [hq.2]
      exact ⟨Finset.mem_range.mpr (by exact_mod_cast hr), hq⟩
    · exact And.right
  unfold primeForm
  rw [he]

theorem weight_nonneg (q : ℕ) : 0 ≤ weight q := by
  exact div_nonneg (Real.log_natCast_nonneg _) (Real.sqrt_nonneg _)

theorem chainConstant_nonneg (q : ℕ) : 0 ≤ chainConstant q := by
  unfold chainConstant
  split_ifs <;> positivity

theorem support_guard {q : ℕ} (hq : q ∈ powers) :
    1 ≤ q ∧ 1 ≤ chainLength q ∧ (19 : ℝ) ≤ (q : ℝ) ^ chainLength q := by
  simp only [powers, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [chainLength]

theorem allowed_chain {q : ℕ} (hq : q ∈ powers) :
    SupportTranslation.ChainBound (H := H) (chainLength q) (chainConstant q) := by
  simp only [powers, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | simpa [chainLength, chainConstant] using (SupportTranslation.chain_bound_one (H := H))
    | simpa [chainLength, chainConstant] using (SupportTranslation.chain_bound_two (H := H))
    | simpa [chainLength, chainConstant] using (SupportTranslation.chain_bound_three (H := H))
    | simpa [chainLength, chainConstant] using (SupportTranslation.chain_bound_five (H := H))

theorem logarithmic_support_guard {C : ℝ} (hC : 0 < C) (hupper : C ≤ 19)
    {q : ℕ} (hq : q ∈ powers) :
    Real.log C ≤ chainLength q * Real.log (q : ℝ) := by
  have hg := support_guard hq
  have h := (Real.log_le_log hC hupper).trans
    (Real.log_le_log (by norm_num : (0 : ℝ) < 19) hg.2.2)
  rwa [Real.log_pow] at h

theorem individual_bound {C : ℝ} (hC : 0 < C) (hupper : C ≤ 19)
    {q : ℕ} (hq : q ∈ powers) {f : ℝ → H} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc 0 (Real.log C) → f x = 0) :
    |weight q * (correlation f (Real.log q) + correlation f (-Real.log q))| ≤
      (weight q * chainConstant q) * ∫ x, ‖f x‖ ^ 2 := by
  have hg := support_guard hq
  have ht := Real.log_nonneg (by exact_mod_cast hg.1 : (1 : ℝ) ≤ q)
  have h := SupportTranslation.translation_bound (allowed_chain hq) hf ht hg.2.1
    (logarithmic_support_guard hC hupper hq) hs
  rw [paired_correlation, abs_mul, abs_of_nonneg (weight_nonneg q), abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hw := mul_le_mul_of_nonneg_left h (weight_nonneg q)
  unfold correlation
  convert hw using 1
  ring

/-- Uniform over every supported L² function and every positive cutoff at
most 19. Consequently it covers the entire 17–19 cell, both endpoints, and
every finite Fourier rank without taking a rank-dependent limit. -/
theorem primeForm_bound {C : ℝ} (hC : 0 < C) (hupper : C ≤ 19)
    {f : ℝ → H} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc 0 (Real.log C) → f x = 0) :
    |primeForm C f| ≤ allowance * ∫ x, ‖f x‖ ^ 2 := by
  classical
  have hE : 0 ≤ ∫ x, ‖f x‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  unfold primeForm allowance
  calc
    _ ≤ ∑ q ∈ powers.filter (fun q : ℕ => (q : ℝ) < C),
        |weight q * (correlation f (Real.log q) + correlation f (-Real.log q))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ powers.filter (fun q : ℕ => (q : ℝ) < C),
        (weight q * chainConstant q) * ∫ x, ‖f x‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro q hq
      exact individual_bound hC hupper (Finset.mem_filter.mp hq).1 hf hs
    _ ≤ ∑ q ∈ powers, (weight q * chainConstant q) * ∫ x, ‖f x‖ ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro q _ _
      exact mul_nonneg (mul_nonneg (weight_nonneg q) (chainConstant_nonneg q)) hE
    _ = _ := by rw [Finset.sum_mul]

theorem complexPrimeForm_bound {C : ℝ} (hC : 0 < C) (hupper : C ≤ 19)
    {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc 0 (Real.log C) → f x = 0) :
    ‖complexPrimeForm C f‖ ≤ allowance * ∫ x, ‖f x‖ ^ 2 := by
  rw [complexPrimeForm_eq hf]
  simpa using primeForm_bound hC hupper hf hs

/-- Support endpoints contribute no autocorrelation at the first disjoint
shift. This does not set the endpoint trace to zero. -/
theorem correlation_zero_of_cutoff_le {C : ℝ} (hC : 0 < C) {q : ℕ}
    (hq : 1 ≤ q) (hcut : C ≤ q) {f : ℝ → H} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc 0 (Real.log C) → f x = 0) :
    correlation f (Real.log q) = 0 := by
  exact SupportTranslation.translation_disjoint hf
    (Real.log_nonneg (by exact_mod_cast hq)) (Real.log_le_log hC hcut) hs

end Reinmann.SupportPrimeForm
