/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.CriticalLineRealSlice

/-!
# Counting Critical-Line Zeros via Sign Changes

Building on `riemannZeta_critical_zero_of_sign_change`, we count: a strictly
increasing sample `x : Fin (n+1) → ℝ` whose real slice values alternate in sign at
consecutive points yields **`n` distinct zeros of `ζ` on the critical line**, one
strictly inside each consecutive interval.

* `riemannZeta_critical_zero_of_opposite_signs`: opposite-sign pair ⇒ interior zero.
* `exists_injective_critical_zeros_of_alternating`: `n` sign changes ⇒ an injective
  family of `n` critical-line `ζ`-zeros.

Unconditional, on-line lower bounds on the number of critical-line zeros (Hardy's
method, quantified). Not RH-equivalent.
-/

noncomputable section

open Complex

namespace Reinmann

/-- An opposite-sign pair of slice values detects a critical-line `ζ`-zero between
them. -/
theorem riemannZeta_critical_zero_of_opposite_signs {a b : ℝ} (hab : a < b)
    (h : Zslice a * Zslice b < 0) :
    ∃ t : ℝ, a < t ∧ t < b ∧ riemannZeta (1 / 2 + (t : ℂ) * I) = 0 := by
  rcases mul_neg_iff.mp h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact riemannZeta_critical_zero_of_sign_change' hab ha hb
  · exact riemannZeta_critical_zero_of_sign_change hab ha hb

/-- **Counting critical-line zeros.** If `x` is strictly increasing and the real
slice `Zslice` changes sign across every consecutive pair `x i, x (i+1)`, then
there is an injective family of `n` zeros of `ζ` on the critical line, with the
`i`-th zero strictly inside `(x i, x (i+1))`. -/
theorem exists_injective_critical_zeros_of_alternating {n : ℕ}
    (x : Fin (n + 1) → ℝ) (hmono : StrictMono x)
    (halt : ∀ i : Fin n, Zslice (x i.castSucc) * Zslice (x i.succ) < 0) :
    ∃ z : Fin n → ℝ, Function.Injective z ∧
      ∀ i : Fin n, x i.castSucc < z i ∧ z i < x i.succ ∧
        riemannZeta (1 / 2 + (z i : ℂ) * I) = 0 := by
  choose z hz1 hz2 hz3 using fun i : Fin n =>
    riemannZeta_critical_zero_of_opposite_signs
      (hmono i.castSucc_lt_succ) (halt i)
  refine ⟨z, ?_, fun i => ⟨hz1 i, hz2 i, hz3 i⟩⟩
  intro i j hij
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exfalso
    have hlt' : (i : ℕ) < (j : ℕ) := hlt
    have hle : i.succ ≤ j.castSucc := by
      rw [Fin.le_def]; simp only [Fin.val_succ, Fin.val_castSucc]; omega
    have hxle : x i.succ ≤ x j.castSucc := hmono.monotone hle
    have hzz : z i < z j :=
      lt_of_lt_of_le (hz2 i) (le_trans hxle (le_of_lt (hz1 j)))
    rw [hij] at hzz; exact lt_irrefl _ hzz
  · exact heq
  · exfalso
    have hgt' : (j : ℕ) < (i : ℕ) := hgt
    have hle : j.succ ≤ i.castSucc := by
      rw [Fin.le_def]; simp only [Fin.val_succ, Fin.val_castSucc]; omega
    have hxle : x j.succ ≤ x i.castSucc := hmono.monotone hle
    have hzz : z j < z i :=
      lt_of_lt_of_le (hz2 j) (le_trans hxle (le_of_lt (hz1 i)))
    rw [hij] at hzz; exact lt_irrefl _ hzz

/-- Concrete instance: two consecutive sign changes give two distinct critical-line
zeros. -/
theorem exists_two_distinct_critical_zeros {a b c : ℝ}
    (hab : a < b) (hbc : b < c)
    (h1 : Zslice a * Zslice b < 0) (h2 : Zslice b * Zslice c < 0) :
    ∃ t₁ t₂ : ℝ, t₁ < t₂ ∧
      riemannZeta (1 / 2 + (t₁ : ℂ) * I) = 0 ∧
      riemannZeta (1 / 2 + (t₂ : ℂ) * I) = 0 := by
  obtain ⟨t₁, ht1a, ht1b, hz1⟩ := riemannZeta_critical_zero_of_opposite_signs hab h1
  obtain ⟨t₂, ht2b, ht2c, hz2⟩ := riemannZeta_critical_zero_of_opposite_signs hbc h2
  exact ⟨t₁, t₂, lt_trans ht1b ht2b, hz1, hz2⟩

end Reinmann
