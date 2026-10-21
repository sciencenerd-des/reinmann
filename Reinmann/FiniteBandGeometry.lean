/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.FiniteHeightPFCalibration
import Reinmann.RationalBallCover
import Reinmann.XiAdaptiveTiles
import Reinmann.XiAnnihilator

/-! Finite-width confinement from an upper-right box and an existing low rectangle.
This is finite strengthening; no global zero-free half-plane is assumed. -/
noncomputable section
namespace Reinmann.FiniteBandGeometry
open scoped ComplexConjugate

theorem box_nonzero_of_upper_box {σ H : ℝ} (hσ : 0 ≤ σ)
    (hlow : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → |z.im| ≤ (141/10:ℝ) → xiCompleted z ≠ 0)
    (hupper : ∀ z ∈ RationalBallCover.rectangle σ 1 (141/10) H, xiCompleted z ≠ 0)
    {z : ℂ} (hx0 : σ ≤ z.re) (hx1 : z.re ≤ 1) (hy : |z.im| ≤ H) :
    xiCompleted z ≠ 0 := by
  by_cases hlowy : |z.im| ≤ (141/10:ℝ)
  · exact hlow z (hσ.trans hx0) hx1 hlowy
  · have htop : (141/10:ℝ) ≤ |z.im| := (lt_of_not_ge hlowy).le
    by_cases hpos : 0 ≤ z.im
    · apply hupper z
      exact ⟨hx0, hx1, by simpa [abs_of_nonneg hpos] using htop,
        by simpa [abs_of_nonneg hpos] using hy⟩
    · have hn : z.im ≤ 0 := (lt_of_not_ge hpos).le
      have hmem : conj z ∈ RationalBallCover.rectangle σ 1 (141/10) H := by
        change σ ≤ z.re ∧ z.re ≤ 1 ∧ (141/10:ℝ) ≤ -z.im ∧ -z.im ≤ H
        exact ⟨hx0, hx1, by simpa [abs_of_nonpos hn] using htop,
          by simpa [abs_of_nonpos hn] using hy⟩
      intro hz
      apply hupper (conj z) hmem
      rw [XiDividedDifference.xi_conj, hz]
      simp

theorem lowHeightWidth_of_box {σ H : ℝ}
    (hbox : ∀ z : ℂ, σ ≤ z.re → z.re ≤ 1 → |z.im| ≤ H → xiCompleted z ≠ 0) :
    FiniteHeightPFCalibration.LowHeightWidth (σ-1/2) H := by
  intro s hs ht
  have hright : s.re ≤ σ := not_lt.mp (fun h =>
    hbox s h.le hs.2.2.le ht (XiAnnihilator.xi_zero_of_strip_zero hs.1 hs.2.1 hs.2.2))
  have hzero : riemannZeta (1-s) = 0 := strip_zero_reflects hs.2.1 hs.2.2 hs.1
  have hleft : (1-s).re ≤ σ := not_lt.mp (fun h =>
    hbox (1-s) h.le (by simp only [Complex.sub_re, Complex.one_re]; linarith [hs.2.1])
      (by simpa using ht)
      (XiAnnihilator.xi_zero_of_strip_zero hzero
        (by simp only [Complex.sub_re, Complex.one_re]; linarith [hs.2.2])
        (by simp only [Complex.sub_re, Complex.one_re]; linarith [hs.2.1])))
  simp only [Complex.sub_re, Complex.one_re] at hleft
  rw [abs_le]
  constructor <;> linarith

end Reinmann.FiniteBandGeometry
