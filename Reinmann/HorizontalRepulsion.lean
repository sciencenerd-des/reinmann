/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.FiberCentroid
import Reinmann.FiberEnergyGap

/-!
# Horizontal Same-Height Repulsion Experiment

This file records a genuinely new analytic route to attack the exact remaining
fiber-cardinality gap.

The idea is to study, for each fixed height `γ`, the real one-variable function

  `x ↦ ‖ζ(x + iγ)‖²`.

If this squared modulus were strictly midpoint-convex on the open critical strip
for every height, then two distinct zeros on the same horizontal line would be
impossible: strict midpoint convexity would force the squared norm at the
midpoint to be `< 0`, contradicting nonnegativity.

This is not claimed as a theorem about zeta. In fact, coarse numerical searches
suggest the global strict-midpoint-convexity statement is too strong. The file is
kept as a diagnostic reduction: any viable same-height repulsion principle must
be weaker and more local than global convexity of `‖ζ(x+iγ)‖²`.
-/

noncomputable section

open Complex

namespace Reinmann

/-- Horizontal squared modulus of zeta at height `γ` and real coordinate `x`. -/
def horizontalZetaNormSq (γ x : ℝ) : ℝ :=
  ‖riemannZeta (x + I * γ : ℂ)‖ ^ 2

/-- Experimental same-height repulsion principle: along every horizontal line,
`‖ζ(x+iγ)‖²` is strictly midpoint-convex inside the critical strip. -/
def HorizontalStrictMidpointConvexZeta : Prop :=
  ∀ γ x y : ℝ, 0 < x → x < 1 → 0 < y → y < 1 → x ≠ y →
    horizontalZetaNormSq γ ((x + y) / 2) <
      (horizontalZetaNormSq γ x + horizontalZetaNormSq γ y) / 2

/-- Strict midpoint convexity of the horizontal squared modulus rules out two
distinct critical-strip zeros at the same height. -/
theorem all_fiber_card_le_one_of_horizontalStrictMidpointConvex
    (hconv : HorizontalStrictMidpointConvexZeta) :
    ∀ γ : ℝ, (fiberFinset γ).card ≤ 1 := by
  intro γ
  rw [Finset.card_le_one]
  intro s hs t ht
  rw [mem_fiberFinset] at hs ht
  obtain ⟨hzs, hspos, hslt, hsim⟩ := hs
  obtain ⟨hzt, htpos, htlt, htim⟩ := ht
  by_contra hne
  have hre_ne : s.re ≠ t.re := by
    intro hre
    apply hne
    apply Complex.ext
    · exact hre
    · rw [hsim, htim]
  have hstrict := hconv γ s.re t.re hspos hslt htpos htlt hre_ne
  have hs_norm : horizontalZetaNormSq γ s.re = 0 := by
    unfold horizontalZetaNormSq
    have hs_eq : (s.re + I * γ : ℂ) = s := by
      apply Complex.ext
      · simp
      · simp [hsim]
    rw [hs_eq, hzs, norm_zero]
    norm_num
  have ht_norm : horizontalZetaNormSq γ t.re = 0 := by
    unfold horizontalZetaNormSq
    have ht_eq : (t.re + I * γ : ℂ) = t := by
      apply Complex.ext
      · simp
      · simp [htim]
    rw [ht_eq, hzt, norm_zero]
    norm_num
  rw [hs_norm, ht_norm] at hstrict
  have hnonneg : 0 ≤ horizontalZetaNormSq γ ((s.re + t.re) / 2) := by
    unfold horizontalZetaNormSq
    positivity
  linarith

/-- The horizontal strict midpoint-convexity repulsion principle implies RH. -/
theorem riemannHypothesis_of_horizontalStrictMidpointConvex
    (hconv : HorizontalStrictMidpointConvexZeta) : RiemannHypothesis :=
  riemannHypothesis_of_all_fiber_card_le_one
    (all_fiber_card_le_one_of_horizontalStrictMidpointConvex hconv)

end Reinmann
