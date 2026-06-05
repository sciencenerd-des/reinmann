/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.RiemannSpine
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Experiment A: The Zero-Free-Region Positivity Engine

## First-principles motivation

Every classical zero-free region for `ζ` (de la Vallée Poussin and successors)
runs on a single positivity fact. From the Euler product, for `Re s = σ > 1`,

  `3 log|ζ(σ)| + 4 log|ζ(σ+it)| + log|ζ(σ+2it)|`
      `= ∑_{p,k} (k⁻¹ p^{-kσ}) · (3 + 4cos(kt log p) + cos(2kt log p)) ≥ 0`,

because **every** angular factor `3 + 4cosθ + cos2θ` is nonnegative. Exponentiating
gives `|ζ(σ)|³ |ζ(σ+it)|⁴ |ζ(σ+2it)| ≥ 1`, which is incompatible with a zero on
the line `Re = 1` (and, with quantitative growth bounds, pushes the boundary into
the strip).

This file isolates and *proves* that engine exactly, and frames the remaining
analytic program honestly.

## Honest status

The engine (`cos_341_nonneg`) is unconditional and exact. Turning it into a
zero-free region strictly inside the strip additionally requires growth bounds on
`ζ` near `Re = 1` (Borel–Carathéodory / Hadamard three-circles), which are not yet
in Mathlib. We therefore deliver the verified engine plus the precise reduction
target (`zeroFreeRightOf_half_iff_riemannHypothesis`); the missing input is named,
not hidden.
-/

noncomputable section

namespace Reinmann

/-! ### The positivity engine -/

/-- **The 3–4–1 identity.** `3 + 4cosθ + cos2θ = 2(1+cosθ)²`. This is the exact
algebraic heart of every classical zero-free region. -/
theorem cos_341_eq (θ : ℝ) :
    3 + 4 * Real.cos θ + Real.cos (2 * θ) = 2 * (1 + Real.cos θ) ^ 2 := by
  rw [Real.cos_two_mul]; ring

/-- **The 3–4–1 inequality** (de la Vallée Poussin positivity): the angular factor
is always nonnegative. -/
theorem cos_341_nonneg (θ : ℝ) : 0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
  rw [cos_341_eq]; positivity

/-- The factor vanishes exactly at `θ = π (mod 2π)`, i.e. when `cos θ = -1`.
This is why equality (a zero exactly on the boundary) is so rigid. -/
theorem cos_341_eq_zero_iff (θ : ℝ) :
    3 + 4 * Real.cos θ + Real.cos (2 * θ) = 0 ↔ Real.cos θ = -1 := by
  rw [cos_341_eq]
  constructor
  · intro h
    have : (1 + Real.cos θ) ^ 2 = 0 := by linarith
    have h0 : 1 + Real.cos θ = 0 := by
      exact pow_eq_zero_iff (by norm_num) |>.mp this
    linarith
  · intro h; rw [h]; norm_num

/-! ### The reduction target the engine is aiming at -/

/-- A zero-free region: `ζ` has no zeros strictly to the right of `Re = b`
within the critical strip. Smaller `b` is a stronger statement. -/
def ZeroFreeRightOf (b : ℝ) : Prop :=
  ∀ s : ℂ, b < s.re → s.re < 1 → riemannZeta s ≠ 0

/-- Zero-free regions are monotone: a stronger (smaller-`b`) region implies a
weaker one. -/
theorem zeroFreeRightOf_mono {a b : ℝ} (hab : a ≤ b)
    (h : ZeroFreeRightOf a) : ZeroFreeRightOf b :=
  fun s hb hlt => h s (lt_of_le_of_lt hab hb) hlt

/-- **The target.** Pushing the zero-free boundary all the way down to `1/2` is
*exactly* the Riemann Hypothesis. The de la Vallée Poussin engine currently reaches
`b → 1⁻`; the open problem is to reach `b = 1/2`. -/
theorem zeroFreeRightOf_half_iff_riemannHypothesis :
    ZeroFreeRightOf (1 / 2) ↔ RiemannHypothesis := by
  unfold ZeroFreeRightOf
  exact rightHalfStripZeroFree_iff_riemannHypothesis

end Reinmann
