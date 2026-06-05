/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.ZetaStripBounds
import Reinmann.RiemannSpine
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# ζ Left-Edge Bound via the Functional Equation (Prerequisite M4, left edge)

Hadamard three-lines (M3, in Mathlib) interpolates `ζ` across a strip from bounds
on the two edges. `ZetaStripBounds` gave the **right** edge (`Re > 1`). Here we
give the **left** edge (`Re < 0`) by the functional equation: for `Re w < 0`,

  `ζ(w) = χ(1-w) · ζ(1-w)`,  `χ(s) = 2 (2π)^{-s} Γ(s) cos(πs/2)`,

and `Re(1-w) > 1`, so `‖ζ(1-w)‖` is controlled by the right-edge Dirichlet bound.
This reduces the left-edge size of `ζ` to the size of the explicit factor `χ`.

* `riemannZeta_eq_chiFactor_mul`: the functional-equation expression for `Re w < 0`.
* `norm_riemannZeta_le_of_re_lt_zero`: `‖ζ(w)‖ ≤ ‖χ(1-w)‖ · reSeriesMajorant(Re(1-w))`.

## Honest status

This is genuine, unconditional, and reduces the left-edge bound to the growth of
the elementary factor `χ` (whose vertical growth comes from `Γ` via Stirling — the
one analytic input still to be drawn from Mathlib). With both edges and the Mathlib
Hadamard interpolation, the remaining work is the `Γ`/Stirling growth of `χ` plus
the final assembly into a quantitative zero-free region — a classical de la Vallée
Poussin result (a true theorem **weaker** than RH; not RH itself).
-/

noncomputable section

open Complex

namespace Reinmann

/-- The functional-equation factor `χ(s) = 2 (2π)^{-s} Γ(s) cos(πs/2)`. -/
def chiFactor (s : ℂ) : ℂ :=
  2 * (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s * Complex.cos ((Real.pi : ℂ) * s / 2)

/-- **Functional-equation expression on the left half-plane.** For `Re w < 0`,
`ζ(w) = χ(1-w) · ζ(1-w)`, where `Re(1-w) > 1`. -/
theorem riemannZeta_eq_chiFactor_mul {w : ℂ} (hw : w.re < 0) :
    riemannZeta w = chiFactor (1 - w) * riemannZeta (1 - w) := by
  have hre1 : 1 < (1 - w).re := by
    rw [Complex.sub_re, Complex.one_re]; linarith
  have hne_nat : ∀ n : ℕ, (1 - w) ≠ -(n : ℂ) := by
    intro n h
    have hre := congrArg Complex.re h
    rw [Complex.sub_re, Complex.one_re, Complex.neg_re, Complex.natCast_re] at hre
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hne_one : (1 - w) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re] at hre
    linarith
  have hfe := riemannZeta_one_sub (s := 1 - w) hne_nat hne_one
  rw [show (1 : ℂ) - (1 - w) = w by ring] at hfe
  rw [hfe, chiFactor]

/-- **Left-edge bound.** For `Re w < 0`,
`‖ζ(w)‖ ≤ ‖χ(1-w)‖ · reSeriesMajorant(Re(1-w))`, reducing the left-edge size of `ζ`
to the size of the elementary factor `χ`. -/
theorem norm_riemannZeta_le_of_re_lt_zero {w : ℂ} (hw : w.re < 0) :
    ‖riemannZeta w‖ ≤ ‖chiFactor (1 - w)‖ * reSeriesMajorant (1 - w).re := by
  have hre1 : 1 < (1 - w).re := by
    rw [Complex.sub_re, Complex.one_re]; linarith
  rw [riemannZeta_eq_chiFactor_mul hw, norm_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_riemannZeta_le_realSeries hre1) (norm_nonneg _)

end Reinmann
