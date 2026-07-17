/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.Order3Certificate
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Basic

/-!
# Van Dantzig pick function and 1-Separation

This module states a van Dantzig mixing framework. We model the moments via
a Laplace exponent `Ψ` of a spectrally negative Lévy process. We show that when
`Ψ(u)/u` is a Pick function satisfying the 1-separation property, it guarantees
the positivity of the order-3 Toeplitz minors as an explicit theorem target.
-/

noncomputable section

open Set Filter Complex

namespace Reinmann

/-- A function `f : ℂ → ℂ` is a Pick function (or Nevanlinna function) if it maps
the upper half-plane to the upper half-plane. -/
def IsPickFunction (f : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, 0 < z.im → 0 < (f z).im

/-- The Pick 1-separation property for a Laplace exponent `Ψ`.
Classically, this means that the poles and zeros of `Ψ(u)/u` interlace on the
negative real axis with gaps of at least 1. We state this as a property of the Pick
representation. -/
structure PickOneSeparation (Ψ : ℂ → ℂ) where
  is_pick : IsPickFunction (fun z => Ψ z / z)
  poles_separated : ∀ z1 z2 : ℂ, (Ψ z1 / z1).im = 0 → (Ψ z2 / z2).im = 0 →
    z1.im = 0 ∧ z2.im = 0 ∧ (z1 ≠ z2 → 1 ≤ |z1.re - z2.re|)

/-- The van Dantzig mixing framework theorem target:
If there exists a Laplace exponent `Ψ` satisfying the Pick 1-separation property
such that the moments `M` match the product of `Ψ`:
`Ψ(1) * Ψ(2) * ... * Ψ(n) = (2n)! / (2 * M n)`
then the moments `M` satisfy the order-3 Toeplitz minor positivity condition. -/
def VanDantzigPickOrder3Bridge : Prop :=
  ∀ (M : ℕ → ℝ) (Ψ : ℂ → ℂ),
    PickOneSeparation Ψ →
    (∀ n : ℕ, ((List.range n).map (fun i => (Ψ (i + 1 : ℂ)).re)).prod =
      ((2 * n).factorial : ℝ) / (2 * M n)) →
    MomentToeplitzOrder3Positive M

end Reinmann
