/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.CompletedZetaConj

/-!
# Foundation for the Laguerre–Pólya / Jensen Program (Structure A)

First verified step of Structure A (`research/RH_SOLUTION_STRUCTURES.md`): the
critical-line slice of the *entire* completed zeta `Λ₀` is a genuine **real, even**
function of the real variable `t`:

  `Ξ(t) := Re Λ₀(1/2 + i t)`.

* `completedZeta₀_critical_eq_ofReal_Xi`: `Λ₀(1/2 + i t) = (Ξ t : ℂ)` (realness).
* `Xi_even`: `Ξ(-t) = Ξ(t)` (from the functional equation `Λ₀(1-s) = Λ₀(s)`).

Because `Ξ` is real and even, its Taylor coefficients `b_n` (coefficients of `t^{2n}`)
are real — the prerequisite for the Jensen-polynomial / Laguerre–Pólya criterion
`RH ⟺ every Jensen polynomial of (b_n) is real-rooted`. Defining the `b_n` and Jensen
polynomials and stating that equivalence is the next step.
-/

noncomputable section

open Complex

namespace Reinmann

/-- The real critical-line slice of the entire completed zeta. -/
def Xi (t : ℝ) : ℝ := (completedRiemannZeta₀ (1 / 2 + (t : ℂ) * I)).re

/-- On the critical line the entire completed zeta is the real cast of `Ξ`. -/
theorem completedZeta₀_critical_eq_ofReal_Xi (t : ℝ) :
    completedRiemannZeta₀ (1 / 2 + (t : ℂ) * I) = (Xi t : ℂ) := by
  apply Complex.ext
  · simp [Xi]
  · rw [Complex.ofReal_im]
    exact completedZeta₀_real_on_critical_line (by simp : ((1 / 2 + (t : ℂ) * I)).re = 1 / 2)

/-- `Ξ` is **even**: `Ξ(-t) = Ξ(t)`, from the functional equation `Λ₀(1-s) = Λ₀(s)`
(on the line, `1 - (1/2 + it) = 1/2 - it`). -/
theorem Xi_even (t : ℝ) : Xi (-t) = Xi t := by
  unfold Xi
  congr 1
  rw [show (1 / 2 + ((-t : ℝ) : ℂ) * I) = 1 - (1 / 2 + (t : ℂ) * I) by push_cast; ring]
  exact completedRiemannZeta₀_one_sub (1 / 2 + (t : ℂ) * I)

end Reinmann
