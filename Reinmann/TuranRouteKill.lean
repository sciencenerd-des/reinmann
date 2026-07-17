/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

/-!
# Route-kill: local Turán data cannot close the order-3 contiguous rung

The classical unconditional results about the `Ξ` coefficients closest to the
strict-ladder frontier are the second-order Turán inequalities
(Csordas–Norfolk–Varga 1986) and the third-order Turán inequalities
(Dimitrov–Lucas 2011).  A tempting shortcut for the strict ladder's `k = 3`
rung (`XiContigMinorStrictPositiveAt 3`) is a *sequence-level* implication:

> positivity + strict 2nd-order Turán + 3rd-order Turán
>   ⟹  the contiguous `3 × 3` Toeplitz determinant is nonnegative.

**This implication is false**, and this module preserves the machine-checked
counterexample, per the falsification discipline of the research plan.

The witness `(b₀,…,b₄) = (1/100, 1, 5/4, 1, 1/100)` satisfies all five
positivity conditions, all three strict log-concavity conditions, and both
third-order Turán inequalities (each with margin `≈ 0.68`), yet the Toeplitz
determinant

`b₂(b₂² - b₁b₃) - b₁(b₂b₃ - b₁b₄) + b₀(b₃² - b₂b₄) = 45/64 - 31/25 + 79/8000 < 0`.

Structurally: the determinant is increasing in `b₄` (its `b₄`-coefficient is
`b₁² - b₀b₂ > 0`), equals the perfect square `(b₂² - b₁b₃)²/b₂ ≥ 0` at the
log-concavity boundary `b₄ = b₃²/b₂`, but dips negative for small `b₀, b₄`,
where third-order Turán only requires `3b₂² ≥ 4b₁b₃`.

**Consequence.**  Closing the `k = 3` rung of the strict ladder requires
`Ξ`-specific quantitative input beyond the local `(2nd, 3rd)`-Turán window —
e.g. effective coefficient asymptotics in the style of
Griffin–Ono–Rolen–Zagier together with a certified finite prefix.  RH remains
unproved; this module only prunes a dead branch honestly.
-/

namespace Reinmann

/-- **The sequence-level shortcut is false.**  Positivity, strict second-order
Turán (log-concavity), and third-order Turán on a five-term window do not
imply nonnegativity of the contiguous `3 × 3` Toeplitz determinant. -/
theorem turan23_not_imp_toeplitz3 :
    ¬ (∀ b0 b1 b2 b3 b4 : ℝ,
        0 < b0 → 0 < b1 → 0 < b2 → 0 < b3 → 0 < b4 →
        b0 * b2 < b1 ^ 2 → b1 * b3 < b2 ^ 2 → b2 * b4 < b3 ^ 2 →
        (b1 * b2 - b0 * b3) ^ 2 ≤ 4 * (b1 ^ 2 - b0 * b2) * (b2 ^ 2 - b1 * b3) →
        (b2 * b3 - b1 * b4) ^ 2 ≤ 4 * (b2 ^ 2 - b1 * b3) * (b3 ^ 2 - b2 * b4) →
        0 ≤ b2 * (b2 ^ 2 - b1 * b3) - b1 * (b2 * b3 - b1 * b4) +
            b0 * (b3 ^ 2 - b2 * b4)) := by
  intro h
  have hc := h (1/100) 1 (5/4) 1 (1/100)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at hc

end Reinmann
