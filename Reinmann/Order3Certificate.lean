/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.XiMomentKernel

/-!
# Order-3 Toeplitz Certificate Fragment

The first open rung beyond Turán is `MomentToeplitzOrder3Positive M`
(`XiMomentKernel.lean`): nonnegativity of *every* order-`3` factorial-weighted
moment Toeplitz determinant.  Proving it in full is open analysis — it is
`Order3FrontierTheorem`'s payload.

This module does the honest engineering part around that open core:

1. It isolates the determinant as an explicit five-argument polynomial
   `order3DetExpr`, tied to the library's `momentToeplitzOrder3_eq`.
2. It records **machine-checked numeric certificates** — including a strictly
   positive one — so the frontier's numeric evidence is no longer only in Python
   logs but verified in Lean.  (Note the factorial-data determinant is genuinely
   *negative* here, which is exactly why this rung is hard: naive positivity
   fails.)
3. It splits the infinite target into a finite certified prefix plus a single
   **named tail gap** (`Order3TailGap`), and proves
   `certified prefix + tail gap → MomentToeplitzOrder3Positive`.

Nothing here assumes the frontier; the residual analytic content is confined to
`Order3TailGap`, a `Prop` (not an axiom).  `#print axioms` on every theorem
reports only `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

namespace Reinmann

/-! ## The order-3 determinant as an explicit polynomial -/

/-- The order-`3` moment-Toeplitz determinant as a polynomial in five consecutive
weighted moments `m₀,…,m₄`, matching the expansion in `momentToeplitzOrder3_eq`. -/
def order3DetExpr (m0 m1 m2 m3 m4 : ℝ) : ℝ :=
  m2 * (m2 ^ 2 - m1 * m3) - m1 * (m3 * m2 - m1 * m4) + m0 * (m3 ^ 2 - m2 * m4)

/-- The library determinant at offset `n` equals `order3DetExpr` on the five
consecutive weighted moments starting at `n`. -/
theorem momentToeplitzContigMinor_eq_order3DetExpr (M : ℕ → ℝ) (n : ℕ) :
    momentToeplitzContigMinor M 3 (n + 2) =
      order3DetExpr (weightedMoment M n) (weightedMoment M (n + 1))
        (weightedMoment M (n + 2)) (weightedMoment M (n + 3))
        (weightedMoment M (n + 4)) := by
  rw [momentToeplitzOrder3_eq]
  unfold order3DetExpr
  ring

/-! ## Machine-checked numeric certificates -/

/-- A strictly positive order-`3` determinant certificate: the log-convex data
`(1, 2, 5, 13, 33)` yields determinant `1 > 0`.  Verified by `norm_num`. -/
theorem order3DetExpr_pos_certificate : 0 < order3DetExpr 1 2 5 13 33 := by
  unfold order3DetExpr; norm_num

/-- Boundary certificate: geometric (rank-1) data gives determinant exactly `0`. -/
theorem order3DetExpr_geometric_zero (a r : ℝ) :
    order3DetExpr a (a * r) (a * r ^ 2) (a * r ^ 3) (a * r ^ 4) = 0 := by
  unfold order3DetExpr; ring

/-- Frontier witness: factorial data `(0!,1!,2!,3!,4!) = (1,1,2,6,24)` gives a
*negative* order-`3` determinant.  This is why the rung is genuinely open —
positivity is not automatic and must be earned, not assumed. -/
theorem order3DetExpr_factorial_neg : order3DetExpr 1 1 2 6 24 < 0 := by
  unfold order3DetExpr; norm_num

/-! ## Prefix + named tail gap ⟹ the full order-3 target -/

/-- Pointwise order-`3` nonnegativity at offset `n` (decidable for rational data
via `momentToeplitzContigMinor_eq_order3DetExpr` + `norm_num`). -/
def Order3DetNonneg (M : ℕ → ℝ) (n : ℕ) : Prop :=
  0 ≤ momentToeplitzContigMinor M 3 (n + 2)

/-- The residual analytic gap for a moment model `M` beyond a certified prefix of
length `N`: order-`3` nonnegativity for all *large* offsets.  This is a named
hypothesis (a `Prop`), never an axiom — it is exactly what remains open once the
finite front has been certified numerically. -/
def Order3TailGap (M : ℕ → ℝ) (N : ℕ) : Prop :=
  ∀ n : ℕ, N ≤ n → Order3DetNonneg M n

/-- **Decomposition theorem.**  A finite certified prefix together with the named
tail gap yields the full frontier target `MomentToeplitzOrder3Positive`.  This
sharpens what is open: given machine-checked positivity for `n < N`, only
`Order3TailGap M N` stands between the numerics and the Level-1 target. -/
theorem momentToeplitzOrder3Positive_of_prefix_and_tail (M : ℕ → ℝ) (N : ℕ)
    (hpre : ∀ n : ℕ, n < N → Order3DetNonneg M n)
    (htail : Order3TailGap M N) :
    MomentToeplitzOrder3Positive M := by
  intro n
  rcases lt_or_ge n N with h | h
  · exact hpre n h
  · exact htail n h

/-- Reading off the certified-prefix hypothesis through the explicit polynomial:
`Order3DetNonneg M n` is exactly `0 ≤ order3DetExpr …`, so numeric prefixes are
discharged by `norm_num` on rational moment data. -/
theorem order3DetNonneg_iff_expr (M : ℕ → ℝ) (n : ℕ) :
    Order3DetNonneg M n ↔
      0 ≤ order3DetExpr (weightedMoment M n) (weightedMoment M (n + 1))
        (weightedMoment M (n + 2)) (weightedMoment M (n + 3))
        (weightedMoment M (n + 4)) := by
  unfold Order3DetNonneg
  rw [momentToeplitzContigMinor_eq_order3DetExpr]

/-- The ratio-form algebraic equivalence for the order-3 determinant. If the central
moment `weightedMoment M (n + 2)` is non-zero, then the determinant is the product of
the cube of the central moment and the normalized ratio-form expression. -/
theorem momentToeplitzContigMinor_eq_ratioExpr (M : ℕ → ℝ) (n : ℕ)
    (hc : weightedMoment M (n + 2) ≠ 0) :
    momentToeplitzContigMinor M 3 (n + 2) =
      weightedMoment M (n + 2) ^ 3 * momentToeplitzOrder3RatioExpr M n := by
  unfold momentToeplitzOrder3RatioExpr
  dsimp only
  rw [momentToeplitzContigMinor_eq_order3DetExpr]
  unfold order3DetExpr
  field_simp
  ring

end Reinmann
