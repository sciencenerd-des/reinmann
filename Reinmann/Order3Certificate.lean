/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.XiMomentKernel
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic

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

open Filter Topology

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

/-- A nonnegative normalized ratio expression gives a nonnegative raw order-`3`
determinant whenever the central weighted moment is positive. -/
theorem order3DetNonneg_of_ratio_nonneg (M : ℕ → ℝ) (n : ℕ)
    (hc : 0 < weightedMoment M (n + 2))
    (hr : 0 ≤ momentToeplitzOrder3RatioExpr M n) :
    Order3DetNonneg M n := by
  unfold Order3DetNonneg
  rw [momentToeplitzContigMinor_eq_ratioExpr M n (ne_of_gt hc)]
  exact mul_nonneg (pow_nonneg (le_of_lt hc) 3) hr

/-- The asymptotic statement needed for the order-`3` tail, expressed in the
normalized ratio coordinates used by the effective-asymptotics program. -/
def Order3RatioTailGap (M : ℕ → ℝ) (N : ℕ) : Prop :=
  ∀ n : ℕ, N ≤ n → 0 ≤ momentToeplitzOrder3RatioExpr M n

/-- A positive scaled asymptotic limit gives an effective normalized tail.
This is the exact analytic interface needed from a Xi-specific asymptotic
theorem: a limit of `(n+1)^3 D_n` at a positive value forces `D_n ≥ 0`
eventually, with an extracted finite threshold `N`. -/
theorem order3RatioTailGap_of_scaled_limit
    (M : ℕ → ℝ) {L : ℝ} (hL : 0 < L)
    (hlim : Tendsto
      (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ 3) * momentToeplitzOrder3RatioExpr M n)
      atTop (nhds L)) :
    ∃ N : ℕ, Order3RatioTailGap M N := by
  have hevent : ∀ᶠ n : ℕ in atTop,
      L / 2 < (((n + 1 : ℕ) : ℝ) ^ 3) * momentToeplitzOrder3RatioExpr M n := by
    exact hlim (Ioi_mem_nhds (by linarith))
  rcases (eventually_atTop.1 hevent) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hs := hN n hn
  have hp : 0 < (((n + 1 : ℕ) : ℝ) ^ 3) := by positivity
  nlinarith

/-! ## Xi-specific coefficient-side interface -/

/-- A positive scaled `k = 3` limit in the exact kernel normalization used by
`XiMomentKernel`.  This is a named analytic target: the definition records the
precise convention that an eventual Xi asymptotic proof must instantiate. -/
def XiOrder3PositiveScaledLimit (M : ℕ → ℝ) : Prop :=
  ∃ L : ℝ, 0 < L ∧
    Tendsto
      (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ 3) *
        momentToeplitzOrder3RatioExpr M n)
      atTop (nhds L)

/-- Positive Pólya moments provide the denominator sign needed by the
normalized tail interface. -/
theorem weightedMoment_pos_of_pos (M : ℕ → ℝ)
    (hMpos : ∀ n : ℕ, 0 < M n) (n : ℕ) :
    0 < weightedMoment M n := by
  unfold weightedMoment
  exact div_pos (hMpos n) (by exact_mod_cast (2 * n).factorial_pos)

/-- The scaled-limit contract gives an eventual tail for the actual Xi
`3 × 3` Toeplitz minors, after transporting through Pólya's coefficient
normalization.  The theorem is conditional on the named Xi moment
representation and does not assert the missing asymptotic itself. -/
theorem xiToeplitzMinor3_eventually_nonneg_of_scaled_limit
    {M : ℕ → ℝ}
    (hMpos : ∀ n : ℕ, 0 < M n)
    (hM : ∀ n, XiCoeff n = (-1) ^ n *
      (2 * M n / ((2 * n).factorial : ℝ)))
    (hlim : XiOrder3PositiveScaledLimit M) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 ≤ XiToeplitzMinor3 n := by
  rcases hlim with ⟨L, hL, hscaled⟩
  rcases order3RatioTailGap_of_scaled_limit M hL hscaled with ⟨N, htail⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hpos : ∀ k : ℕ, 0 < weightedMoment M k :=
    weightedMoment_pos_of_pos M hMpos
  rw [xiToeplitzMinor3_eq_contig]
  rw [xiToeplitzContigMinor_nonneg_iff_moment_of_kernelRep hM 3 (n + 2)]
  exact order3DetNonneg_of_ratio_nonneg M n (hpos (n + 2)) (htail n hn)

/-! ## Adjacent-ratio normal form and an effective certificate -/

/- The four adjacent ratios of five consecutive weighted moments are the
coordinates in which the normalized determinant has a particularly transparent
curvature form. -/
def order3AdjacentRatio (M : ℕ → ℝ) (n : ℕ) : ℝ :=
  weightedMoment M (n + 1) / weightedMoment M n

def order3RatioGapExpr (a b c d : ℝ) : ℝ :=
  (a * (c - b) ^ 2 - c * (b - a) * (d - c)) / (a * b ^ 2)

/-- Exact adjacent-ratio factorization of the normalized order-`3` expression.
The numerator is the competition between the square of the middle ratio gap
and the product of the neighbouring gaps. -/
theorem momentToeplitzOrder3RatioExpr_eq_adjacentGap
    (M : ℕ → ℝ) (n : ℕ)
    (hpos : ∀ k : ℕ, 0 < weightedMoment M k) :
    momentToeplitzOrder3RatioExpr M n =
      order3RatioGapExpr (order3AdjacentRatio M n)
        (order3AdjacentRatio M (n + 1))
        (order3AdjacentRatio M (n + 2))
        (order3AdjacentRatio M (n + 3)) := by
  have h0 := ne_of_gt (hpos n)
  have h1 := ne_of_gt (hpos (n + 1))
  have h2 := ne_of_gt (hpos (n + 2))
  have h3 := ne_of_gt (hpos (n + 3))
  unfold momentToeplitzOrder3RatioExpr order3RatioGapExpr order3AdjacentRatio
  dsimp only
  field_simp [h0, h1, h2, h3]
  ring

/- A quantitative sufficient condition for the gap expression to be
nonnegative.  The constants `a₀,c₁,l,u,v` are intended to come from explicit
asymptotic bounds: a positive lower bound on `a`, an upper bound on `c`, a
lower bound on the middle gap, and upper bounds on its two neighbours. -/
theorem order3RatioGapExpr_nonneg_of_effective_bounds
    {a b c d a₀ c₁ l u v : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hba : 0 ≤ b - a) (hcb : 0 ≤ c - b) (hdc : 0 ≤ d - c)
    (ha₀ : 0 ≤ a₀) (h₀c₁ : 0 ≤ c₁) (hl : 0 ≤ l)
    (hu : 0 ≤ u)
    (ha_lower : a₀ ≤ a) (hc_upper : c ≤ c₁)
    (hmid : l ≤ c - b) (hleft : b - a ≤ u) (hright : d - c ≤ v)
    (hcert : c₁ * u * v ≤ a₀ * l ^ 2) :
    0 ≤ order3RatioGapExpr a b c d := by
  have hmid_sq : l ^ 2 ≤ (c - b) ^ 2 :=
    (sq_le_sq₀ hl hcb).mpr hmid
  have hleft_sq : a₀ * l ^ 2 ≤ a * (c - b) ^ 2 := by
    calc
      a₀ * l ^ 2 ≤ a₀ * (c - b) ^ 2 :=
        mul_le_mul_of_nonneg_left hmid_sq ha₀
      _ ≤ a * (c - b) ^ 2 :=
        mul_le_mul_of_nonneg_right ha_lower (sq_nonneg _)
  have hgap_prod : (b - a) * (d - c) ≤ u * v :=
    mul_le_mul hleft hright hdc hu
  have hright_prod : c * ((b - a) * (d - c)) ≤ c₁ * (u * v) := by
    exact mul_le_mul hc_upper hgap_prod
      (mul_nonneg hba hdc) h₀c₁
  have hnum : 0 ≤ a * (c - b) ^ 2 - c * (b - a) * (d - c) := by
    calc
      0 ≤ a₀ * l ^ 2 - c₁ * u * v := by linarith
      _ ≤ a * (c - b) ^ 2 - c * (b - a) * (d - c) := by
        have hchain : c₁ * u * v ≤ a * (c - b) ^ 2 :=
          le_trans hcert hleft_sq
        linarith
  unfold order3RatioGapExpr
  exact div_nonneg hnum (le_of_lt (mul_pos ha (sq_pos_of_pos hb)))

/- The sequence-level theorem packages the preceding algebra into the exact
effective normalized `k = 3` tail target.  It is deliberately phrased as an
explicit quantitative hypothesis, so an eventual Xi asymptotic estimate can
be plugged in without changing the Lean conclusion. -/
theorem order3RatioTailGap_of_effective_bounds
    (M : ℕ → ℝ) (N : ℕ) (a₀ c₁ l u v : ℝ)
    (hpos : ∀ k : ℕ, 0 < weightedMoment M k)
    (ha₀ : 0 ≤ a₀) (h₀c₁ : 0 ≤ c₁) (hl : 0 ≤ l)
    (hu : 0 ≤ u)
    (hcert : c₁ * u * v ≤ a₀ * l ^ 2)
    (hbound : ∀ n : ℕ, N ≤ n →
      a₀ ≤ order3AdjacentRatio M n ∧
      order3AdjacentRatio M (n + 2) ≤ c₁ ∧
      l ≤ order3AdjacentRatio M (n + 2) - order3AdjacentRatio M (n + 1) ∧
      order3AdjacentRatio M (n + 1) - order3AdjacentRatio M n ≤ u ∧
      order3AdjacentRatio M (n + 3) - order3AdjacentRatio M (n + 2) ≤ v ∧
      0 ≤ order3AdjacentRatio M (n + 1) - order3AdjacentRatio M n ∧
      0 ≤ order3AdjacentRatio M (n + 2) - order3AdjacentRatio M (n + 1) ∧
      0 ≤ order3AdjacentRatio M (n + 3) - order3AdjacentRatio M (n + 2)) :
    Order3RatioTailGap M N := by
  intro n hn
  rcases hbound n hn with ⟨ha_lower, hc_upper, hmid, hleft, hright, hba, hcb, hdc⟩
  have ha : 0 < order3AdjacentRatio M n := by
    exact div_pos (hpos (n + 1)) (hpos n)
  have hbpos : 0 < order3AdjacentRatio M (n + 1) := by
    exact div_pos (hpos (n + 2)) (hpos (n + 1))
  rw [momentToeplitzOrder3RatioExpr_eq_adjacentGap M n hpos]
  apply order3RatioGapExpr_nonneg_of_effective_bounds ha hbpos hba hcb hdc
    ha₀ h₀c₁ hl hu ha_lower hc_upper hmid hleft hright hcert

/-- Positive central moments plus the normalized ratio tail imply the raw
order-`3` tail gap. -/
theorem order3TailGap_of_ratioTailGap (M : ℕ → ℝ) (N : ℕ)
    (hcentral : ∀ n : ℕ, 0 < weightedMoment M (n + 2))
    (hratio : Order3RatioTailGap M N) :
    Order3TailGap M N := by
  intro n hn
  exact order3DetNonneg_of_ratio_nonneg M n (hcentral n) (hratio n hn)

/-- Finite prefix plus the normalized effective tail closes the order-`3`
moment target.  The only analytic input left is `Order3RatioTailGap`. -/
theorem momentToeplitzOrder3Positive_of_prefix_and_ratioTail
    (M : ℕ → ℝ) (N : ℕ)
    (hpre : ∀ n : ℕ, n < N → Order3DetNonneg M n)
    (hcentral : ∀ n : ℕ, 0 < weightedMoment M (n + 2))
    (hratio : Order3RatioTailGap M N) :
    MomentToeplitzOrder3Positive M := by
  exact momentToeplitzOrder3Positive_of_prefix_and_tail M N hpre
    (order3TailGap_of_ratioTailGap M N hcentral hratio)

end Reinmann
