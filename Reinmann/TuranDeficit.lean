/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.Order3Certificate

/-!
# A deficit interface for the decreasing Xi coefficient ratios

The algebra is proved. No theta estimate uniform in n is asserted. This avoids
using the increasing-ratio hypotheses of the older sufficient certificate.
-/
noncomputable section
namespace Reinmann

def turanQuotient (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  a n * a (n + 2) / a (n + 1) ^ 2

def turanDeficit (a : ℕ → ℝ) (n : ℕ) : ℝ := 1 - turanQuotient a n

/-- Exact normalized five-coefficient identity. -/
theorem order3_deficit_identity (a b c d e : ℝ)
    (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    order3DetExpr a b c d e / c ^ 3 =
      (1 - b * d / c ^ 2) ^ 2 -
        (b * d / c ^ 2) ^ 2 * (1 - a * c / b ^ 2) * (1 - c * e / d ^ 2) := by
  unfold order3DetExpr
  field_simp [hb, hc, hd]
  ring

/-- A quantitative sufficient condition. The slack must be proved from the
coefficient source, not inferred from finitely many observations. -/
theorem order3_pos_of_deficit_slack (a b c d e ε : ℝ)
    (hb : b ≠ 0) (hc : 0 < c) (hd : d ≠ 0) (hε : 0 < ε)
    (hslack : ε ≤ (1 - b * d / c ^ 2) ^ 2 -
      (b * d / c ^ 2) ^ 2 * (1 - a * c / b ^ 2) * (1 - c * e / d ^ 2)) :
    0 < order3DetExpr a b c d e := by
  have hid := order3_deficit_identity a b c d e hb (ne_of_gt hc) hd
  have hpos : 0 < order3DetExpr a b c d e / c ^ 3 := by
    rw [hid]
    exact lt_of_lt_of_le hε hslack
  exact (div_pos_iff_of_pos_right (pow_pos hc 3)).mp hpos

/-- The research obligation still quantifies over every offset. -/
def UniformTuranDeficitSlack (a : ℕ → ℝ) : Prop :=
  ∀ n, 0 < turanDeficit a (n + 1) ^ 2 -
    turanQuotient a (n + 1) ^ 2 * turanDeficit a n * turanDeficit a (n + 2)

/-- One condensation step from a quantitative curvature bound. Here t models
m/(m+r), which is below one. This is algebra, not a bound proved for Xi. -/
theorem condensation_pos_of_quantitative_bound (next prev center left right t : ℝ)
    (hprev : 0 < prev) (hcenter : center ≠ 0) (ht : t < 1)
    (hbound : left * right ≤ t * center ^ 2)
    (hcond : next * prev = center ^ 2 - left * right) : 0 < next := by
  have hs : 0 < center ^ 2 := sq_pos_of_ne_zero hcenter
  have hstrict : t * center ^ 2 < center ^ 2 := by nlinarith
  have hp : 0 < next * prev := by rw [hcond]; linarith
  exact (mul_pos_iff_of_pos_right hprev).mp hp

/-- An abstract all-rank induction theorem. The quantitative bound is a
hypothesis over ALL ranks and shifts; a finite table cannot instantiate it.
The indices avoid subtraction at natural-number boundaries. -/
theorem all_ranks_pos_of_quantitative_condensation (D : ℕ → ℕ → ℝ)
    (hzero : ∀ m, 0 < D 0 m) (hone : ∀ m, 0 < D 1 m)
    (hboundary : ∀ r, 0 < D r 0)
    (hcond : ∀ r m, D (r + 2) (m + 1) * D r (m + 1) =
      D (r + 1) (m + 1) ^ 2 - D (r + 1) m * D (r + 1) (m + 2))
    (hbound : ∀ r m : ℕ,
      (((m : ℝ) + 1) + ((r : ℝ) + 1)) *
        (D (r + 1) m * D (r + 1) (m + 2)) ≤
      ((m : ℝ) + 1) * D (r + 1) (m + 1) ^ 2) :
    ∀ r m, 0 < D r m := by
  intro r
  induction r using Nat.twoStepInduction with
  | zero => exact hzero
  | one => exact hone
  | more r hr hr1 =>
    intro m
    cases m with
    | zero => exact hboundary (r + 2)
    | succ m =>
      have hc := hr1 (m + 1)
      have hp := hr (m + 1)
      have hs : 0 < D (r + 1) (m + 1) ^ 2 := sq_pos_of_pos hc
      have hb := hbound r m
      have hi := hcond r m
      have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
      have hrr : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
      have hg : 0 < (((m : ℝ) + 1) + ((r : ℝ) + 1)) := by positivity
      have hprod : 0 < (((r : ℝ) + 1) * D (r + 1) (m + 1) ^ 2) := by positivity
      have hd : 0 < D (r + 1) (m + 1) ^ 2 -
          D (r + 1) m * D (r + 1) (m + 2) := by
        nlinarith
      have hn : 0 < D (r + 2) (m + 1) * D r (m + 1) := by
        rw [hi]
        exact hd
      exact (mul_pos_iff_of_pos_right hp).mp hn

/-- Exponential-series coefficients of 2 exp(z)-1. -/
def shiftedExponentialGamma (n : ℕ) : ℝ := if n = 0 then 1 else 2

/-- The rank-one strengthened coefficient inequality holds at every index
for this control; it nevertheless fails the proposed rank-two bound below. -/
theorem shiftedExponentialGamma_logConcave (n : ℕ) :
    shiftedExponentialGamma n * shiftedExponentialGamma (n + 2) ≤
      shiftedExponentialGamma (n + 1) ^ 2 := by
  cases n <;> norm_num [shiftedExponentialGamma]

/-- Rank-one strengthened Turan information alone does not imply the proposed
rank-two bound. These are coefficients of the entire function 2 exp(z)-1. -/
theorem exponential_shift_rank2_bound_fails :
    2 * ((1 : ℝ) ^ 2 - 2 * (1 / 3)) ^ 2 <
      4 * (2 ^ 2 - 1 * 1) * ((1 / 3) ^ 2 - 1 * (1 / 12)) := by
  norm_num

/-- Shifted indexing: n=m-1, so this equals epsilon_m=(m+1) delta_(m-1). -/
def scaledTuranDeficit (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) + 2) * turanDeficit a n

/-- Exact rank-two normalization identity. The factor f represents m! and
m is the central shift; dividing all coefficients by a_0 is optional. -/
theorem rank2_scaled_deficit_factorization (a b c f m : ℝ) (hb : b ≠ 0) :
    (b ^ 2 - a * c) * f ^ 2 * (m + 1) =
      (f * b) ^ 2 * ((m + 1) * (1 - a * c / b ^ 2)) := by
  field_simp [hb]

/-- The product mechanism: gamma log-concavity and scaled-deficit log-concavity
imply log-concavity of A2=gamma^2 epsilon. No Xi-specific assumption is proved. -/
theorem rank2_logConcave_of_gamma_and_scaled_deficit
    (g0 g1 g2 e0 e1 e2 : ℝ)
    (hg0 : 0 ≤ g0) (hg2 : 0 ≤ g2) (he0 : 0 ≤ e0) (he2 : 0 ≤ e2)
    (hg : g0 * g2 ≤ g1 ^ 2) (he : e0 * e2 ≤ e1 ^ 2) :
    (g0 ^ 2 * e0) * (g2 ^ 2 * e2) ≤ (g1 ^ 2 * e1) ^ 2 := by
  have hgg : (g0 * g2) ^ 2 ≤ (g1 ^ 2) ^ 2 :=
    (sq_le_sq₀ (mul_nonneg hg0 hg2) (sq_nonneg g1)).mpr hg
  calc
    (g0 ^ 2 * e0) * (g2 ^ 2 * e2) = (g0 * g2) ^ 2 * (e0 * e2) := by ring
    _ ≤ (g1 ^ 2) ^ 2 * e1 ^ 2 :=
      mul_le_mul hgg he (mul_nonneg he0 he2) (sq_nonneg (g1 ^ 2))
    _ = (g1 ^ 2 * e1) ^ 2 := by ring

/-- Summed accelerations give the exact rank slope. This identity permits
negative individual accelerations; it assumes no Xi-specific estimate. -/
theorem rank_slope_eq_cumulative_correction (d c : ℕ → ℝ)
    (hzero : d 0 = 0)
    (hrec : ∀ n, d (n + 2) - d (n + 1) = d (n + 1) - d n + c n) :
    ∀ n, d (n + 1) - d n = d 1 + ∑ k ∈ Finset.range n, c k := by
  intro n
  induction n with
  | zero => simp [hzero]
  | succ n ih =>
    rw [show n + 1 + 1 = n + 2 by omega, hrec n, ih, Finset.sum_range_succ]
    ring

/-- A cumulative lower budget implies a linear lower bound at every rank.
The budget is still an unbounded hypothesis, not verified by a finite scan. -/
theorem rank_lower_bound_of_cumulative_budget (d c : ℕ → ℝ) (b : ℝ)
    (hzero : d 0 = 0)
    (hrec : ∀ n, d (n + 2) - d (n + 1) = d (n + 1) - d n + c n)
    (hbudget : ∀ n, b ≤ d 1 + ∑ k ∈ Finset.range n, c k) :
    ∀ n : ℕ, (n : ℝ) * b ≤ d n := by
  have hs := rank_slope_eq_cumulative_correction d c hzero hrec
  intro n
  induction n with
  | zero => simp [hzero]
  | succ n ih =>
    have hn : b ≤ d (n + 1) - d n := by rw [hs n]; exact hbudget n
    push_cast
    nlinarith

/-- The shift-one strengthened ratio bound is a lower bound on the dual
reciprocal-coefficient ratio. The analytic ratio estimate is not assumed true. -/
theorem boundary_ratio_le_one_iff (r q : ℝ) (hr : 0 < r + 1) :
    (r + 1) * (1 - q) ≤ 1 ↔ r / (r + 1) ≤ q := by
  rw [div_le_iff₀ hr]
  constructor <;> intro h <;> nlinarith

end Reinmann
