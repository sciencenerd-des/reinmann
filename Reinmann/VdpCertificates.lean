/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.RiemannSpine
import Reinmann.ZeroFreeEngine
import Reinmann.VdpConditional
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Theory of de la Vallée Poussin Certificates

## First-principles development

The classical zero-free region runs on *one* nonnegative cosine polynomial,
`3 + 4cosθ + cos2θ`. From first principles, what made it work was not the specific
numbers but two structural facts:

* **nonnegativity**: `∑ cₖ cos(kθ) ≥ 0` (so the Euler-product log sum is `≥ 0`);
* **the gap `c₀ < c₁`**: the weight `c₁` on the `ζ(σ+it)` factor exceeds the weight
  `c₀` on the polar `ζ(σ)` factor, so a boundary zero of order `m ≥ 1` produces net
  vanishing exponent `c₁·m − c₀ > 0`.

We call any such polynomial a **certificate**, and we *generate a whole family* of
them from `(1 + cosθ)ⁿ`:

| n | scaled identity | (c₀, c₁) | c₁/c₀ |
|---|-----------------|----------|-------|
| 2 | `3 + 4c + cos2θ = 2(1+c)²` | (3, 4) | 1.333… |
| 3 | `10 + 15c + 6cos2θ + cos3θ = 4(1+c)³` | (10, 15) | 1.5 |
| 4 | `35 + 56c + 28cos2θ + 8cos3θ + cos4θ = 8(1+c)⁴` | (35, 56) | 1.6 |

**Experimental finding (observed, not proved here):** `c₁/c₀` is strictly
increasing in `n` and appears to approach `2`. The value `2` is the dVP threshold:
larger `c₁/c₀` lets the same argument push the zero-free boundary further into the
strip. So the higher-order certificates are exactly the tool for *quantitative*
regions — and they are all nonnegative for the same trivial reason: `1 + cosθ ≥ 0`.

Everything below is verified (`safe-verify` clean); the `c₁/c₀ → 2` limit is flagged
as an experimental observation, not a theorem.
-/

noncomputable section

namespace Reinmann

/-! ### The umbrella: every `(1+cosθ)ⁿ` is nonnegative -/

/-- The base of every certificate is nonnegative. -/
theorem one_add_cos_nonneg (θ : ℝ) : 0 ≤ 1 + Real.cos θ := by
  have := Real.neg_one_le_cos θ; linarith

/-- Every power `(1+cosθ)ⁿ` is a nonnegative cosine polynomial. -/
theorem one_add_cos_pow_nonneg (θ : ℝ) (n : ℕ) : 0 ≤ (1 + Real.cos θ) ^ n :=
  pow_nonneg (one_add_cos_nonneg θ) n

/-! ### The generated family of certificates (verified) -/

/-- Order-2 certificate (the classical de la Vallée Poussin polynomial). -/
theorem certificate_two (θ : ℝ) :
    3 + 4 * Real.cos θ + Real.cos (2 * θ) = 2 * (1 + Real.cos θ) ^ 2 :=
  cos_341_eq θ

/-- Order-3 certificate. -/
theorem certificate_three (θ : ℝ) :
    10 + 15 * Real.cos θ + 6 * Real.cos (2 * θ) + Real.cos (3 * θ)
      = 4 * (1 + Real.cos θ) ^ 3 := by
  rw [Real.cos_two_mul, Real.cos_three_mul]; ring

/-- Order-4 certificate. -/
theorem certificate_four (θ : ℝ) :
    35 + 56 * Real.cos θ + 28 * Real.cos (2 * θ) + 8 * Real.cos (3 * θ)
        + Real.cos (4 * θ)
      = 8 * (1 + Real.cos θ) ^ 4 := by
  have h4 : Real.cos (4 * θ) = 2 * Real.cos (2 * θ) ^ 2 - 1 := by
    rw [show (4 : ℝ) * θ = 2 * (2 * θ) by ring]; exact Real.cos_two_mul (2 * θ)
  rw [h4, Real.cos_two_mul θ, Real.cos_three_mul]; ring

/-! ### Nonnegativity of each certificate -/

theorem certificate_two_nonneg (θ : ℝ) :
    0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ) := cos_341_nonneg θ

theorem certificate_three_nonneg (θ : ℝ) :
    0 ≤ 10 + 15 * Real.cos θ + 6 * Real.cos (2 * θ) + Real.cos (3 * θ) := by
  rw [certificate_three]
  have := one_add_cos_pow_nonneg θ 3; linarith

theorem certificate_four_nonneg (θ : ℝ) :
    0 ≤ 35 + 56 * Real.cos θ + 28 * Real.cos (2 * θ) + 8 * Real.cos (3 * θ)
        + Real.cos (4 * θ) := by
  rw [certificate_four]
  have := one_add_cos_pow_nonneg θ 4; linarith

/-! ### The general criterion: the gap `c₀ < c₁` drives the contradiction -/

/-- **General net-exponent positivity.** For any certificate with `0 ≤ c₀ < c₁`, a
boundary zero of order `m ≥ 1` yields a strictly positive net vanishing exponent
`c₁·m − c₀`. This generalizes `vdp_net_exponent_pos` (the `(c₀,c₁) = (3,4)` case)
to the entire certificate family. -/
theorem general_vdp_net_exponent_pos (c₀ c₁ m : ℝ)
    (hc₀ : 0 ≤ c₀) (hlt : c₀ < c₁) (hm : 1 ≤ m) :
    0 < c₁ * m - c₀ := by
  have hc₁ : 0 ≤ c₁ := le_of_lt (lt_of_le_of_lt hc₀ hlt)
  nlinarith [mul_le_mul_of_nonneg_left hm hc₁]

/-- The gap holds for each generated certificate. -/
theorem certificate_two_gap : (3 : ℝ) < 4 := by norm_num
theorem certificate_three_gap : (10 : ℝ) < 15 := by norm_num
theorem certificate_four_gap : (35 : ℝ) < 56 := by norm_num

/-- Each generated certificate drives the boundary contradiction (instantiating the
general criterion at the relevant orders). -/
theorem certificate_three_net_pos {m : ℝ} (hm : 1 ≤ m) : 0 < 15 * m - 10 :=
  general_vdp_net_exponent_pos 10 15 m (by norm_num) certificate_three_gap hm

theorem certificate_four_net_pos {m : ℝ} (hm : 1 ≤ m) : 0 < 56 * m - 35 :=
  general_vdp_net_exponent_pos 35 56 m (by norm_num) certificate_four_gap hm

/-! ### Experimental findings (verified numerics)

The data generated by the family: the gap ratios `c₁/c₀` for `n = 2,3,4`. -/

/-- The ratios `c₁/c₀ = 4/3, 15/10, 56/35` are strictly increasing in the order. -/
theorem certificate_ratios_strictly_increasing :
    (4 : ℝ) / 3 < 15 / 10 ∧ (15 : ℝ) / 10 < 56 / 35 := by
  constructor <;> norm_num

/-- Every generated ratio stays below the de la Vallée Poussin threshold `2`. -/
theorem certificate_ratios_below_two :
    (4 : ℝ) / 3 < 2 ∧ (15 : ℝ) / 10 < 2 ∧ (56 : ℝ) / 35 < 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num

end Reinmann
