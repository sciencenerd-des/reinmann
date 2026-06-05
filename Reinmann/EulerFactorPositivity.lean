/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.RiemannSpine
import Reinmann.ZeroFreeEngine
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

/-!
# Experiment E1 (bricks): Euler-factor 3-4-1 positivity

Towards the 3-4-1 modulus inequality for `ζ`, this file verifies the two
*local* (per-Euler-factor) ingredients, with no cosines needed:

* `cos341_unit`: for `‖v‖ = 1`, `3 + 4·Re v + Re(v²) = 2(1+Re v)² ≥ 0`. This is the
  3-4-1 engine in complex form (here `v = p^{-i n t}` plays the role of the angle).
* `euler_triple_re_nonneg`: the per-prime numerator
  `3·Re(rⁿ) + 4·Re((r u)ⁿ) + Re((r u²)ⁿ) ≥ 0` for `0 ≤ r`, `‖u‖ = 1` — exactly the
  three Euler factors at `p^{-σ}, p^{-σ-it}, p^{-σ-2it}` (with `r = p^{-σ}`,
  `u = p^{-it}`), raised to the `n`-th series term.
* `hasSum_re_neg_log`, `re_neg_log_one_sub`: the real part of the `-log(1-z)` Taylor
  series, linking the above to `-log‖1-z‖` (the Euler-product log).

The remaining E1 work (documented in `research/EXPERIMENTAL_PROGRAM.md`) is the
`1/n` weighting and the summation/interchange over `Nat.Primes × ℕ`.
-/

noncomputable section

open Complex

namespace Reinmann

/-! ### The complex 3-4-1 engine on the unit circle -/

/-- **Complex 3-4-1 positivity.** For a unit-modulus `v`,
`3 + 4·Re v + Re(v²) = 2(1 + Re v)²`, hence `≥ 0`. -/
theorem cos341_unit (v : ℂ) (hv : ‖v‖ = 1) :
    0 ≤ 3 + 4 * v.re + (v ^ 2).re := by
  have hsq : (v ^ 2).re = v.re ^ 2 - v.im ^ 2 := by
    rw [pow_two, Complex.mul_re]; ring
  have hns : v.re ^ 2 + v.im ^ 2 = 1 := by
    have hnsq : Complex.normSq v = 1 := by
      rw [Complex.normSq_eq_norm_sq, hv]; norm_num
    rw [Complex.normSq_apply] at hnsq
    nlinarith [hnsq]
  rw [hsq]
  nlinarith [hns, sq_nonneg (1 + v.re)]

/-! ### Per-Euler-factor numerator positivity -/

/-- **Per-prime 3-4-1 numerator.** With `r = p^{-σ} ≥ 0` and `u = p^{-it}` on the
unit circle, the `n`-th-term numerator from the three Euler factors is nonnegative.
-/
theorem euler_triple_re_nonneg (r : ℝ) (hr : 0 ≤ r) (u : ℂ) (hu : ‖u‖ = 1) (n : ℕ) :
    0 ≤ 3 * (((r : ℂ)) ^ n).re + 4 * (((r : ℂ) * u) ^ n).re
        + (((r : ℂ) * u ^ 2) ^ n).re := by
  have hu2 : (u ^ 2) ^ n = (u ^ n) ^ 2 := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  have e0 : (((r : ℂ)) ^ n).re = r ^ n := by
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  have e1 : (((r : ℂ) * u) ^ n).re = r ^ n * (u ^ n).re := by
    rw [mul_pow, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
  have e2 : (((r : ℂ) * u ^ 2) ^ n).re = r ^ n * ((u ^ n) ^ 2).re := by
    rw [mul_pow, ← Complex.ofReal_pow, Complex.re_ofReal_mul, hu2]
  rw [e0, e1, e2]
  have hv : ‖u ^ n‖ = 1 := by rw [norm_pow, hu, one_pow]
  have key : 0 ≤ 3 + 4 * (u ^ n).re + ((u ^ n) ^ 2).re := cos341_unit (u ^ n) hv
  have hrn : 0 ≤ r ^ n := pow_nonneg hr n
  nlinarith [key, hrn]

/-! ### Real part of the `-log(1-z)` Taylor series -/

/-- The real part of the `-log(1-z)` Taylor series sums termwise. -/
theorem hasSum_re_neg_log {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (z ^ n / n).re) (-Complex.log (1 - z)).re :=
  Complex.hasSum_re (Complex.hasSum_taylorSeries_neg_log hz)

/-- `Re(-log(1-z)) = -log‖1-z‖` — the bridge to the Euler-product log. -/
theorem re_neg_log_one_sub (z : ℂ) :
    (-Complex.log (1 - z)).re = -Real.log ‖1 - z‖ := by
  rw [Complex.neg_re, Complex.log_re]

end Reinmann
