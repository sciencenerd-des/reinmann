/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.JensenProgram

/-!
# Unifying the Jensen `d=2` rung with the Turán/Toeplitz condition

With `Ξ` now correctly Riemann's `ξ` (`JensenProgram`), the order-`2` frameworks
coincide and we can *prove* the link unconditionally given the nondegeneracy
`XiCoeff (n+2) ≠ 0` (which the moment representation supplies, since
`XiCoeff n = ±2Mₙ/(2n)!` with `Mₙ > 0`):

> the Turán inequality `XiTuran2 n` (⟺ order-`2` Toeplitz minor `≥ 0`) implies the
> degree-`2` **Jensen polynomial `J_{2,n}` is hyperbolic**.

This ties the bottom rung of `AllJensenHyperbolic` to the verified positivity
ladder.  The proof is elementary complex algebra (complete the square): no square
roots, no zero-locus input.

* `jensenPoly_two` — the explicit quadratic.
* `jensenPoly_two_map_eval` — its value over `ℂ`.
* `im_zero_of_sq_eq_nonneg_real` — `w² = (D:ℂ)`, `D ≥ 0` real ⟹ `w` real.
* `jensenPoly_two_hyperbolic_of_turan` — `XiTuran2 n` (+ nondegeneracy) ⟹ `J_{2,n}`
  hyperbolic.
* `allJensenTwo_hyperbolic_of_turan2All` — the whole `d=2` row, from `XiTuran2All`
  and nondegeneracy.
-/

noncomputable section

open Polynomial Complex

namespace Reinmann

/-- The degree-`2` Jensen polynomial of `Ξ` written out. -/
theorem jensenPoly_two (n : ℕ) :
    JensenPoly 2 n
      = C (XiCoeff n) + C (2 * XiCoeff (n + 1)) * X + C (XiCoeff (n + 2)) * X ^ 2 := by
  unfold JensenPoly
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.add_zero,
    Nat.choose_zero_right, Nat.choose_self, Nat.choose_one_right, Nat.cast_one, Nat.cast_ofNat,
    one_mul, pow_zero, pow_one, mul_one]

/-- The complex value of the degree-`2` Jensen polynomial. -/
theorem jensenPoly_two_map_eval (n : ℕ) (z : ℂ) :
    eval z ((JensenPoly 2 n).map (algebraMap ℝ ℂ))
      = (XiCoeff (n + 2) : ℂ) * z ^ 2 + 2 * (XiCoeff (n + 1) : ℂ) * z + (XiCoeff n : ℂ) := by
  rw [jensenPoly_two]
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C,
    Polynomial.map_X, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X, Complex.coe_algebraMap]
  push_cast
  ring

/-- **Reality from a nonnegative-real square.** If `w² = (D:ℂ)` with `D ≥ 0` real,
then `w` is real. (Either `w.im = 0`, or `w.re = 0` forcing `w.im² = -D ≤ 0`.) -/
theorem im_zero_of_sq_eq_nonneg_real {w : ℂ} {D : ℝ} (hD : 0 ≤ D) (h : w ^ 2 = (D : ℂ)) :
    w.im = 0 := by
  have himeq : w.re * w.im + w.im * w.re = 0 := by
    have := congrArg Complex.im h
    simpa [pow_two, Complex.mul_im, Complex.ofReal_im] using this
  have hreeq : w.re * w.re - w.im * w.im = D := by
    have := congrArg Complex.re h
    simpa [pow_two, Complex.mul_re, Complex.ofReal_re] using this
  have hprod : w.re * w.im = 0 := by linarith
  rcases mul_eq_zero.mp hprod with hr | hi
  · have h0 : w.im ^ 2 ≤ 0 := by nlinarith [hreeq, hD, hr]
    have hz : w.im ^ 2 = 0 := le_antisymm h0 (sq_nonneg _)
    exact pow_eq_zero_iff (by norm_num) |>.mp hz
  · exact hi

/-- **Turán ⟹ Jensen `d=2` hyperbolic.** If the Turán inequality holds and the
leading coefficient is nonzero, every complex root of `J_{2,n}` is real. -/
theorem jensenPoly_two_hyperbolic_of_turan (n : ℕ) (h2 : XiCoeff (n + 2) ≠ 0)
    (hT : XiTuran2 n) : PolynomialHyperbolic (JensenPoly 2 n) := by
  intro z hz
  rw [jensenPoly_two_map_eval] at hz
  have hD : (0 : ℝ) ≤ XiCoeff (n + 1) ^ 2 - XiCoeff n * XiCoeff (n + 2) := by
    unfold XiTuran2 at hT; linarith
  have hw : ((XiCoeff (n + 2) : ℂ) * z + (XiCoeff (n + 1) : ℂ)) ^ 2
      = ((XiCoeff (n + 1) ^ 2 - XiCoeff n * XiCoeff (n + 2) : ℝ) : ℂ) := by
    have hexp : ((XiCoeff (n + 2) : ℂ) * z + (XiCoeff (n + 1) : ℂ)) ^ 2
        = (XiCoeff (n + 2) : ℂ) *
            ((XiCoeff (n + 2) : ℂ) * z ^ 2 + 2 * (XiCoeff (n + 1) : ℂ) * z + (XiCoeff n : ℂ))
          + ((XiCoeff (n + 1) : ℂ) ^ 2 - (XiCoeff n : ℂ) * (XiCoeff (n + 2) : ℂ)) := by ring
    rw [hexp, hz, mul_zero, zero_add]; push_cast; ring
  have him : ((XiCoeff (n + 2) : ℂ) * z + (XiCoeff (n + 1) : ℂ)).im = 0 :=
    im_zero_of_sq_eq_nonneg_real hD hw
  have he : XiCoeff (n + 2) * z.im = 0 := by
    simpa [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] using him
  rcases mul_eq_zero.mp he with h | h
  · exact absurd h h2
  · exact h

/-- **The whole `d=2` Jensen row from Turán + nondegeneracy.** If every leading
coefficient is nonzero (supplied by the moment representation) and all Turán
inequalities hold, then every degree-`2` Jensen polynomial is hyperbolic. -/
theorem allJensenTwo_hyperbolic_of_turan2All
    (hnz : ∀ n, XiCoeff n ≠ 0) (hT : XiTuran2All) (n : ℕ) :
    PolynomialHyperbolic (JensenPoly 2 n) :=
  jensenPoly_two_hyperbolic_of_turan n (hnz (n + 2)) (hT n)

end Reinmann
