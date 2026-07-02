/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.EulerFactorPositivity
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Experiment E1.3/E1.4: global Euler-product bridge

`EulerFactorPositivity` proves the local 3-4-1 inequality for each Euler factor.
This file records the public Mathlib bridge that performs the global
prime-summability and Euler-product assembly.

The key point is methodological: the hard interchange/summability over primes is
not reproved locally. Mathlib already exposes the needed L-series theorem, and
we specialize it to the trivial character as the verified global certificate.
-/

noncomputable section

open Complex
open scoped LSeries.notation

namespace Reinmann

/-! ### Prime-log summability -/

/-- Euler-factor logarithms for the trivial character are summable over primes in
the half-plane `1 < re s`. -/
theorem trivial_prime_log_summable {s : ℂ} (hs : 1 < s.re) :
    Summable fun p : Nat.Primes =>
      -Complex.log (1 - (1 : DirichletCharacter ℂ 1) p * (p : ℂ) ^ (-s)) := by
  exact DirichletCharacter.summable_neg_log_one_sub_mul_prime_cpow
    (N := 1) (1 : DirichletCharacter ℂ 1) hs

/-! ### Global 3-4-1 modulus bridge -/

/-- Global 3-4-1 inequality for the trivial Dirichlet character, inherited from
Mathlib's Euler-product nonvanishing argument. This is the verified global
counterpart of the local `euler_factor_341_log` brick. -/
theorem trivialCharacter_LSeries_341_ge_one {x : ℝ} (hx : 0 < x) (y : ℝ) :
    ‖L ↗(1 : DirichletCharacter ℂ 1) (1 + x) ^ 3 *
      L ↗(1 : DirichletCharacter ℂ 1) (1 + x + I * y) ^ 4 *
      L ↗((1 : DirichletCharacter ℂ 1) ^ 2 :) (1 + x + 2 * I * y)‖ ≥ 1 := by
  exact DirichletCharacter.norm_LSeries_product_ge_one (N := 1)
    (1 : DirichletCharacter ℂ 1) hx y

/-! ### Zeta Euler-product log identity -/

/-- The zeta Euler-product logarithmic identity used to convert prime-log sums
back to `riemannZeta` in the half-plane `1 < re s`. -/
theorem zeta_euler_log_exp {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-s))) =
      riemannZeta s := by
  exact riemannZeta_eulerProduct_exp_log hs

/-! ### Zeta-form 3-4-1 modulus inequality -/

/-- The trivial Dirichlet character modulo `1` has the same L-series as
`riemannZeta` in the convergence half-plane. -/
theorem trivialChar_LSeries_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    L ↗(1 : DirichletCharacter ℂ 1) s = riemannZeta s := by
  rw [LSeries_congr (g := 1) (s := s)]
  · exact LSeries_one_eq_riemannZeta hs
  · intro n _hn
    exact MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1))

/-- **Zeta-form global 3-4-1 inequality.** For every `σ > 1`,
`‖ζ(σ)^3 ζ(σ+it)^4 ζ(σ+2it)‖ ≥ 1`.

This is the classical de la Vallée Poussin modulus inequality in the half-plane
where the Euler product converges. -/
theorem zeta_341_modulus {σ t : ℝ} (hσ : 1 < σ) :
    ‖riemannZeta (σ : ℂ) ^ 3 * riemannZeta (σ + I * t) ^ 4 *
      riemannZeta (σ + 2 * I * t)‖ ≥ 1 := by
  have hx : 0 < σ - 1 := by linarith
  have h := trivialCharacter_LSeries_341_ge_one (x := σ - 1) hx t
  have hs0 : 1 < (σ : ℂ).re := by simpa using hσ
  have hs1 : 1 < (σ + I * t : ℂ).re := by simp [hσ]
  have hs2 : 1 < (σ + 2 * I * t : ℂ).re := by simp [hσ]
  norm_num at h
  rw [trivialChar_LSeries_eq_riemannZeta hs0,
    trivialChar_LSeries_eq_riemannZeta hs1,
    trivialChar_LSeries_eq_riemannZeta hs2] at h
  simpa [norm_mul, norm_pow, ge_iff_le, mul_assoc] using h

end Reinmann
