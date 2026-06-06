/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.CompletedZetaConj
import Reinmann.CriticalLineRealSlice
import Reinmann.RiemannSpine
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Data.Nat.Choose.Sum

/-!
# Foundation for the Laguerre–Pólya / Jensen Program (Structure A)

**Correctness note (2026-06-06).** An earlier version of this file built `Ξ` on the
*entire completed zeta* `Λ₀ = completedRiemannZeta₀`.  That was a mathematical
error: `Λ₀ = Λ + 1/s + 1/(1-s)`, so the zeros of `Λ₀` are **not** the Riemann
zeros (at a nontrivial zero `ρ`, `Λ₀(ρ) = 1/ρ + 1/(1-ρ) ≠ 0`).  A Laguerre–Pólya /
Jensen program on `Λ₀` would target the wrong object.

This file now uses **Riemann's `ξ`**, the entire function that removes the poles of
`Λ` by *multiplying* by `s(s-1)/2` (which preserves the zeros), not by adding pole
terms:

  `ξ(s) := (s(s-1)/2) · Λ(s)`,   `Λ = completedRiemannZeta`,
  `Ξ(t) := Re ξ(1/2 + i t) = -((t² + 1/4)/2) · Zslice t`.

Because `Λ(1/2+it)` is real (`completedRiemannZeta_real_on_critical_line`) and the
prefactor `s(s-1)/2 = -(t²+1/4)/2` is a nonzero real scalar, `Ξ` is a genuine
**real, even** function whose **zeros are exactly the critical-line zeros of `ζ`**:

* `xiCompleted_critical_eq_ofReal_Xi`: `ξ(1/2+it) = (Ξ t : ℂ)`.
* `Xi_even`: `Ξ(-t) = Ξ(t)` (functional equation `ξ(1-s) = ξ(s)`).
* `Xi_eq_zero_iff_riemannZeta`: `Ξ t = 0 ↔ ζ(1/2+it) = 0` — the property `Λ₀`
  lacked, and the reason this is the correct target for RH.

`ξ` equals `½ s(s-1) π^{-s/2} Γ(s/2) ζ(s)` exactly, so its Taylor coefficients are
Riemann's `ξ`-coefficients and the classical Pólya–Jensen / Csordas–Norfolk–Varga
results genuinely apply.  The full Pólya–Jensen theorem and the CNV Turán
inequalities are recorded as **named external classical inputs**, not axioms and
not proved here.
-/

noncomputable section

open Complex
open Polynomial
open scoped Polynomial

namespace Reinmann

/-- **Riemann's `ξ`**: `ξ(s) = (s(s-1)/2)·Λ(s)`, `Λ = completedRiemannZeta`.  This
is `½ s(s-1) π^{-s/2} Γ(s/2) ζ(s)`, entire, with exactly the nontrivial zeros of
`ζ` (the prefactor `s(s-1)/2` only adds zeros at `s = 0, 1`, which are the poles of
`Λ`). -/
def xiCompleted (s : ℂ) : ℂ := s * (s - 1) / 2 * completedRiemannZeta s

/-- The real critical-line slice of Riemann's `ξ`:
`Ξ(t) = Re ξ(1/2+it) = -((t²+1/4)/2)·Zslice t`. -/
def Xi (t : ℝ) : ℝ := -((t ^ 2 + 1 / 4) / 2) * Zslice t

/-- On the critical line, Riemann's `ξ` is the real cast of `Ξ`. -/
theorem xiCompleted_critical_eq_ofReal_Xi (t : ℝ) :
    xiCompleted (1 / 2 + (t : ℂ) * I) = (Xi t : ℂ) := by
  have hpre : (1 / 2 + (t : ℂ) * I) * ((1 / 2 + (t : ℂ) * I) - 1)
      = -((t : ℂ) ^ 2 + 1 / 4) := by
    have h : (1 / 2 + (t : ℂ) * I) * ((1 / 2 + (t : ℂ) * I) - 1)
        = (t : ℂ) ^ 2 * I ^ 2 - 1 / 4 := by ring
    rw [h, Complex.I_sq]; ring
  unfold xiCompleted Xi
  rw [completedRiemannZeta_critical_eq_ofReal, hpre]
  push_cast
  ring

/-- `Ξ` is **even**: `Ξ(-t) = Ξ(t)`, from the functional equation `ξ(1-s) = ξ(s)`
(on the line, `1 - (1/2 + it) = 1/2 - it`). -/
theorem Xi_even (t : ℝ) : Xi (-t) = Xi t := by
  have hz : Zslice (-t) = Zslice t := by
    unfold Zslice
    rw [show (1 / 2 + ((-t : ℝ) : ℂ) * I) = 1 - (1 / 2 + (t : ℂ) * I) by push_cast; ring,
        completedRiemannZeta_one_sub]
  unfold Xi
  rw [hz]; ring

/-- **The zeros of `Ξ` are exactly the critical-line zeros of `ζ`.** This is the
property the old `Λ₀` slice lacked, and is what makes `Ξ` the correct target for
the Laguerre–Pólya / Jensen route to RH. -/
theorem Xi_eq_zero_iff_riemannZeta (t : ℝ) :
    Xi t = 0 ↔ riemannZeta (1 / 2 + (t : ℂ) * I) = 0 := by
  unfold Xi
  rw [mul_eq_zero]
  constructor
  · rintro (hc | hz)
    · exfalso
      have hpos : (0 : ℝ) < (t ^ 2 + 1 / 4) / 2 := by positivity
      linarith [hc]
    · exact riemannZeta_critical_zero_of_Zslice_zero hz
  · intro hζ
    right
    have hg : Gammaℝ (1 / 2 + (t : ℂ) * I) ≠ 0 :=
      Gammaℝ_ne_zero_of_re_pos (by rw [linePoint_re]; norm_num)
    have hdef := riemannZeta_def_of_ne_zero (linePoint_ne_zero t)
    rw [hζ] at hdef
    have hΛ : completedRiemannZeta (1 / 2 + (t : ℂ) * I) = 0 := by
      rcases div_eq_zero_iff.mp hdef.symm with h | h
      · exact h
      · exact absurd h hg
    exact (Zslice_eq_zero_iff t).mpr hΛ

/-! ## Jensen polynomial setup -/

/-- The real even Taylor coefficient sequence for `Ξ`, normalized so that
`Ξ(t) = Σ' n, XiCoeff n * t^(2n)` when the Taylor expansion is available.

The definition is deliberately derivative-based.  It is a concrete real sequence
now, while the analytic theorem identifying it with the entire Taylor expansion
is left to the Laguerre--Pólya/Jensen program. -/
def XiCoeff (n : ℕ) : ℝ :=
  deriv^[2 * n] Xi 0 / ((Nat.factorial (2 * n) : ℕ) : ℝ)

/-- The degree-`d`, shift-`n` Jensen polynomial attached to the `Ξ` coefficient
sequence:

`J_{d,n}(X) = Σ_{k=0}^d binom(d,k) b_{n+k} X^k`. -/
def JensenPoly (d n : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (d + 1),
    Polynomial.C ((Nat.choose d k : ℝ) * XiCoeff (n + k)) * Polynomial.X ^ k

/-- A concrete real-rootedness predicate for real polynomials: every complex
root has zero imaginary part.  This avoids depending on a specialized
hyperbolicity API while expressing exactly what the Jensen criterion needs. -/
def PolynomialHyperbolic (p : ℝ[X]) : Prop :=
  ∀ z : ℂ, Polynomial.eval z (p.map (algebraMap ℝ ℂ)) = 0 → z.im = 0

/-- The Structure-A Jensen target: all Jensen polynomials attached to `Ξ` are
hyperbolic. -/
def AllJensenHyperbolic : Prop :=
  ∀ d n : ℕ, PolynomialHyperbolic (JensenPoly d n)

/-- The external Pólya--Jensen bridge needed to turn Structure A into RH.  It is
kept as a definition, not assumed as an axiom, so the active Lean surface remains
honest about the gap. -/
def PolyaJensenBridge : Prop :=
  RiemannHypothesis ↔ AllJensenHyperbolic

/-- If the Pólya--Jensen bridge is proved, RH is exactly Jensen hyperbolicity for
the coefficient sequence of `Ξ`. -/
theorem riemannHypothesis_iff_allJensenHyperbolic_of_polyaJensen
    (h : PolyaJensenBridge) : RiemannHypothesis ↔ AllJensenHyperbolic :=
  h

/-! ## The `d = 2` Turán fragment -/

/-- The `d = 2` Jensen polynomial has discriminant
`4 * (b_{n+1}^2 - b_n*b_{n+2})`. -/
def JensenQuadraticDiscriminant (n : ℕ) : ℝ :=
  ((2 : ℝ) * XiCoeff (n + 1)) ^ 2 - (4 : ℝ) * XiCoeff n * XiCoeff (n + 2)

/-- The Turán inequality for consecutive `Ξ` coefficients. -/
def XiTuran2 (n : ℕ) : Prop :=
  XiCoeff n * XiCoeff (n + 2) ≤ XiCoeff (n + 1) ^ 2

/-- Nonnegative quadratic Jensen discriminant is exactly the `d = 2` Turán
inequality.  This is the first coefficient-level Jensen fragment; importing the
analytic theorem that `XiTuran2 n` holds for all `n` is the next external
mathematical input. -/
theorem jensenQuadraticDiscriminant_nonneg_iff_turan2 (n : ℕ) :
    0 ≤ JensenQuadraticDiscriminant n ↔ XiTuran2 n := by
  unfold JensenQuadraticDiscriminant XiTuran2
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

/-- A named target for the known Csordas--Norfolk--Varga Turán ladder fragment. -/
def XiTuran2All : Prop :=
  ∀ n : ℕ, XiTuran2 n

/-- If the Turán inequalities are supplied, every quadratic Jensen discriminant
is nonnegative.  This does not prove RH, but it verifies the `d = 2` rung of the
Jensen hyperbolicity program. -/
theorem jensenQuadraticDiscriminants_nonneg_of_turan2All
    (h : XiTuran2All) (n : ℕ) : 0 ≤ JensenQuadraticDiscriminant n :=
  (jensenQuadraticDiscriminant_nonneg_iff_turan2 n).2 (h n)

end Reinmann
