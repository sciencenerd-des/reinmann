/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.HorizontalCritical
import Mathlib.Analysis.Complex.RealDeriv

/-!
# The ζ′ Bridge for the Horizontal Route

`HorizontalCritical` reduces RH to the componentwise critical-pair exclusion
`NoComponentwiseCriticalPairBetweenZetaZeros`, phrased via the *abstract*
derivatives `deriv (horizontalZetaRe γ)` and `deriv (horizontalZetaIm γ)`.

This file identifies those derivatives with the genuine analytic object — the
complex derivative `ζ′` — so the remaining gap is stated in standard terms:

* `horizontalZetaDeriv_eq`: `d/dx ζ(x+iγ) = ζ′(x+iγ)` (the real-direction
  derivative of the holomorphic slice is the complex derivative);
* `horizontalZetaRe_deriv_eq`: `d/dx Re ζ(x+iγ) = Re ζ′(x+iγ)`;
* `horizontalZetaIm_deriv_eq`: `d/dx Im ζ(x+iγ) = Im ζ′(x+iγ)`.

Consequently a horizontal "critical point" of the real (resp. imaginary) part is
exactly a point where `Re ζ′` (resp. `Im ζ′`) vanishes. The remaining RH-strength
input becomes: between two same-height zeros, `ζ′` cannot have both its real part
and its imaginary part vanish (at possibly different interior points).
-/

noncomputable section

open Complex

namespace Reinmann

variable {γ : ℝ} {x : ℝ}

/-- The holomorphic shift `w ↦ ζ(w + iγ)`; the horizontal slice is its real
restriction. -/
private def zetaShift (γ : ℝ) : ℂ → ℂ := fun w => riemannZeta (w + I * γ)

private theorem zetaShift_hasDerivAt (hne : (x : ℂ) + I * γ ≠ 1) :
    HasDerivAt (zetaShift γ) (deriv riemannZeta ((x : ℂ) + I * γ)) (x : ℂ) := by
  have hinner : HasDerivAt (fun w : ℂ => w + I * γ) 1 (x : ℂ) :=
    (hasDerivAt_id (x : ℂ)).add_const (I * γ)
  have hζ : HasDerivAt riemannZeta (deriv riemannZeta ((x : ℂ) + I * γ))
      ((x : ℂ) + I * γ) := (differentiableAt_riemannZeta hne).hasDerivAt
  have := hζ.comp (x : ℂ) hinner
  simpa [zetaShift, mul_one] using this

/-- The real-direction derivative of the horizontal slice is the complex
derivative `ζ′`. -/
theorem horizontalZetaSlice_hasDerivAt (hne : (x : ℂ) + I * γ ≠ 1) :
    HasDerivAt (horizontalZetaSlice γ) (deriv riemannZeta ((x : ℂ) + I * γ)) x := by
  have h := (zetaShift_hasDerivAt (γ := γ) (x := x) hne).comp_ofReal
  simpa [horizontalZetaSlice, zetaShift] using h

theorem horizontalZetaDeriv_eq (hne : (x : ℂ) + I * γ ≠ 1) :
    horizontalZetaDeriv γ x = deriv riemannZeta ((x : ℂ) + I * γ) :=
  (horizontalZetaSlice_hasDerivAt hne).deriv

/-- `d/dx Re ζ(x+iγ) = Re ζ′(x+iγ)`. -/
theorem horizontalZetaRe_deriv_eq (hne : (x : ℂ) + I * γ ≠ 1) :
    deriv (horizontalZetaRe γ) x = (deriv riemannZeta ((x : ℂ) + I * γ)).re := by
  have h := (zetaShift_hasDerivAt (γ := γ) (x := x) hne).real_of_complex
  have h' : HasDerivAt (horizontalZetaRe γ)
      (deriv riemannZeta ((x : ℂ) + I * γ)).re x := by
    simpa [horizontalZetaRe, horizontalZetaSlice, zetaShift] using h
  exact h'.deriv

/-- `d/dx Im ζ(x+iγ) = Im ζ′(x+iγ)`. -/
theorem horizontalZetaIm_deriv_eq (hne : (x : ℂ) + I * γ ≠ 1) :
    deriv (horizontalZetaIm γ) x = (deriv riemannZeta ((x : ℂ) + I * γ)).im := by
  -- Use `(z * (-I)).re = z.im` and the real-part bridge applied to `ζ(·+iγ)·(-I)`.
  have hmul : HasDerivAt (fun w : ℂ => zetaShift γ w * (-I))
      (deriv riemannZeta ((x : ℂ) + I * γ) * (-I)) (x : ℂ) :=
    (zetaShift_hasDerivAt (γ := γ) (x := x) hne).mul_const (-I)
  have h := hmul.real_of_complex
  have h' : HasDerivAt (horizontalZetaIm γ)
      (deriv riemannZeta ((x : ℂ) + I * γ)).im x := by
    have hre_eq : ∀ z : ℂ, (z * (-I)).re = z.im := by
      intro z; simp [Complex.mul_re]
    simpa [horizontalZetaIm, horizontalZetaSlice, zetaShift, hre_eq] using h
  exact h'.deriv

end Reinmann
