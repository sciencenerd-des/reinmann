/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.ConjugateSymmetryComplete
import Reinmann.HorizontalDerivative
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Unconditional Symmetry of ζ′ (the derivative)

## Where this comes from (distant-theory motivation)

In the **electrostatic picture** (Gauss–Lucas / logarithmic potential), the zeros
of `ζ` are unit charges and `ζ′/ζ = ∑_ρ 1/(s-ρ)` is their field; the zeros of `ζ′`
are the *equilibrium points* of that field. A symmetry of the charge configuration
forces the same symmetry on the field and hence on its equilibria.

`ζ` has the conjugation symmetry `ζ(s̄) = ζ̄(s)` (proved: `riemannZeta_conj`). The
charge configuration (zero set) is therefore conjugate-symmetric, so the field and
its equilibria must be too. We make this precise and *unconditional* at the level
of `ζ′`:

* `deriv_riemannZeta_conj`: `ζ′(s̄) = ζ̄′(s)` for `s ≠ 1`;
* `deriv_riemannZeta_zero_conj`: the zeros of `ζ′` are closed under conjugation.

These are genuine new theorems about `ζ′` (not equivalent to RH). They are the
derivative-level analogue of the conjugate symmetry used throughout the project,
and connect to **Speiser's theorem** (RH ⟺ `ζ′ ≠ 0` on `0 < Re s < 1/2`): under
conjugation symmetry, the left-half-strip zeros of `ζ′` come in conjugate pairs.

## Honest scope

`SpeiserLeftHalfZeroFree` below is *defined* as the Speiser target; it is
classically equivalent to RH and is **not** proved here. Only the unconditional
symmetry statements are theorems.
-/

noncomputable section

open Complex
open scoped ComplexConjugate

namespace Reinmann

/-- **Conjugation symmetry of `ζ′`.** For `s ≠ 1`, `ζ′(s̄) = ζ̄′(s)`.

Proof via the electrostatic/reflection idea made rigorous: `conj ∘ ζ ∘ conj`
agrees with `ζ` near `s` (that is the conjugate symmetry of `ζ`), and
`conj ∘ ζ ∘ conj` is holomorphic with derivative `conj (ζ′(s̄))`
(`HasDerivAt.conj_conj`). Uniqueness of the derivative gives the identity. -/
theorem deriv_riemannZeta_conj {s : ℂ} (hs : s ≠ 1) :
    deriv riemannZeta (conj s) = conj (deriv riemannZeta s) := by
  have hconj_ne : (conj s) ≠ 1 := by
    intro h
    apply hs
    have := congrArg (starRingEnd ℂ) h
    simpa using this
  -- ζ is differentiable at s̄.
  have hf : HasDerivAt riemannZeta (deriv riemannZeta (conj s)) (conj s) :=
    (differentiableAt_riemannZeta hconj_ne).hasDerivAt
  -- conj ∘ ζ ∘ conj has derivative conj (ζ′(s̄)) at conj(conj s) = s.
  have hcc := hf.conj_conj
  rw [Complex.conj_conj] at hcc
  -- ζ agrees with conj ∘ ζ ∘ conj on a neighbourhood of s (s ≠ 1).
  have heq : riemannZeta =ᶠ[nhds s]
      (⇑(starRingEnd ℂ) ∘ riemannZeta ∘ ⇑(starRingEnd ℂ)) := by
    filter_upwards [isOpen_ne.mem_nhds hs] with z hz
    change riemannZeta z = conj (riemannZeta (conj z))
    rw [riemannZeta_conj z hz, Complex.conj_conj]
  -- Transfer the derivative to ζ and use uniqueness.
  have hζ : HasDerivAt riemannZeta (conj (deriv riemannZeta (conj s))) s :=
    hcc.congr_of_eventuallyEq heq
  have huniq : deriv riemannZeta s = conj (deriv riemannZeta (conj s)) := hζ.deriv
  have h2 := congrArg (starRingEnd ℂ) huniq
  rw [Complex.conj_conj] at h2
  exact h2.symm

/-- **The zeros of `ζ′` are conjugate-symmetric.** If `ζ′(s) = 0` (`s ≠ 1`), then
`ζ′(s̄) = 0`. -/
theorem deriv_riemannZeta_zero_conj {s : ℂ} (hs : s ≠ 1)
    (h : deriv riemannZeta s = 0) : deriv riemannZeta (conj s) = 0 := by
  rw [deriv_riemannZeta_conj hs, h, map_zero]

/-- Real part of `ζ′` is even under `γ ↦ -γ` along a vertical reflection; imaginary
part is odd. (Direct corollary of conjugation symmetry, stated on the horizontal
slice coordinates.) -/
theorem deriv_riemannZeta_re_conj {s : ℂ} (hs : s ≠ 1) :
    (deriv riemannZeta (conj s)).re = (deriv riemannZeta s).re := by
  rw [deriv_riemannZeta_conj hs, Complex.conj_re]

theorem deriv_riemannZeta_im_conj {s : ℂ} (hs : s ≠ 1) :
    (deriv riemannZeta (conj s)).im = -(deriv riemannZeta s).im := by
  rw [deriv_riemannZeta_conj hs, Complex.conj_im]

/-! ### Speiser's target (definition only; classically ≡ RH, not proved) -/

/-- **Speiser's left-half zero-free target.** `ζ′` has no zeros in the open left
half of the critical strip `0 < Re s < 1/2`. Classically (Speiser 1934) this is
equivalent to RH. Stated here as a target; under `deriv_riemannZeta_zero_conj`
its zeros would occur in conjugate pairs. -/
def SpeiserLeftHalfZeroFree : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 / 2 → deriv riemannZeta s ≠ 0

/-- **Speiser bridge.** Classically, RH is equivalent to the absence of zeros of
`ζ′` in the left half of the critical strip.  This is a named external bridge,
not an axiom and not proved here. -/
def SpeiserBridge : Prop :=
  RiemannHypothesis ↔ SpeiserLeftHalfZeroFree

/-- If Speiser's bridge is supplied, the derivative zero-free target proves RH. -/
theorem riemannHypothesis_of_speiserLeftHalfZeroFree
    (hbridge : SpeiserBridge) (hspeiser : SpeiserLeftHalfZeroFree) :
    RiemannHypothesis :=
  hbridge.mpr hspeiser

/-- If Speiser's bridge is supplied, RH gives the derivative zero-free target. -/
theorem speiserLeftHalfZeroFree_of_riemannHypothesis
    (hbridge : SpeiserBridge) (hRH : RiemannHypothesis) :
    SpeiserLeftHalfZeroFree :=
  hbridge.mp hRH

end Reinmann
