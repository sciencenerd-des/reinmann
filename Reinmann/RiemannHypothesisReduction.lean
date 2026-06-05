/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.RiemannSpine
import Reinmann.InvolutionSymmetry
import Reinmann.ConjugateSymmetryComplete
import Reinmann.ZeroSymmetry

/-!
# Unconditional Reduction of RH to Zero Imaginary-Height Uniqueness

`ConjugateSymmetryComplete.lean` proves the conjugate-symmetry bridge
(`StripConjugateZeroSymmetry`) as a theorem, removing it from the list of
assumptions. As a consequence, mathlib's `RiemannHypothesis` is now provably
**equivalent** to the single remaining arithmetic statement `ZeroImUniqueness`:
at most one critical-strip zero occurs at each imaginary height.

This isolates the entire remaining content of RH into one clean target.
-/

noncomputable section

namespace Reinmann

/-- `ZeroImUniqueness` alone implies the Riemann Hypothesis: the conjugate
symmetry side condition is now discharged by `stripConjugateZeroSymmetry_proved`. -/
theorem riemannHypothesis_of_zeroImUniqueness
    (huniq : ZeroImUniqueness) : RiemannHypothesis :=
  uniqueness_implies_rh huniq stripConjugateZeroSymmetry_proved

/-- Conversely, the Riemann Hypothesis implies `ZeroImUniqueness`. -/
theorem zeroImUniqueness_of_riemannHypothesis
    (hrh : RiemannHypothesis) : ZeroImUniqueness :=
  zeroImUniqueness_of_noSameImaginaryPartCollision
    (noSameImaginaryPartCollision_of_riemannHypothesis hrh)

/-- **The remaining content of RH, isolated.**
Mathlib's `RiemannHypothesis` is equivalent to `ZeroImUniqueness`. -/
theorem riemannHypothesis_iff_zeroImUniqueness :
    RiemannHypothesis ↔ ZeroImUniqueness :=
  ⟨zeroImUniqueness_of_riemannHypothesis, riemannHypothesis_of_zeroImUniqueness⟩

/-- Equivalent phrasing via the no-collision spectral target. -/
theorem riemannHypothesis_iff_noSameImaginaryPartCollision_unconditional :
    RiemannHypothesis ↔ NoSameImaginaryPartCollision :=
  riemannHypothesis_iff_noSameImaginaryPartCollision stripConjugateZeroSymmetry_proved

/-- Equivalent phrasing via fiberwise real-coordinate uniqueness at every height. -/
theorem riemannHypothesis_iff_forall_zeroFiberRealUnique_unconditional :
    RiemannHypothesis ↔ ∀ γ : Real, ZeroFiberRealUnique γ :=
  riemannHypothesis_iff_forall_zeroFiberRealUnique stripConjugateZeroSymmetry_proved

/-! ### Local structure of the height-fibers (unconditional)

Now that conjugate symmetry is a theorem, the geometric involution
`s ↦ 1 - conj s` acts on the zero set with no hypotheses. We record the
resulting unconditional facts about a single imaginary height. -/

/-- **Fiber reflection.** Every critical-strip zero `s` has a partner zero at the
same imaginary height with real part reflected across `1/2`. -/
theorem strip_zero_height_partner {s : ℂ}
    (hpos : 0 < s.re) (hlt : s.re < 1) (hz : riemannZeta s = 0) :
    riemannZeta (zetaInvolution s) = 0 ∧
      (zetaInvolution s).im = s.im ∧
      (zetaInvolution s).re = 1 - s.re := by
  refine ⟨involution_maps_strip_zeros stripConjugateZeroSymmetry_proved ⟨hpos, hlt⟩ hz,
    ?_, ?_⟩
  · simp only [zetaInvolution, Complex.sub_im, Complex.one_im, Complex.conj_im,
      zero_sub, neg_neg]
  · simp only [zetaInvolution, Complex.sub_re, Complex.one_re, Complex.conj_re]

/-- **Single zeros sit on the critical line.** If an imaginary height carries a
*unique* critical-strip zero, that zero has real part exactly `1/2`.

This is unconditional and isolates the mechanism behind `ZeroImUniqueness → RH`:
the symmetry `σ ↦ 1 - σ` forces a lone fiber element to be its own reflection. -/
theorem unique_zero_at_height_on_line {s : ℂ}
    (hpos : 0 < s.re) (hlt : s.re < 1) (hz : riemannZeta s = 0)
    (huniq : ∀ t : ℂ, riemannZeta t = 0 → 0 < t.re → t.re < 1 →
      t.im = s.im → t = s) :
    s.re = 1 / 2 := by
  obtain ⟨hz', him', hre'⟩ := strip_zero_height_partner hpos hlt hz
  have hstrip' : 0 < (zetaInvolution s).re ∧ (zetaInvolution s).re < 1 :=
    zetaInvolution_preserves_strip ⟨hpos, hlt⟩
  have hpartner_eq : zetaInvolution s = s :=
    huniq (zetaInvolution s) hz' hstrip'.1 hstrip'.2 him'
  have : (zetaInvolution s).re = s.re := by rw [hpartner_eq]
  rw [hre'] at this
  linarith

end Reinmann
