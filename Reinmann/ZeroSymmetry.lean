/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.RiemannSpine
import Reinmann.InvolutionSymmetry
import Reinmann.TwoBranchArchitecture
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Complex.Basic

/-!
# Zero Symmetry Properties

This file explores what we can prove about the symmetry of Riemann zeta zeros
using only the functional equation, without assuming conjugate symmetry.

## Key Results

We prove that:
1. Zeros come in symmetric pairs under s ↦ 1-s (functional equation)
2. If all zeros are on the critical line, they must be symmetric under conjugation
3. Properties of the imaginary parts of zeros

-/

noncomputable section

namespace Reinmann

/-! ### Functional Equation Pairs -/

/-- For any strip zero at s, there is a corresponding zero at 1-s.
    This is the functional equation symmetry, already proved in RiemannSpine. -/
theorem functional_equation_pair {s : Complex}
    (hstrip : 0 < s.re ∧ s.re < 1) (hz : riemannZeta s = 0) :
    riemannZeta (1 - s) = 0 :=
  strip_zero_reflects hstrip.1 hstrip.2 hz

/-- If a zero is on the critical line, its functional equation pair is its conjugate. -/
theorem criticalLine_zero_pair_is_conjugate {s : Complex}
    (hline : OnCriticalLine s) (_hz : riemannZeta s = 0) :
    1 - s = starRingEnd Complex s := by
  simp only [OnCriticalLine] at hline
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith
  · simp only [Complex.sub_im, Complex.one_im, Complex.conj_im, zero_sub]

/-- The imaginary parts of functional equation pairs sum to zero. -/
theorem functional_pair_im_sum_zero {s : Complex} :
    s.im + (1 - s).im = 0 := by
  simp only [Complex.sub_im, Complex.one_im, zero_sub]
  ring

/-- The real parts of functional equation pairs sum to one. -/
theorem functional_pair_re_sum_one {s : Complex} :
    s.re + (1 - s).re = 1 := by
  simp only [Complex.sub_re, Complex.one_re]
  ring

/-! ### Constraints on Off-Line Zeros -/

/-- If a zero is not on the critical line, then it and its functional equation pair
    are distinct points. -/
theorem offLine_zero_has_distinct_pair {s : Complex}
    (_hstrip : 0 < s.re ∧ s.re < 1)
    (hoffLine : ¬OnCriticalLine s) :
    1 - s ≠ s := by
  intro h
  have hre : (1 - s).re = s.re := by rw [h]
  simp only [Complex.sub_re, Complex.one_re] at hre
  have : s.re = 1 / 2 := by linarith
  exact hoffLine this

/-- An off-line zero has its pair on the opposite side of the critical line. -/
theorem offLine_zero_pair_opposite_side {s : Complex}
    (_hstrip : 0 < s.re ∧ s.re < 1)
    (hright : 1 / 2 < s.re) :
    (1 - s).re < 1 / 2 := by
  simp only [Complex.sub_re, Complex.one_re]
  linarith

/-! ### Constraints from RH Equivalence -/

/-- If RH is false, there exist two distinct zeros in the critical strip
    that are related by the functional equation. -/
theorem not_rh_implies_distinct_functional_pair :
    ¬RiemannHypothesis →
    ∃ s : Complex, 0 < s.re ∧ s.re < 1 ∧ riemannZeta s = 0 ∧
    riemannZeta (1 - s) = 0 ∧ s ≠ 1 - s := by
  intro hnrh
  -- From ¬RH, we get a counterexample in the right half
  have ⟨s, hright, hlt, hz⟩ := not_riemannHypothesis_iff_exists_rightHalfStrip_zero.mp hnrh
  use s
  constructor
  · linarith
  constructor
  · exact hlt
  constructor
  · exact hz
  constructor
  · -- The functional equation gives us the pair
    have hstrip : 0 < s.re ∧ s.re < 1 := ⟨by linarith, hlt⟩
    exact strip_zero_reflects hstrip.1 hstrip.2 hz
  · -- They are distinct because s is off the critical line
    intro h
    have : s.re = 1 / 2 := by
      have hre : s.re = (1 - s).re := by
        rw [← h]
      simp only [Complex.sub_re, Complex.one_re] at hre
      linarith
    linarith

/-! ### Imaginary Part Properties -/

/-- Key property: zeros with the same imaginary part must have the same real part
    (uniqueness for each imaginary part). This is the spectral gap. -/
def ZeroImUniqueness : Prop :=
  ∀ s t : Complex,
    riemannZeta s = 0 → riemannZeta t = 0 →
    0 < s.re → s.re < 1 → 0 < t.re → t.re < 1 →
    s.im = t.im → s.re = t.re

/-- No two critical-strip zeros collide at the same imaginary height with
    different real parts. This is the operator/spectral no-degeneracy target. -/
def NoSameImaginaryPartCollision : Prop :=
  ¬ ∃ s t : Complex,
    riemannZeta s = 0 ∧ riemannZeta t = 0 ∧
    0 < s.re ∧ s.re < 1 ∧ 0 < t.re ∧ t.re < 1 ∧
    s.im = t.im ∧ s.re ≠ t.re

/-- A concrete same-height collision witness for critical-strip zeros. -/
def SameHeightCollisionWitness : Prop :=
  ∃ s t : Complex,
    riemannZeta s = 0 ∧ riemannZeta t = 0 ∧
    0 < s.re ∧ s.re < 1 ∧ 0 < t.re ∧ t.re < 1 ∧
    s.im = t.im ∧ s.re ≠ t.re

/-- A same-height collision witness is exactly the negation of the no-collision target. -/
theorem sameHeightCollisionWitness_iff_not_noSameImaginaryPartCollision :
    SameHeightCollisionWitness ↔ ¬ NoSameImaginaryPartCollision := by
  unfold SameHeightCollisionWitness NoSameImaginaryPartCollision
  constructor
  · intro h hno
    exact hno h
  · intro h
    by_contra hnone
    exact h (by intro hw; exact hnone hw)

/-- At a fixed imaginary height, all critical-strip zeros have the same real
    coordinate. This is the fiberwise spectral rigidity target. -/
def ZeroFiberRealUnique (γ : Real) : Prop :=
  ∀ s t : Complex,
    riemannZeta s = 0 → riemannZeta t = 0 →
    0 < s.re → s.re < 1 → 0 < t.re → t.re < 1 →
    s.im = γ → t.im = γ → s.re = t.re

/-- Global imaginary-height uniqueness is equivalent to fiberwise real-coordinate
    uniqueness at every height. -/
theorem zeroImUniqueness_iff_forall_zeroFiberRealUnique :
    ZeroImUniqueness ↔ ∀ γ : Real, ZeroFiberRealUnique γ := by
  constructor
  · intro h γ s t hz_s hz_t hs_pos hs_lt ht_pos ht_lt hsγ htγ
    exact h s t hz_s hz_t hs_pos hs_lt ht_pos ht_lt (hsγ.trans htγ.symm)
  · intro h s t hz_s hz_t hs_pos hs_lt ht_pos ht_lt hsame
    exact h s.im s t hz_s hz_t hs_pos hs_lt ht_pos ht_lt rfl hsame.symm

/-- Fiberwise uniqueness at every height implies the no-collision target. -/
theorem noSameImaginaryPartCollision_of_forall_zeroFiberRealUnique
    (hfiber : ∀ γ : Real, ZeroFiberRealUnique γ) :
    NoSameImaginaryPartCollision := by
  intro h
  rcases h with ⟨s, t, hz_s, hz_t, hs_pos, hs_lt, ht_pos, ht_lt, him, hre_ne⟩
  exact hre_ne (hfiber s.im s t hz_s hz_t hs_pos hs_lt ht_pos ht_lt rfl him.symm)

/-- Imaginary-height uniqueness rules out same-height real-part collisions. -/
theorem noSameImaginaryPartCollision_of_zeroImUniqueness
    (huniq : ZeroImUniqueness) : NoSameImaginaryPartCollision := by
  intro h
  rcases h with ⟨s, t, hz_s, hz_t, hs_pos, hs_lt, ht_pos, ht_lt, him, hre_ne⟩
  exact hre_ne (huniq s t hz_s hz_t hs_pos hs_lt ht_pos ht_lt him)

/-- No same-height collision implies imaginary-height uniqueness. -/
theorem zeroImUniqueness_of_noSameImaginaryPartCollision
    (hno : NoSameImaginaryPartCollision) : ZeroImUniqueness := by
  intro s t hz_s hz_t hs_pos hs_lt ht_pos ht_lt him
  by_contra hne
  exact hno ⟨s, t, hz_s, hz_t, hs_pos, hs_lt, ht_pos, ht_lt, him, hne⟩

/-- The spectral no-collision target is exactly `ZeroImUniqueness`. -/
theorem noSameImaginaryPartCollision_iff_zeroImUniqueness :
    NoSameImaginaryPartCollision ↔ ZeroImUniqueness := by
  constructor
  · exact zeroImUniqueness_of_noSameImaginaryPartCollision
  · exact noSameImaginaryPartCollision_of_zeroImUniqueness

/-- If s and t are both zeros with the same imaginary part but different real parts,
    and both are in the critical strip, this is the core multiplicity problem.
    This is equivalent to saying that the operator (if it exists) has
    degenerate eigenvalues, which contradicts self-adjointness. -/
theorem same_im_different_re_not_both_in_strip (huniq : ZeroImUniqueness) {s t : Complex}
    (hs_strip : 0 < s.re ∧ s.re < 1)
    (ht_strip : 0 < t.re ∧ t.re < 1)
    (hz : riemannZeta s = 0)
    (ht : riemannZeta t = 0)
    (hsame_im : s.im = t.im)
    (hdiff_re : s.re ≠ t.re) :
    False := by
  have heq : s.re = t.re :=
    huniq s t hz ht hs_strip.1 hs_strip.2 ht_strip.1 ht_strip.2 hsame_im
  exact hdiff_re heq

/-- The imaginary parts of nontrivial zeros form a discrete set (state this formally). -/
def ZeroImaginaryParts : Set Real :=
  {γ : Real | ∃ s : Complex, riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ s.im = γ}

/-! ### Conditional Results -/

/-- Assuming strip zero-level conjugate symmetry, if there's a zero off the critical line,
    there are at least two distinct zeros with the same imaginary part. -/
theorem offLine_zero_implies_im_multiplicity (hconj : StripConjugateZeroSymmetry) :
    (∃ s : Complex, 0 < s.re ∧ s.re < 1 ∧ riemannZeta s = 0 ∧ ¬OnCriticalLine s) →
    ∃ γ : Real, ∃ s t : Complex,
      s ≠ t ∧
      riemannZeta s = 0 ∧ riemannZeta t = 0 ∧
      0 < s.re ∧ s.re < 1 ∧ 0 < t.re ∧ t.re < 1 ∧
      s.im = γ ∧ t.im = γ := by
  intro ⟨s, hpos, hlt, hz, hoffLine⟩
  use s.im
  -- s is a zero off the line
  -- By conjugate symmetry, conj(s) is also a zero
  have hz_conj : riemannZeta (starRingEnd Complex s) = 0 :=
    conjugate_of_strip_zero hconj hpos hlt hz
  -- conj(s) has the same real part but opposite imaginary part
  -- By functional equation, 1 - conj(s) is also a zero
  have hstrip_conj : 0 < (starRingEnd Complex s).re ∧ (starRingEnd Complex s).re < 1 := by
    simp only [Complex.conj_re]
    exact ⟨hpos, hlt⟩
  have hz_inv : riemannZeta (1 - starRingEnd Complex s) = 0 :=
    strip_zero_reflects hstrip_conj.1 hstrip_conj.2 hz_conj
  -- 1 - conj(s) has imaginary part conj(s.im) = s.im
  use s, 1 - starRingEnd Complex s
  have hdistinct : s ≠ 1 - starRingEnd Complex s := by
    intro h
    have : zetaInvolution s = s := by
      simp only [zetaInvolution]
      exact h.symm
    exact hoffLine ((zetaInvolution_fixed_iff_onCriticalLine s).mp this)
  have ht_re_pos : 0 < (1 - starRingEnd Complex s).re := by
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith
  have ht_re_lt : (1 - starRingEnd Complex s).re < 1 := by
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith
  have hsame_im : (1 - starRingEnd Complex s).im = s.im := by
    simp only [Complex.sub_im, Complex.one_im, Complex.conj_im, zero_sub, neg_neg]
  exact ⟨hdistinct, hz, hz_inv, hpos, hlt, ht_re_pos, ht_re_lt, rfl, hsame_im⟩

/-! ### Gap Analysis and Equivalences -/

/-- The HilbertPolya witness implies uniqueness. -/
theorem hilbertPolya_implies_uniqueness (hp : HilbertPolyaWitness) :
    ZeroImUniqueness := by
  intro s t hs ht hs_pos hs_lt ht_pos ht_lt hsame_im
  -- Both s.im and t.im are in the spectrum
  have hs_in : s.im ∈ hp.zeroImagParts := hp.complete s hs hs_pos hs_lt
  have ht_in : t.im ∈ hp.zeroImagParts := hp.complete t ht ht_pos ht_lt
  -- By selfAdjoint_forces_criticalLine, both have re = 1/2
  have hs_half : s.re = 1/2 :=
    hp.selfAdjoint_forces_criticalLine s.im hs_in s hs rfl hs_pos hs_lt
  have ht_half : t.re = 1/2 :=
    hp.selfAdjoint_forces_criticalLine t.im ht_in t ht (hsame_im ▸ rfl) ht_pos ht_lt
  -- Therefore s.re = t.re
  rw [hs_half, ht_half]

/-- Uniqueness plus strip zero-level conjugate symmetry implies RH. -/
theorem uniqueness_implies_rh
    (huniq : ZeroImUniqueness) (hconj : StripConjugateZeroSymmetry) :
    RiemannHypothesis := by
  by_contra hnrh
  have ⟨s, hright, hlt, hz⟩ :=
    not_riemannHypothesis_iff_exists_rightHalfStrip_zero.mp hnrh
  have hstrip : 0 < s.re ∧ s.re < 1 := ⟨by linarith, hlt⟩
  have hz_conj : riemannZeta (starRingEnd Complex s) = 0 :=
    conjugate_of_strip_zero hconj hstrip.1 hstrip.2 hz
  have hstrip_conj : 0 < (starRingEnd Complex s).re ∧
      (starRingEnd Complex s).re < 1 := by
    simp only [Complex.conj_re]
    exact hstrip
  have hz_invol : riemannZeta (zetaInvolution s) = 0 :=
    strip_zero_reflects hstrip_conj.1 hstrip_conj.2 hz_conj
  have hsame_im : s.im = (zetaInvolution s).im := by
    simp only [zetaInvolution, Complex.sub_im, Complex.one_im, Complex.conj_im,
      zero_sub, neg_neg]
  have hdiff_re : s.re ≠ (zetaInvolution s).re := by
    simp only [zetaInvolution, Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith
  have hinvol_strip : 0 < (zetaInvolution s).re ∧ (zetaInvolution s).re < 1 :=
    zetaInvolution_preserves_strip hstrip
  exact same_im_different_re_not_both_in_strip huniq
    hstrip hinvol_strip hz hz_invol hsame_im hdiff_re

/-- Alias for the main uniqueness → RH theorem. -/
theorem riemannHypothesis_of_zero_im_uniqueness
    (huniq : ZeroImUniqueness) (hconj : StripConjugateZeroSymmetry) :
    RiemannHypothesis :=
  uniqueness_implies_rh huniq hconj

/-- The no-collision spectral target plus strip zero-level conjugation implies RH. -/
theorem riemannHypothesis_of_no_same_imaginary_collision
    (hno : NoSameImaginaryPartCollision) (hconj : StripConjugateZeroSymmetry) :
    RiemannHypothesis :=
  uniqueness_implies_rh
    (zeroImUniqueness_of_noSameImaginaryPartCollision hno) hconj

/-- RH rules out same-height real-part collisions among critical-strip zeros. -/
theorem noSameImaginaryPartCollision_of_riemannHypothesis
    (hrh : RiemannHypothesis) :
    NoSameImaginaryPartCollision := by
  intro h
  rcases h with ⟨s, t, hz_s, hz_t, hs_pos, hs_lt, ht_pos, ht_lt, _him, hre_ne⟩
  have hs_half : s.re = 1 / 2 :=
    (criticalStripObligations_of_riemannHypothesis hrh).strip_zero_on_line
      s hs_pos hs_lt hz_s
  have ht_half : t.re = 1 / 2 :=
    (criticalStripObligations_of_riemannHypothesis hrh).strip_zero_on_line
      t ht_pos ht_lt hz_t
  exact hre_ne (hs_half.trans ht_half.symm)

/-- Assuming strip zero-level conjugation, RH is equivalent to no same-height
    real-part collision among critical-strip zeros. -/
theorem riemannHypothesis_iff_noSameImaginaryPartCollision
    (hconj : StripConjugateZeroSymmetry) :
    RiemannHypothesis ↔ NoSameImaginaryPartCollision := by
  constructor
  · exact noSameImaginaryPartCollision_of_riemannHypothesis
  · intro hno
    exact riemannHypothesis_of_no_same_imaginary_collision hno hconj

/-- Assuming strip zero-level conjugation, RH is equivalent to fiberwise
    real-coordinate uniqueness at every imaginary height. -/
theorem riemannHypothesis_iff_forall_zeroFiberRealUnique
    (hconj : StripConjugateZeroSymmetry) :
    RiemannHypothesis ↔ ∀ γ : Real, ZeroFiberRealUnique γ := by
  rw [riemannHypothesis_iff_noSameImaginaryPartCollision hconj]
  rw [noSameImaginaryPartCollision_iff_zeroImUniqueness]
  exact zeroImUniqueness_iff_forall_zeroFiberRealUnique

/-- RH implies the strip zero-level conjugation bridge. On the critical line,
    conjugation agrees with the functional-equation reflection `s ↦ 1 - s`. -/
theorem stripConjugateZeroSymmetry_of_riemannHypothesis
    (hrh : RiemannHypothesis) : StripConjugateZeroSymmetry := by
  intro s hpos hlt hz
  have hline : OnCriticalLine s :=
    (criticalStripObligations_of_riemannHypothesis hrh).strip_zero_on_line
      s hpos hlt hz
  have hconj_eq : starRingEnd Complex s = 1 - s := by
    exact (criticalLine_zero_pair_is_conjugate hline hz).symm
  rw [hconj_eq]
  exact strip_zero_reflects hpos hlt hz

/-- Under strip zero-level conjugation, any failure of RH produces two
    critical-strip zeros with the same imaginary part and different real parts. -/
theorem not_riemannHypothesis_implies_same_height_collision
    (hconj : StripConjugateZeroSymmetry) :
    ¬ RiemannHypothesis → SameHeightCollisionWitness := by
  intro hnrh
  by_contra hno_exists
  have hno : NoSameImaginaryPartCollision := by
    intro h
    exact hno_exists h
  exact hnrh (riemannHypothesis_of_no_same_imaginary_collision hno hconj)

/-- Under strip zero-level conjugation, RH failure is exactly a same-height
    collision witness. -/
theorem not_riemannHypothesis_iff_sameHeightCollisionWitness
    (hconj : StripConjugateZeroSymmetry) :
    ¬ RiemannHypothesis ↔ SameHeightCollisionWitness := by
  rw [riemannHypothesis_iff_noSameImaginaryPartCollision hconj]
  exact sameHeightCollisionWitness_iff_not_noSameImaginaryPartCollision.symm

/-- Under strip zero-level conjugation, any failure of RH produces a failed
    imaginary-height fiber. -/
theorem not_riemannHypothesis_implies_failed_zeroFiberRealUnique
    (hconj : StripConjugateZeroSymmetry) :
    ¬ RiemannHypothesis → ∃ γ : Real, ¬ ZeroFiberRealUnique γ := by
  intro hnrh
  by_contra hno
  have hfiber : ∀ γ : Real, ZeroFiberRealUnique γ := by
    intro γ
    by_contra hbad
    exact hno ⟨γ, hbad⟩
  exact hnrh ((riemannHypothesis_iff_forall_zeroFiberRealUnique hconj).mpr hfiber)

/-- Under strip zero-level conjugation, RH failure is exactly the failure of
    one imaginary-height fiber. -/
theorem not_riemannHypothesis_iff_exists_failed_zeroFiberRealUnique
    (hconj : StripConjugateZeroSymmetry) :
    ¬ RiemannHypothesis ↔ ∃ γ : Real, ¬ ZeroFiberRealUnique γ := by
  rw [riemannHypothesis_iff_forall_zeroFiberRealUnique hconj]
  constructor
  · intro h
    by_contra hnone
    apply h
    intro γ
    by_contra hbad
    exact hnone ⟨γ, hbad⟩
  · intro h hall
    rcases h with ⟨γ, hbad⟩
    exact hbad (hall γ)

/-- Fiberwise real-coordinate uniqueness at every height plus strip zero-level
    conjugation implies RH. -/
theorem riemannHypothesis_of_forall_zeroFiberRealUnique
    (hfiber : ∀ γ : Real, ZeroFiberRealUnique γ)
    (hconj : StripConjugateZeroSymmetry) :
    RiemannHypothesis :=
  uniqueness_implies_rh
    (zeroImUniqueness_iff_forall_zeroFiberRealUnique.mpr hfiber) hconj

/-- The older full-conjugate-symmetry formulation remains available as a corollary. -/
theorem uniqueness_implies_rh_of_conjugateSymmetry
    (huniq : ZeroImUniqueness) (hconj : ConjugateSymmetry) :
    RiemannHypothesis :=
  uniqueness_implies_rh huniq
    (stripConjugateZeroSymmetry_of_conjugateSymmetry hconj)

end Reinmann
