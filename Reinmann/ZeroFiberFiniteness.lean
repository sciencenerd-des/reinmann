/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.RiemannSpine
import Reinmann.ZeroSymmetry
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Finiteness of Critical-Strip Zeros at a Fixed Imaginary Height

The remaining content of RH is `ZeroImUniqueness`: at each imaginary height
`γ`, the critical strip contains at most one zero. This file proves the
unconditional structural fact underneath that target:

* `finite_strip_zeros_at_height`: at every height `γ`, the set of critical-strip
  zeros with imaginary part `γ` is **finite**.

The point: the zeros at height `γ` all lie on the compact segment
`[0,1] × {γ}`, and Mathlib's `IsCompact.inter_riemannZetaZeros_finite`
(a consequence of the discreteness of the zero set) makes that intersection
finite. So `ZeroImUniqueness` is not a statement about an a priori infinite
fiber — it asks whether a finite set has at most one element.
-/

noncomputable section

open Complex

namespace Reinmann

/-- The horizontal segment `[0,1] × {γ}` is compact: it is the continuous image
of `[0,1] ⊆ ℝ` under `r ↦ r + γ i`. -/
theorem isCompact_strip_segment (γ : ℝ) :
    IsCompact ((fun r : ℝ => (r : ℂ) + (γ : ℂ) * Complex.I) '' Set.Icc 0 1) := by
  have hcont : Continuous (fun r : ℝ => (r : ℂ) + (γ : ℂ) * Complex.I) :=
    Complex.continuous_ofReal.add continuous_const
  exact isCompact_Icc.image hcont

/-- **At each imaginary height, the critical-strip zeros are finite.**
This is unconditional (it does not assume RH or `ZeroImUniqueness`). -/
theorem finite_strip_zeros_at_height (γ : ℝ) :
    {s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ s.im = γ}.Finite := by
  -- The compact segment containing every such zero.
  set seg : Set ℂ := (fun r : ℝ => (r : ℂ) + (γ : ℂ) * Complex.I) '' Set.Icc 0 1 with hseg
  have hfin : (seg ∩ riemannZetaZeros).Finite :=
    (isCompact_strip_segment γ).inter_riemannZetaZeros_finite
  apply hfin.subset
  intro s hs
  obtain ⟨hz, hpos, hlt, him⟩ := hs
  refine ⟨?_, ?_⟩
  · -- s lies on the segment
    rw [hseg]
    refine ⟨s.re, ⟨hpos.le, hlt.le⟩, ?_⟩
    apply Complex.ext
    · simp
    · simp [him]
  · -- s is a zero
    exact (mem_riemannZetaZeros).mpr hz

/-- `ZeroImUniqueness` is exactly the assertion that each (finite) height-fiber
of critical-strip zeros has at most one element, phrased via subsingleton-ness of
the fiber. -/
theorem zeroImUniqueness_iff_fibers_subsingleton :
    ZeroImUniqueness ↔
      ∀ γ : ℝ, ∀ s ∈ {s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ s.im = γ},
        ∀ t ∈ {s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ s.im = γ},
          s.re = t.re := by
  constructor
  · intro h γ s hs t ht
    obtain ⟨hz_s, hs_pos, hs_lt, hsγ⟩ := hs
    obtain ⟨hz_t, ht_pos, ht_lt, htγ⟩ := ht
    exact h s t hz_s hz_t hs_pos hs_lt ht_pos ht_lt (hsγ.trans htγ.symm)
  · intro h s t hz_s hz_t hs_pos hs_lt ht_pos ht_lt hsame
    exact h s.im s ⟨hz_s, hs_pos, hs_lt, rfl⟩ t ⟨hz_t, ht_pos, ht_lt, hsame.symm⟩

end Reinmann
