/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.RiemannSpine
import Reinmann.InvolutionSymmetry
import Reinmann.ConjugateSymmetryComplete
import Reinmann.SpectralEnergyCriterion
import Reinmann.FiberEnergyGap

/-!
# Mirror-Height Energy: a Counterexample Lights Up Two Heights

Conjugate symmetry (now a theorem) sends a zero at height `γ` to a zero at height
`−γ` with the *same* real part. Combined with the spectral-gap bound
(`fiberEnergy_ge_of_offLine`), a single off-line zero forces strictly positive
fiber energy at **both** heights `γ` and `−γ`. So a counterexample cannot be a
solitary blemish at one height; its energy signature is mirrored.

This is an unconditional, verified consequence (not equivalent to RH); it sharpens
the detectability of any RH counterexample.
-/

noncomputable section

open Complex

namespace Reinmann

/-- The conjugate of a strip zero at height `γ` is a strip zero at height `−γ`,
with the same real part. -/
theorem conj_mem_fiberSet {γ : ℝ} {s : ℂ} (hs : s ∈ fiberSet γ) :
    (starRingEnd ℂ) s ∈ fiberSet (-γ) := by
  obtain ⟨hz, hpos, hlt, him⟩ := hs
  refine ⟨conjugate_of_strip_zero stripConjugateZeroSymmetry_proved hpos hlt hz, ?_, ?_, ?_⟩
  · simpa [Complex.conj_re] using hpos
  · simpa [Complex.conj_re] using hlt
  · simp [Complex.conj_im, him]

/-- **Mirror-height energy bound.** An off-line zero at height `γ` forces the
spectral-gap lower bound on the energy at *both* `γ` and `−γ`. -/
theorem offLine_energy_mirror {γ : ℝ} {s : ℂ}
    (hs : s ∈ fiberSet γ) (hoff : s.re ≠ 1 / 2) :
    2 * (s.re - 1 / 2) ^ 2 ≤ fiberEnergy γ ∧
      2 * (s.re - 1 / 2) ^ 2 ≤ fiberEnergy (-γ) := by
  refine ⟨fiberEnergy_ge_of_offLine hs hoff, ?_⟩
  have hc : (starRingEnd ℂ) s ∈ fiberSet (-γ) := conj_mem_fiberSet hs
  have hcoff : ((starRingEnd ℂ) s).re ≠ 1 / 2 := by simpa [Complex.conj_re] using hoff
  have hbound := fiberEnergy_ge_of_offLine hc hcoff
  simpa [Complex.conj_re] using hbound

/-- **A counterexample lights up two distinct heights.** An off-line zero at a
nonzero height `γ` produces strictly positive fiber energy at the two distinct
heights `γ` and `−γ`. -/
theorem offLine_zero_two_positive_energies {γ : ℝ} {s : ℂ}
    (hs : s ∈ fiberSet γ) (hoff : s.re ≠ 1 / 2) (hγ : γ ≠ 0) :
    0 < fiberEnergy γ ∧ 0 < fiberEnergy (-γ) ∧ γ ≠ -γ := by
  refine ⟨fiberEnergy_pos_of_offLine hs hoff, ?_, ?_⟩
  · have hc : (starRingEnd ℂ) s ∈ fiberSet (-γ) := conj_mem_fiberSet hs
    have hcoff : ((starRingEnd ℂ) s).re ≠ 1 / 2 := by simpa [Complex.conj_re] using hoff
    exact fiberEnergy_pos_of_offLine hc hcoff
  · intro h
    apply hγ
    linarith [h]

end Reinmann
