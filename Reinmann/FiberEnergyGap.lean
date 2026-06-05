/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.RiemannSpine
import Reinmann.SpectralEnergyCriterion
import Reinmann.FiberCentroid
import Reinmann.RiemannHypothesisReduction
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# A Spectral Gap for the Fiber Energy

`SpectralEnergyCriterion.lean` shows `RH ↔ ∀ γ, fiberEnergy γ = 0`. Here we make
the *failure* side quantitative: a single off-line zero cannot have arbitrarily
small effect. By the unconditional reflection symmetry, an off-line zero at
`Re = σ` is always accompanied by its mirror at `1 − σ`, so it contributes at
least `2 (σ − 1/2)²` to the fiber energy.

* `fiberEnergy_ge_of_offLine`: `2 (Re s − 1/2)² ≤ fiberEnergy γ` for any off-line
  zero `s` at height `γ`;
* `fiberEnergy_pos_of_offLine`: hence the energy is strictly positive there;
* `not_riemannHypothesis_iff_exists_fiberEnergy_pos`: RH fails iff some fiber has
  positive energy.

This is a "spectral gap" in spirit: there is no continuous path of
counterexamples with energy decaying to zero while staying off the line — any
off-line zero is detected with weight bounded below by its own distance to the
critical line. (It does not prove RH; positivity of *some* energy is exactly the
negation of RH.)
-/

noncomputable section

open Complex
open scoped BigOperators

namespace Reinmann

/-- **Quantitative lower bound.** An off-line zero at height `γ` forces the fiber
energy to be at least twice the square of its distance to the critical line
(counting its mandatory mirror partner). -/
theorem fiberEnergy_ge_of_offLine {γ : ℝ} {s : ℂ}
    (hs : s ∈ fiberSet γ) (hoff : s.re ≠ 1 / 2) :
    2 * (s.re - 1 / 2) ^ 2 ≤ fiberEnergy γ := by
  have hsF : s ∈ fiberFinset γ := mem_fiberFinset.mpr hs
  have hgF : zetaInvolution s ∈ fiberFinset γ := zetaInvolution_mem_fiberFinset hsF
  have hgre : (zetaInvolution s).re = 1 - s.re := by
    simp only [zetaInvolution, Complex.sub_re, Complex.one_re, Complex.conj_re]
  have hne : s ≠ zetaInvolution s := by
    intro h
    exact hoff ((zetaInvolution_fixed_iff_re_eq_half s).mp h.symm)
  have hsub : ({s, zetaInvolution s} : Finset ℂ) ⊆ fiberFinset γ := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hsF
    · exact hgF
  have hpair : ∑ x ∈ ({s, zetaInvolution s} : Finset ℂ), (x.re - 1 / 2) ^ 2
      = 2 * (s.re - 1 / 2) ^ 2 := by
    rw [Finset.sum_pair hne, hgre]; ring
  have hmono := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun i _ _ => sq_nonneg (i.re - 1 / 2))
  rw [hpair] at hmono
  exact hmono

/-- An off-line zero forces strictly positive fiber energy. -/
theorem fiberEnergy_pos_of_offLine {γ : ℝ} {s : ℂ}
    (hs : s ∈ fiberSet γ) (hoff : s.re ≠ 1 / 2) :
    0 < fiberEnergy γ := by
  have hne : s.re - 1 / 2 ≠ 0 := sub_ne_zero.mpr hoff
  have hpos : 0 < 2 * (s.re - 1 / 2) ^ 2 := by positivity
  linarith [fiberEnergy_ge_of_offLine hs hoff]

/-- The Riemann Hypothesis fails iff some height-fiber carries positive energy. -/
theorem not_riemannHypothesis_iff_exists_fiberEnergy_pos :
    ¬ RiemannHypothesis ↔ ∃ γ : ℝ, 0 < fiberEnergy γ := by
  rw [riemannHypothesis_iff_forall_fiberEnergy_zero]
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    apply h
    intro γ
    exact le_antisymm (hcon γ) (fiberEnergy_nonneg γ)
  · rintro ⟨γ, hγ⟩ hall
    rw [hall γ] at hγ
    exact lt_irrefl 0 hγ

end Reinmann
