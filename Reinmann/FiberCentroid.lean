/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.RiemannSpine
import Reinmann.InvolutionSymmetry
import Reinmann.ConjugateSymmetryComplete
import Reinmann.SpectralEnergyCriterion
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The Centroid of Each Height-Fiber is Exactly 1/2 (Unconditional)

Continuing the electrostatic picture from `SpectralEnergyCriterion.lean`: the
finite cloud of critical-strip zeros at a fixed imaginary height `γ` is balanced
about the critical line. We prove this **unconditionally**.

The geometric involution `s ↦ 1 - conj s` (`zetaInvolution`) now acts on the zero
set with no hypotheses, because conjugate symmetry is a theorem
(`stripConjugateZeroSymmetry_proved`). On the fiber it is a fixed-point-respecting
involution under which `Re s − 1/2 ↦ −(Re s − 1/2)`. Hence the signed deviations
cancel:

* `fiber_sum_re_sub_half_eq_zero`: `∑_{s ∈ fiber γ} (Re s − 1/2) = 0`;
* `fiber_centroid_eq_half`: the mean real part over a nonempty fiber is `1/2`.

## Interpretation

Combined with `riemannHypothesis_iff_forall_fiberEnergy_zero`, the picture is:
the **first moment** (centroid) of every fiber already equals `1/2`
unconditionally, and RH is *exactly* the statement that the **second moment**
(`fiberEnergy`, the variance) vanishes. So RH says: each balanced finite cloud
has zero spread. This is true, sharp, and machine-checked — and it does not prove
RH, since the second-moment vanishing is equivalent to RH.
-/

noncomputable section

open Complex
open scoped BigOperators

namespace Reinmann

/-- The geometric involution sends a fiber element to a fiber element: it preserves
zerohood (via the proven conjugate symmetry plus the functional equation), the
critical strip, and the imaginary height. -/
theorem zetaInvolution_mem_fiberFinset {γ : ℝ} {s : ℂ}
    (hs : s ∈ fiberFinset γ) : zetaInvolution s ∈ fiberFinset γ := by
  rw [mem_fiberFinset] at hs ⊢
  obtain ⟨hz, hpos, hlt, him⟩ := hs
  refine ⟨involution_maps_strip_zeros stripConjugateZeroSymmetry_proved ⟨hpos, hlt⟩ hz,
    (zetaInvolution_preserves_strip ⟨hpos, hlt⟩).1,
    (zetaInvolution_preserves_strip ⟨hpos, hlt⟩).2, ?_⟩
  simp only [zetaInvolution, Complex.sub_im, Complex.one_im, Complex.conj_im,
    zero_sub, neg_neg]
  exact him

/-- **First-moment vanishing.** The signed deviations of the fiber's real parts
about `1/2` sum to zero. -/
theorem fiber_sum_re_sub_half_eq_zero (γ : ℝ) :
    ∑ s ∈ fiberFinset γ, (s.re - 1 / 2) = 0 := by
  apply Finset.sum_involution (fun s _ => zetaInvolution s)
  · -- pairs cancel: (Re s − 1/2) + (Re (1−s̄) − 1/2) = 0
    intro a _
    have hre : (zetaInvolution a).re = 1 - a.re := by
      simp only [zetaInvolution, Complex.sub_re, Complex.one_re, Complex.conj_re]
    rw [hre]; ring
  · -- a nonzero deviation means a is not a fixed point
    intro a _ hfa hfix
    apply hfa
    have : a.re = 1 / 2 := (zetaInvolution_fixed_iff_re_eq_half a).mp hfix
    rw [this]; ring
  · -- the involution maps the fiber to itself
    intro a ha
    exact zetaInvolution_mem_fiberFinset ha
  · -- the involution is an involution
    intro a _
    exact zetaInvolution_involutive a

/-- The sum of real parts over a fiber equals `(#fiber) · (1/2)`. -/
theorem fiber_sum_re (γ : ℝ) :
    ∑ s ∈ fiberFinset γ, s.re = (fiberFinset γ).card * (1 / 2) := by
  have h := fiber_sum_re_sub_half_eq_zero γ
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at h
  linarith

/-- **The fiber centroid is exactly `1/2`** (unconditional, for any nonempty
height-fiber). -/
theorem fiber_centroid_eq_half (γ : ℝ) (h : (fiberFinset γ).Nonempty) :
    (∑ s ∈ fiberFinset γ, s.re) / (fiberFinset γ).card = 1 / 2 := by
  have hcard : ((fiberFinset γ).card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr h
  rw [fiber_sum_re]
  field_simp

/-! ### Cardinality bridge to the energy criterion -/

/-- If a height-fiber has at most one zero, its energy vanishes. The proof uses
the unconditional centroid identity: a singleton fiber with centroid `1/2` must
sit on the critical line. -/
theorem fiberEnergy_eq_zero_of_fiber_card_le_one (γ : ℝ)
    (hcard : (fiberFinset γ).card ≤ 1) : fiberEnergy γ = 0 := by
  rw [fiberEnergy_eq_zero_iff]
  intro s hs
  have hsF : s ∈ fiberFinset γ := mem_fiberFinset.mpr hs
  have huniq : ∀ t ∈ fiberFinset γ, t = s := by
    intro t ht
    exact (Finset.card_le_one.mp hcard) t ht s hsF
  have hsum : ∑ x ∈ fiberFinset γ, (x.re - 1 / 2) = s.re - 1 / 2 := by
    calc
      ∑ x ∈ fiberFinset γ, (x.re - 1 / 2)
          = ∑ x ∈ fiberFinset γ, (s.re - 1 / 2) := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              rw [huniq x hx]
      _ = (fiberFinset γ).card * (s.re - 1 / 2) := by
              rw [Finset.sum_const, nsmul_eq_mul]
      _ = 1 * (s.re - 1 / 2) := by
              have hcard_pos : 0 < (fiberFinset γ).card := Finset.card_pos.mpr ⟨s, hsF⟩
              have hcard_eq : (fiberFinset γ).card = 1 := by omega
              rw [hcard_eq]
              norm_num
      _ = s.re - 1 / 2 := by ring
  have hzero := fiber_sum_re_sub_half_eq_zero γ
  rw [hsum] at hzero
  linarith

/-- A cardinality version of the uniqueness route: if every height-fiber has at
most one critical-strip zero, then RH follows. -/
theorem riemannHypothesis_of_all_fiber_card_le_one
    (hcard : ∀ γ : ℝ, (fiberFinset γ).card ≤ 1) : RiemannHypothesis := by
  rw [riemannHypothesis_iff_forall_fiberEnergy_zero]
  intro γ
  exact fiberEnergy_eq_zero_of_fiber_card_le_one γ (hcard γ)

end Reinmann
