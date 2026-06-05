/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.RiemannSpine
import Reinmann.ZeroFiberFiniteness
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.GroupWithZero.Basic

/-!
# A Spectral-Energy (Order-Parameter) Criterion for RH

## Idea, and where it comes from

In statistical mechanics the location of partition-function zeros is controlled
by an **order parameter** that vanishes exactly in the symmetric phase
(Lee–Yang theory). In electrostatics, a balanced charge configuration has zero
second moment about its axis of symmetry.

We import that picture. We already proved two unconditional facts:

* each imaginary height `γ` carries only **finitely many** critical-strip zeros
  (`finite_strip_zeros_at_height`); and
* the fiber is symmetric about the line `Re = 1/2`.

So each fiber is a finite cloud of charges symmetric about the critical line.
Define its **energy** (second moment about `Re = 1/2`)

  `fiberEnergy γ = ∑_{s : ζ s = 0, 0 < Re s < 1, Im s = γ} (Re s − 1/2)²`.

This is a finite, nonnegative real number. The Riemann Hypothesis is **exactly**
the statement that every fiber sits in its ground state, `fiberEnergy γ = 0`.

## Honest status

This is a *reformulation*, proved equivalent to RH — not a proof of RH. Because
`RiemannHypothesis ↔ ZeroImUniqueness` is already established, every
back-calculated sufficient condition is necessarily `≥ RH` in strength; a true
equivalence like this one relocates the difficulty into showing the energy
vanishes, which is itself RH. Its value is as a clean, finitely-supported,
physically interpretable target with manifest nonnegativity.
-/

noncomputable section

open Complex
open scoped BigOperators

namespace Reinmann

/-- The set of critical-strip zeros at imaginary height `γ`. -/
def fiberSet (γ : ℝ) : Set ℂ :=
  {s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ s.im = γ}

/-- The fiber at height `γ` as a `Finset` (it is finite, unconditionally). -/
def fiberFinset (γ : ℝ) : Finset ℂ :=
  (finite_strip_zeros_at_height γ).toFinset

@[simp]
theorem mem_fiberFinset {γ : ℝ} {s : ℂ} :
    s ∈ fiberFinset γ ↔ s ∈ fiberSet γ :=
  Set.Finite.mem_toFinset _

/-- The **spectral energy** of the height-`γ` fiber: its second moment about the
critical line `Re = 1/2`. -/
def fiberEnergy (γ : ℝ) : ℝ :=
  ∑ s ∈ fiberFinset γ, (s.re - 1 / 2) ^ 2

/-- The spectral energy is always nonnegative (a sum of squares). -/
theorem fiberEnergy_nonneg (γ : ℝ) : 0 ≤ fiberEnergy γ :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The energy of a fiber vanishes iff every zero at that height lies on the
critical line. -/
theorem fiberEnergy_eq_zero_iff (γ : ℝ) :
    fiberEnergy γ = 0 ↔ ∀ s ∈ fiberSet γ, s.re = 1 / 2 := by
  unfold fiberEnergy
  rw [Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _]
  constructor
  · intro h s hs
    have hmem : s ∈ fiberFinset γ := mem_fiberFinset.mpr hs
    have := h s hmem
    have hsub : s.re - 1 / 2 = 0 := by
      exact sq_eq_zero_iff.mp this
    linarith
  · intro h s hmem
    have hs : s ∈ fiberSet γ := mem_fiberFinset.mp hmem
    have hre : s.re = 1 / 2 := h s hs
    rw [hre]
    ring

/-- **Spectral-energy criterion for RH.**
The Riemann Hypothesis holds iff every height-fiber is in its ground state. -/
theorem riemannHypothesis_iff_forall_fiberEnergy_zero :
    RiemannHypothesis ↔ ∀ γ : ℝ, fiberEnergy γ = 0 := by
  rw [← criticalStripObligations_iff_riemannHypothesis]
  constructor
  · intro h γ
    rw [fiberEnergy_eq_zero_iff]
    rintro s ⟨hz, hpos, hlt, _⟩
    exact h.strip_zero_on_line s hpos hlt hz
  · intro h
    refine ⟨?_⟩
    intro s hpos hlt hz
    have hfib : ∀ t ∈ fiberSet s.im, t.re = 1 / 2 :=
      (fiberEnergy_eq_zero_iff s.im).mp (h s.im)
    exact hfib s ⟨hz, hpos, hlt, rfl⟩

/-- Equivalent global form: the total spectral energy summed over any finite set
of heights vanishes iff each fiber does. (Convenience corollary.) -/
theorem fiberEnergy_zero_of_riemannHypothesis (hrh : RiemannHypothesis) (γ : ℝ) :
    fiberEnergy γ = 0 :=
  (riemannHypothesis_iff_forall_fiberEnergy_zero.mp hrh) γ

end Reinmann
