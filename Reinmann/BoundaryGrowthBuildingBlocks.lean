/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.RiemannSpine
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Analytic Building Blocks for a Zero-Free Region (Experiment b)

The de la Vallée Poussin *strip* region (`Re > 1 - c/log|t|`) is assembled from the
3-4-1 modulus inequality (already proved, `zeta_341_modulus`) plus two analytic
inputs about the size of `ζ`:

* the **pole growth** of `ζ` at `s = 1` (the `+3` side of the cubed factor); and
* the **local vanishing** of `ζ` at a hypothetical zero (the `-4` side).

This file formalizes those two ingredients as reusable lemmas, directly from
Mathlib's residue and the derivative.

* `norm_riemannZeta_pole_growth`: `|σ-1| · ‖ζ(σ)‖ → 1` as `σ → 1⁺`.
* `riemannZeta_isBigO_sub_of_zero`: if `ζ p = 0` (`p ≠ 1`) then `ζ = O(· - p)` near
  `p` (linear vanishing).

## Honest status

These are the genuine analytic ingredients. The *line* `Re = 1` is already covered
by Mathlib (`riemannZeta_ne_zero_of_one_le_re`), so assembling these into the line
result would be vacuous. The genuinely *new* target — a quantitative region inside
the strip — additionally needs **Borel–Carathéodory / Hadamard three-circles**
growth bounds for `ζ` in vertical strips (Mathlib prerequisites M2–M4), which are a
separate major formalization. We provide the building blocks and name that gap.
-/

noncomputable section

open Complex Filter Topology

namespace Reinmann

/-- The map `σ ↦ (σ : ℂ)` sends `𝓝[>] 1` (reals) into `𝓝[≠] 1` (complex). -/
private theorem ofReal_tendsto_nhdsWithin_ne_one :
    Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨(continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  simp only [Set.mem_Ioi] at hσ
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  intro h
  have : (σ : ℝ) = 1 := by exact_mod_cast h
  linarith

/-- **Pole growth of `ζ` at `s = 1`.** `‖(σ-1)·ζ(σ)‖ → 1` as `σ → 1⁺`; equivalently
`ζ` blows up like `1/|σ-1|`. (From `riemannZeta_residue_one`.) -/
theorem norm_riemannZeta_pole_growth :
    Tendsto (fun σ : ℝ => ‖((σ : ℂ) - 1) * riemannZeta (σ : ℂ)‖)
      (𝓝[>] (1 : ℝ)) (𝓝 1) := by
  have h1 := riemannZeta_residue_one.comp ofReal_tendsto_nhdsWithin_ne_one
  have h2 := (continuous_norm.tendsto (1 : ℂ)).comp h1
  rw [norm_one] at h2
  exact h2

/-- **Local linear vanishing at a zero.** If `ζ p = 0` and `p ≠ 1`, then `ζ` is
`O(z - p)` near `p` (it vanishes at least linearly). (From the derivative.) -/
theorem riemannZeta_isBigO_sub_of_zero {p : ℂ} (hp : p ≠ 1)
    (hz : riemannZeta p = 0) :
    (fun z => riemannZeta z) =O[𝓝 p] (fun z => z - p) := by
  have h := (differentiableAt_riemannZeta hp).hasDerivAt.isBigO_sub
  simpa [hz] using h

end Reinmann
