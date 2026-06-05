/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.RiemannSpine
import Reinmann.InvolutionSymmetry
import Reinmann.ConjugateHalfPlane
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Global Conjugate Symmetry of Riemann Zeta

This file closes the analytic-continuation gap left open by
`ConjugateHalfPlane.lean`. We prove the *global* conjugate symmetry

  `ζ(conj s) = conj (ζ s)` for all `s ≠ 1`

via the identity theorem for analytic functions, and use it to discharge the
`ConjugateSymmetry` and `StripConjugateZeroSymmetry` obligations as **theorems**
(rather than assumptions).

## Strategy

The reflected function `g s = conj (ζ (conj s))` is holomorphic on `{1}ᶜ`,
because `conj ∘ f ∘ conj` is holomorphic whenever `f` is
(`DifferentiableAt.conj_conj`). The genuine zeta function `ζ` is also analytic
on `{1}ᶜ` (`analyticOn_riemannZeta`). On the half-plane `1 < re s` we already
know `ζ(conj s) = conj (ζ s)`, equivalently `ζ s = g s`. Since `{1}ᶜ` is
preconnected and `g` agrees with `ζ` on an open neighbourhood of `s = 2`, the
identity theorem forces `ζ = g` on all of `{1}ᶜ`.
-/

noncomputable section

open Complex
open scoped ComplexConjugate

namespace Reinmann

/-- The complement of `{1}` in `ℂ` is preconnected (it is `ℂ` minus a point). -/
theorem compl_singleton_one_isPreconnected :
    IsPreconnected (({(1 : ℂ)} : Set ℂ)ᶜ) :=
  (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected

/-- The reflected zeta function `g s = conj (ζ (conj s))` is analytic on `{1}ᶜ`. -/
theorem reflectedZeta_analyticOnNhd :
    AnalyticOnNhd ℂ (fun s : ℂ => conj (riemannZeta (conj s))) (({(1 : ℂ)} : Set ℂ)ᶜ) := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_compl_singleton
  intro z hz
  have hz_ne : z ≠ 1 := by simpa using hz
  have hconj_ne : (starRingEnd ℂ) z ≠ 1 := by
    intro h
    apply hz_ne
    have := congrArg (starRingEnd ℂ) h
    simpa using this
  have hdiff : DifferentiableAt ℂ riemannZeta ((starRingEnd ℂ) z) :=
    differentiableAt_riemannZeta hconj_ne
  have hcc := hdiff.conj_conj
  rw [Complex.conj_conj] at hcc
  exact hcc.differentiableWithinAt

/-- **Global conjugate symmetry of the Riemann zeta function.**
For every `s ≠ 1`, `ζ(conj s) = conj (ζ s)`. -/
theorem riemannZeta_conj (s : ℂ) (hs : s ≠ 1) :
    riemannZeta (conj s) = conj (riemannZeta s) := by
  -- The reflected function.
  set g : ℂ → ℂ := fun z => conj (riemannZeta (conj z)) with hg_def
  -- `ζ` and `g` are analytic on `{1}ᶜ`.
  have hζ : AnalyticOnNhd ℂ riemannZeta (({(1 : ℂ)} : Set ℂ)ᶜ) := analyticOn_riemannZeta
  have hg : AnalyticOnNhd ℂ g (({(1 : ℂ)} : Set ℂ)ᶜ) := reflectedZeta_analyticOnNhd
  -- They agree on a neighbourhood of `2` (the open half-plane `1 < re`).
  have hfg : riemannZeta =ᶠ[nhds (2 : ℂ)] g := by
    refine Filter.eventuallyEq_of_mem
      (s := {s : ℂ | 1 < s.re})
      (one_lt_re_halfPlane_isOpen.mem_nhds (by norm_num)) ?_
    intro z hz
    simp only [Set.mem_setOf_eq] at hz
    have hzz : riemannZeta (conj z) = conj (riemannZeta z) :=
      riemannZeta_conj_of_one_lt_re z hz
    change riemannZeta z = conj (riemannZeta (conj z))
    rw [hzz, Complex.conj_conj]
  -- Identity theorem: `ζ = g` on the whole punctured plane.
  have h2mem : (2 : ℂ) ∈ (({(1 : ℂ)} : Set ℂ)ᶜ) := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    norm_num
  have hEq : Set.EqOn riemannZeta g (({(1 : ℂ)} : Set ℂ)ᶜ) :=
    hζ.eqOn_of_preconnected_of_eventuallyEq hg
      compl_singleton_one_isPreconnected h2mem hfg
  -- Evaluate at `conj s`.
  have hconj_mem : (starRingEnd ℂ) s ∈ (({(1 : ℂ)} : Set ℂ)ᶜ) := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    apply hs
    have := congrArg (starRingEnd ℂ) h
    simpa using this
  have hval := hEq hconj_mem
  -- `hval : ζ (conj s) = conj (ζ (conj (conj s)))`
  rw [hg_def] at hval
  simpa [Complex.conj_conj] using hval

/-- The global `ConjugateSymmetry` obligation is now a theorem. -/
theorem conjugateSymmetry_proved : ConjugateSymmetry := by
  intro s hs
  exact riemannZeta_conj s hs

/-- Consequently the strip-level zero conjugate symmetry is a theorem. -/
theorem stripConjugateZeroSymmetry_proved : StripConjugateZeroSymmetry :=
  stripConjugateZeroSymmetry_of_conjugateSymmetry conjugateSymmetry_proved

end Reinmann
