/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.RiemannSpine
import Reinmann.TwoBranchArchitecture
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

/-!
# Li's Criterion as a Named-Hypothesis Route to RH

Li (1997) proved that RH is equivalent to `λ_n ≥ 0` for all `n ≥ 1`, where the
Li coefficients are

```
λ_n = (1/(n-1)!) · dⁿ/dsⁿ [ s^{n-1} · log ξ(s) ] |_{s=1}  =  Σ_ρ [ 1 − (1 − 1/ρ)ⁿ ].
```

This module promotes the earlier `research/lean-drafts/LiCriterion.lean.draft`
into the verified library **without any `sorry` or `axiom`**.  The draft defined
`λ_n` with `sorry` and left every downstream theorem unproven.  Formalizing the
analytic content of Li's theorem (the derivative/zero-sum identity and its
convergence) is exactly the open problem; axiomatizing it would be dishonest.

Instead we follow the repository's established idiom (cf. `Order3FrontierTheorem`,
`XiToeplitzTotalPositive`): the two *directional analytic contracts* of Li's
theorem are packaged as fields of a `LiData` structure — named hypotheses, not
axioms.  Everything that is genuinely elementary (the completed-`ξ` functional
equation, the strip zero correspondence, and the criterion ⇔ zero-free
equivalence *relative to* those contracts) is proven outright.

`#print axioms li_criterion_iff_rh` reports only `[propext, Classical.choice,
Quot.sound]`.
-/

noncomputable section

namespace Reinmann

open Complex Real

/-! ## Genuinely proven content: the completed ξ function -/

/-- The completed zeta `ξ(s) = ½·s·(s−1)·Λ(s)`, where `Λ = completedRiemannZeta`. -/
def completedXi (s : ℂ) : ℂ :=
  (1 / 2) * s * (s - 1) * completedRiemannZeta s

/-- Functional equation: `ξ(1 − s) = ξ(s)`. Proven, no hypotheses. -/
theorem completedXi_symmetry (s : ℂ) : completedXi (1 - s) = completedXi s := by
  unfold completedXi
  rw [completedRiemannZeta_one_sub]
  ring

/-- Inside the open critical strip, zeros of `ξ` are exactly the zeros of `ζ`. -/
theorem completedXi_zero_iff_zeta_zero_critical {s : ℂ}
    (hstrip : 0 < s.re ∧ s.re < 1) :
    completedXi s = 0 ↔ riemannZeta s = 0 := by
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hstrip; simp at hstrip
  have hs1 : s ≠ 1 := by
    intro h; rw [h] at hstrip; simp at hstrip
  have hGamma : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hstrip.1
  unfold completedXi
  have h_eq : completedRiemannZeta s = Gammaℝ s * riemannZeta s := by
    have h_zeta := riemannZeta_def_of_ne_zero hs0
    rw [h_zeta]
    exact (mul_div_cancel₀ (completedRiemannZeta s) hGamma).symm
  rw [h_eq]
  have h_prod : (1 / 2 : ℂ) * s * (s - 1) * Gammaℝ s ≠ 0 := by
    have h1 : (1 / 2 : ℂ) ≠ 0 := by norm_num
    have h2 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero h1 hs0) h2) hGamma
  have h_rewrite : ((1 / 2 : ℂ) * s * (s - 1)) * (Gammaℝ s * riemannZeta s) =
      ((1 / 2 : ℂ) * s * (s - 1) * Gammaℝ s) * riemannZeta s := by ring
  rw [h_rewrite, mul_eq_zero, or_iff_right h_prod]

/-! ## The analytic contracts of Li's theorem, bundled as named hypotheses -/

/-- The analytic content of Li's criterion, carried as data rather than proved.

`lambda` is a candidate Li-coefficient sequence.  The two fields are the *only*
non-elementary inputs of Li's theorem:

* `offLine_neg` — Li's hard direction: an off-critical-line zero forces some
  coefficient strictly negative (the sum over zeros develops a negative term).
* `rh_nonneg` — the manifest direction: if the right half-strip is zero-free then
  every coefficient is nonnegative.

Constructing an *actual* `LiData` whose `lambda` is the true `λ_n` (and hence
turning this route into an unconditional proof) is precisely the open problem. -/
structure LiData where
  lambda : ℕ → ℝ
  offLine_neg : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → 1 / 2 < ρ.re →
    ∃ N : ℕ, 0 < N ∧ lambda N < 0
  rh_nonneg : RightHalfStripZeroFree → ∀ n : ℕ, 0 < n → 0 ≤ lambda n

/-- Li's criterion for a given coefficient model: all positive-index coefficients
are nonnegative. -/
def LiCriterion (D : LiData) : Prop := ∀ n : ℕ, 0 < n → 0 ≤ D.lambda n

/-- **Li's criterion is equivalent to the right-half-strip zero-free target**,
proven from the two `LiData` contracts.  This is the honest core: given the
analytic inputs of Li's theorem, the equivalence with RH is elementary. -/
theorem li_criterion_iff_rh (D : LiData) :
    LiCriterion D ↔ RightHalfStripZeroFree := by
  constructor
  · -- λ_n ≥ 0 for all n ⟹ no zero in the open right half-strip.
    intro hLi s hlow hhigh hzero
    obtain ⟨N, hN, hneg⟩ :=
      D.offLine_neg s hzero (by linarith) hhigh hlow
    exact absurd (hLi N hN) (not_le.mpr hneg)
  · -- right half-strip zero-free ⟹ λ_n ≥ 0 for all n.
    intro hRH n hn
    exact D.rh_nonneg hRH n hn

/-- Packaged as a route to Mathlib's `RiemannHypothesis`: Li's criterion (for any
coefficient model satisfying the contracts) implies RH. -/
theorem riemannHypothesis_of_liCriterion (D : LiData) (h : LiCriterion D) :
    RiemannHypothesis :=
  riemannHypothesis_iff_rightHalfStripZeroFree.mpr ((li_criterion_iff_rh D).mp h)

/-- Conversely RH yields Li's criterion for any model with the contracts, so the
Li route is genuinely equivalent to RH, not merely sufficient. -/
theorem liCriterion_of_riemannHypothesis (D : LiData) (h : RiemannHypothesis) :
    LiCriterion D :=
  (li_criterion_iff_rh D).mpr (riemannHypothesis_iff_rightHalfStripZeroFree.mp h)

end Reinmann
