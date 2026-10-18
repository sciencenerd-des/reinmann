/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.SplitPairCauchyTail
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Order.Filter.Finite

/-! Patch finitely many actual simple-pole germs into one analytic remainder.
This standalone construction does not change any PF implies RH bridge. -/
noncomputable section
namespace Reinmann.SplitPairPatchedRemainder
open Set Filter Finset
open scoped Topology

/-- Finite patching at distinct points, retaining the exact function away from them. -/
theorem patch_finite_germs {ι : Type*} [Fintype ι] (a : ι → ℂ)
    (ha : Function.Injective a) (f : ℂ → ℂ) (germ : ι → ℂ → ℂ) (S : Set ℂ)
    (hg : ∀ i, AnalyticAt ℂ (germ i) (a i))
    (heq : ∀ i z, z ≠ a i → f z = germ i z)
    (hf : ∀ z ∈ S, (∀ i, z ≠ a i) → AnalyticAt ℂ f z) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g S ∧
      (∀ z, (∀ i, z ≠ a i) → g z = f z) ∧ (∀ i, g (a i) = germ i (a i)) := by
  classical
  let g := Function.extend a (fun i => germ i (a i)) f
  have hga (i : ι) : g (a i) = germ i (a i) := ha.extend_apply _ _ i
  have hgf (z : ℂ) (hz : ∀ i, z ≠ a i) : g z = f z :=
    Function.extend_apply' _ _ _ (by rintro ⟨i, hi⟩; exact hz i hi.symm)
  refine ⟨g, ?_, hgf, hga⟩
  intro z hz
  by_cases hza : ∃ i, z = a i
  · obtain ⟨i, rfl⟩ := hza
    apply (hg i).congr
    have hex : ∀ᶠ w in 𝓝 (a i), ∀ j, j ≠ i → w ≠ a j := by
      apply eventually_all.mpr
      intro j
      by_cases hji : j = i
      · exact Eventually.of_forall (by simp [hji])
      · exact (eventually_ne_nhds (ha.ne (Ne.symm hji))).mono (fun _ hw _ => hw)
    filter_upwards [hex] with w hw
    by_cases hwi : w = a i
    · subst w; exact (hga i).symm
    · have hall : ∀ j, w ≠ a j := by
        intro j
        by_cases hji : j = i
        · simpa [hji] using hwi
        · exact hw j hji
      rw [hgf w hall, heq i w hwi]
  · have hall : ∀ i, z ≠ a i := by simpa only [not_exists] using hza
    apply (hf z hz hall).congr
    have hex : ∀ᶠ w in 𝓝 z, ∀ i, w ≠ a i :=
      eventually_all.mpr (fun i => eventually_ne_nhds (hall i))
    filter_upwards [hex] with w hw
    exact (hgf w hw).symm

/-- All the chosen principal parts are removed from one common reciprocal.
The zero-set hypothesis is local to S; multiplicities outside S are irrelevant. -/
theorem actual_simple_pole_remainder {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : ℂ → ℂ} (hF : Differentiable ℂ F) (a : ι → ℂ)
    (ha : Function.Injective a) (hzero : ∀ i, F (a i) = 0)
    (hsimple : ∀ i, deriv F (a i) ≠ 0) (S : Set ℂ)
    (hall : ∀ z ∈ S, F z = 0 → ∃ i, z = a i) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g S ∧
      ∀ z, (∀ i, z ≠ a i) →
        (F z)⁻¹ = (∑ i, (deriv F (a i))⁻¹ / (z - a i)) + g z := by
  classical
  choose germ hg heq using fun i => SplitPairCauchyTail.simple_pole_analytic_remainder
    hF (hzero i) (hsimple i)
  let P : ι → ℂ → ℂ := fun i z => (deriv F (a i))⁻¹ / (z - a i)
  let raw : ℂ → ℂ := fun z => (F z)⁻¹ - ∑ i, P i z
  let localGerm : ι → ℂ → ℂ := fun i z => germ i z - ∑ j ∈ univ.erase i, P j z
  have hlocal (i : ι) : AnalyticAt ℂ (localGerm i) (a i) := by
    apply (hg i).sub
    apply Finset.analyticAt_fun_sum
    intro j hj
    apply analyticAt_const.div (analyticAt_id.sub analyticAt_const)
    exact sub_ne_zero.mpr (ha.ne (mem_erase.mp hj).1.symm)
  have hmatch (i : ι) (z : ℂ) (hz : z ≠ a i) : raw z = localGerm i z := by
    dsimp [raw, localGerm]
    rw [← heq i z hz]
    have h := sum_erase_add univ (fun j => P j z) (mem_univ i)
    dsimp [P] at *
    rw [← h]
    ring
  have hraw (z : ℂ) (hz : z ∈ S) (hn : ∀ i, z ≠ a i) : AnalyticAt ℂ raw z := by
    have hFz : F z ≠ 0 := by
      intro h
      obtain ⟨i, hi⟩ := hall z hz h
      exact hn i hi
    apply ((hF.analyticAt z).inv hFz).sub
    apply Finset.analyticAt_fun_sum
    intro i _
    exact analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr (hn i))
  obtain ⟨g, hgS, hgf, _⟩ := patch_finite_germs a ha raw localGerm S hlocal hmatch hraw
  refine ⟨g, hgS, ?_⟩
  intro z hz
  rw [hgf z hz]
  dsimp [raw, P]
  ring

end Reinmann.SplitPairPatchedRemainder
