/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

/-! A unique tied boundary pair gives exactly two maximal subset products. -/
noncomputable section
namespace Reinmann.SplitPairModulusOrder
open Finset
variable {ι : Type*} [DecidableEq ι]

theorem boundary_product_gap (w : ι → ℝ) (hpos : ∀ i, 0 < w i)
    (S : Finset ι) (p q : ι) (_hp : p ∈ S) (hq : q ∉ S)
    (hmax : ∀ x ∈ S, ∀ y ∉ S, w y ≤ w x)
    (hequal : ∀ x ∈ S, ∀ y ∉ S, w y = w x → x = p ∧ y = q)
    (T : Finset ι) (hcard : T.card = S.card) (hne : T ≠ S)
    (hswap : T ≠ insert q (S.erase p)) :
    (∏ i ∈ T, w i) < ∏ i ∈ S, w i := by
  classical
  let D := S \ T
  let E := T \ S
  have hc : D.card = E.card := card_sdiff_comm hcard.symm
  let e : D ≃ E := Fintype.equivOfCardEq (by simpa using hc)
  have hD : D.Nonempty := by
    by_contra h
    have hempty : D = ∅ := not_nonempty_iff_eq_empty.mp h
    have hsub : S ⊆ T := sdiff_eq_empty_iff_subset.mp hempty
    exact hne (eq_of_subset_of_card_le hsub (by omega)).symm
  have hle (d : D) : w (e d).val ≤ w d.val :=
    hmax d.val (mem_sdiff.mp d.property).1 (e d).val (mem_sdiff.mp (e d).property).2
  have hstrict : ∃ d : D, w (e d).val < w d.val := by
    by_contra h
    push Not at h
    have hpq (d : D) : d.val = p ∧ (e d).val = q :=
      hequal d.val (mem_sdiff.mp d.property).1 (e d).val
        (mem_sdiff.mp (e d).property).2 (le_antisymm (hle d) (h d))
    obtain ⟨d, hd⟩ := hD
    let d0 : D := ⟨d, hd⟩
    have hpD : p ∈ D := by rw [← (hpq d0).1]; exact d0.property
    have hqE : q ∈ E := by rw [← (hpq d0).2]; exact (e d0).property
    have hdall (i : ι) (hi : i ∈ D) : i = p := (hpq ⟨i, hi⟩).1
    have heall (i : ι) (hi : i ∈ E) : i = q := by
      obtain ⟨d, hd⟩ := e.surjective ⟨i, hi⟩
      simpa only [hd] using (hpq d).2
    apply hswap
    ext i
    simp only [mem_insert, mem_erase]
    constructor
    · intro hi
      by_cases his : i ∈ S
      · right
        refine ⟨?_, his⟩
        intro hip
        subst i
        exact (mem_sdiff.mp hpD).2 hi
      · left
        exact heall i (mem_sdiff.mpr ⟨hi, his⟩)
    · rintro (rfl | ⟨hip, his⟩)
      · exact (mem_sdiff.mp hqE).1
      · by_contra hit
        exact hip (hdall i (mem_sdiff.mpr ⟨his, hit⟩))
  have hlt : (∏ d : D, w (e d).val) < ∏ d : D, w d.val := by
    apply Finset.prod_lt_prod
    · intro i _
      exact hpos _
    · intro i _
      exact hle i
    · obtain ⟨d, hd⟩ := hstrict
      exact ⟨d, mem_univ _, hd⟩
  have hde : (∏ d : D, w (e d).val) = ∏ i ∈ E, w i := by
    rw [← Finset.prod_coe_sort E w]
    exact e.prod_comp (fun i : E => w i.val)
  have hdd : (∏ d : D, w d.val) = ∏ i ∈ D, w i := Finset.prod_coe_sort D w
  rw [hde, hdd] at hlt
  have hcommon : 0 < ∏ i ∈ S ∩ T, w i := prod_pos (fun i _ => hpos i)
  have hs : (∏ i ∈ D, w i) * (∏ i ∈ S ∩ T, w i) = ∏ i ∈ S, w i := by
    have h := prod_sdiff (f := w) (inter_subset_left : S ∩ T ⊆ S)
    simpa [D] using h
  have ht : (∏ i ∈ E, w i) * (∏ i ∈ S ∩ T, w i) = ∏ i ∈ T, w i := by
    have h := prod_sdiff (f := w) (inter_subset_right : S ∩ T ⊆ T)
    simpa [E] using h
  rw [← hs, ← ht]
  exact mul_lt_mul_of_pos_right hlt hcommon

end Reinmann.SplitPairModulusOrder
