/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.ToeplitzPrescribedAtom

/-! # The exact finite-data uniqueness boundary for positive Toeplitz matrices

Singular matrices have unique supported data; every full-rank case has distinct supports.
This is shared finite linear algebra, not an arithmetic PSD estimate.
-/

noncomputable section

namespace Reinmann.ToeplitzFullRank

open Matrix Polynomial Reinmann.ToeplitzKernel Reinmann.ToeplitzAtomic
  Reinmann.ToeplitzExtension Reinmann.ToeplitzDowndate
  Reinmann.ToeplitzPrescribedAtom Reinmann.ToeplitzUniqueness
open scoped ComplexOrder

lemma unit_node_not_mem (s : Finset ℂ) : ∃ z : ℂ, ‖z‖ = 1 ∧ z ∉ s := by
  let f : ℝ → ℂ := fun x => star ((x : ℂ) - Complex.I) / ((x : ℂ) - Complex.I)
  have hd (x : ℝ) : (x : ℂ) - Complex.I ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi
  have hn (x : ℝ) : ‖f x‖ = 1 := by
    dsimp only [f]
    rw [norm_div, norm_star, div_self (norm_ne_zero_iff.mpr (hd x))]
  have hi : Function.Injective f := by
    intro x y h
    have hc := (div_eq_div_iff (hd x) (hd y)).mp h
    have hs (x : ℝ) : star ((x : ℂ) - Complex.I) = (x : ℂ) + Complex.I := by simp
    rw [hs x, hs y] at hc
    have him := congrArg Complex.im hc
    simp [Complex.mul_im] at him
    linarith
  obtain ⟨z, ⟨x, rfl⟩, hz⟩ := (Set.infinite_range_of_injective hi).exists_notMem_finset s
  exact ⟨f x, hn x, hz⟩

/-- Every full-rank PSD Toeplitz matrix has two positive rank-sized representations
with distinct supports. -/
theorem nonunique_of_full_rank {n : ℕ}
    {T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hpsd : T.PosSemidef) (htoe : IsToeplitz T) (hrank : T.rank = n + 1) :
    ∃ s t : Finset ℂ, ∃ w v : ℂ → ℝ,
      s.card = T.rank ∧ t.card = T.rank ∧ s ≠ t ∧
      (∀ z ∈ s, ‖z‖ = 1 ∧ 0 < w z) ∧ (∀ z ∈ t, ‖z‖ = 1 ∧ 0 < v z) ∧
      T = atomicMatrix n s w ∧ T = atomicMatrix n t v := by
  obtain ⟨s, w, hs, hnodes, hentries⟩ :=
    ToeplitzRepresentation.exists_atomic_representation hpsd htoe
  have hsT : T = atomicMatrix n s w := by
    ext i j
    exact hentries i j
  obtain ⟨z, hz, hznot⟩ := unit_node_not_mem s
  obtain ⟨t, v, ht, hzt, hnodes', htT⟩ :=
    exists_representation_containing (posDef_of_full_rank hpsd hrank) htoe hz
  have hne : s ≠ t := by
    intro h
    apply hznot
    rw [h]
    exact hzt
  exact ⟨s, t, w, v, hs, ht, hne, hnodes, hnodes', hsT, htT⟩

/-- Uniqueness of finite positive unit-circle data, modulo arbitrary off-support values. -/
def HasUniquePositiveAtomicData {n : ℕ}
    (T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : Prop :=
  ∀ (s t : Finset ℂ) (w v : ℂ → ℝ),
    (∀ z ∈ s, ‖z‖ = 1 ∧ 0 < w z) → (∀ z ∈ t, ‖z‖ = 1 ∧ 0 < v z) →
    T = atomicMatrix n s w → T = atomicMatrix n t v →
      s = t ∧ ∀ z ∈ s, w z = v z

/-- For PSD Toeplitz matrices, supported finite positive data are unique exactly
in the singular case. The general existence theorem prevents vacuous uniqueness. -/
theorem unique_supported_data_iff_singular {n : ℕ}
    {T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hpsd : T.PosSemidef) (htoe : IsToeplitz T) :
    HasUniquePositiveAtomicData T ↔ T.rank ≤ n := by
  constructor
  · intro h
    by_contra hnot
    have hrank : T.rank = n + 1 := by
      have hb := T.rank_le_width
      omega
    obtain ⟨s, t, w, v, _, _, hne, hs, ht, hsT, htT⟩ :=
      nonunique_of_full_rank hpsd htoe hrank
    exact hne (h s t w v hs ht hsT htT).1
  · intro hrank
    obtain ⟨r, u, _, _, _, huni⟩ :=
      exists_unique_atomic_representation_singular hpsd htoe hrank
    intro s t w v hs ht hsT htT
    obtain ⟨hrs, hws⟩ := huni s w (fun z hz => (hs z hz).2) hsT
    obtain ⟨hrt, hwt⟩ := huni t v (fun z hz => (ht z hz).2) htT
    refine ⟨hrs.symm.trans hrt, ?_⟩
    intro z hz
    have hzr : z ∈ r := by rw [hrs]; exact hz
    exact (hws z hzr).symm.trans (hwt z hzr)

end Reinmann.ToeplitzFullRank
