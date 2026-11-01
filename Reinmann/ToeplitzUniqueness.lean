/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.ToeplitzRepresentation

/-! # Uniqueness and its rank boundary for finite Toeplitz atoms

Shared finite linear algebra, in the original entry and coefficient conventions.
-/

noncomputable section

namespace Reinmann.ToeplitzUniqueness

open Matrix Polynomial Reinmann.ToeplitzKernel Reinmann.ToeplitzAtomic
  Reinmann.ToeplitzExtension
open scoped ComplexOrder

lemma eval_coeff_sum {n : ℕ} {q : ℂ[X]} (hq : q.natDegree ≤ n) (z : ℂ) :
    (∑ j : Fin (n + 1), q.coeff j * z ^ (j : ℕ)) = q.eval z :=
  (Fin.sum_univ_eq_sum_range (fun j : ℕ => q.coeff j * z ^ j) (n + 1)).trans
    (eval_eq_sum_range' (by omega : q.natDegree < n + 1) z).symm

lemma mulVec_atomic_coeff {n : ℕ} (s : Finset ℂ) (w : ℂ → ℝ)
    {q : ℂ[X]} (hq : q.natDegree ≤ n) (i : Fin (n + 1)) :
    (atomicMatrix n s w *ᵥ coeffVec n q) i =
      ∑ z ∈ s, (w z : ℂ) * star (z ^ (i : ℕ)) * q.eval z := by
  simp only [mulVec, dotProduct, atomicMatrix, coeffVec]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  calc
    _ = ((w z : ℂ) * star (z ^ (i : ℕ))) *
        ∑ j : Fin (n + 1), q.coeff j * z ^ (j : ℕ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by rw [eval_coeff_sum hq]

lemma energy_atomicMatrix {n : ℕ} (s : Finset ℂ) (w : ℂ → ℝ)
    {q : ℂ[X]} (hq : q.natDegree ≤ n) :
    energy (atomicMatrix n s w) (coeffVec n q) =
      ∑ z ∈ s, (w z : ℂ) * star (q.eval z) * q.eval z := by
  change (∑ i : Fin (n + 1), star (q.coeff i) *
    (atomicMatrix n s w *ᵥ coeffVec n q) i) = _
  simp_rw [mulVec_atomic_coeff s w hq, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  calc
    _ = ((w z : ℂ) * q.eval z) *
        star (∑ i : Fin (n + 1), q.coeff i * z ^ (i : ℕ)) := by
      rw [star_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [star_mul]
      ring
    _ = _ := by rw [eval_coeff_sum hq]; ring

lemma energy_atomicMatrix_re {n : ℕ} (s : Finset ℂ) (w : ℂ → ℝ)
    {q : ℂ[X]} (hq : q.natDegree ≤ n) :
    (energy (atomicMatrix n s w) (coeffVec n q)).re =
      ∑ z ∈ s, w z * ‖q.eval z‖ ^ 2 := by
  rw [energy_atomicMatrix s w hq]
  have hr (z : ℂ) : (w z : ℂ) * star (q.eval z) * q.eval z =
      ((w z * ‖q.eval z‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_eq_conj_mul_self]
    rw [starRingEnd_apply]
    ring
  simp_rw [hr]
  rw [← Complex.ofReal_sum, Complex.ofReal_re]

/-- Strictly positive atomic weights force every kernel polynomial to vanish on the support. -/
theorem eval_zero_of_kernel {n : ℕ} (s : Finset ℂ) (w : ℂ → ℝ)
    (hw : ∀ z ∈ s, 0 < w z) {q : ℂ[X]} (hq : q.natDegree ≤ n)
    (hk : atomicMatrix n s w *ᵥ coeffVec n q = 0) :
    ∀ z ∈ s, q.eval z = 0 := by
  have he : (∑ z ∈ s, w z * ‖q.eval z‖ ^ 2) = 0 := by
    rw [← energy_atomicMatrix_re s w hq]
    simp [energy, hk]
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun z hz =>
    mul_nonneg (hw z hz).le (sq_nonneg _))).mp he
  intro z hzs
  have hterm := hz z hzs
  have hsq := (mul_eq_zero.mp hterm).resolve_left (ne_of_gt (hw z hzs))
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hsq)

lemma support_subset_of_card_le {n : ℕ} {s t : Finset ℂ} {w v : ℂ → ℝ}
    (hs : s.card ≤ n) (hv : ∀ z ∈ t, 0 < v z)
    (heq : atomicMatrix n s w = atomicMatrix n t v) : t ⊆ s := by
  let q := Lagrange.nodal s id
  have hq : q.natDegree ≤ n := by rw [Lagrange.natDegree_nodal]; exact hs
  have hk : atomicMatrix n t v *ᵥ coeffVec n q = 0 := by
    rw [← heq]
    apply atomicMatrix_kernel s w hq
    intro z hz
    simpa only [id_eq] using (Lagrange.eval_nodal_at_node (v := id) hz)
  have hz := eval_zero_of_kernel t v hv hq hk
  intro z hzt
  have hprod : (∏ x ∈ s, (z - x)) = 0 := by
    simpa only [q, Lagrange.eval_nodal, id_eq] using hz z hzt
  obtain ⟨x, hxs, hzx⟩ := Finset.prod_eq_zero_iff.mp hprod
  rw [sub_eq_zero.mp hzx]
  exact hxs

/-- Positive representations with at most n atoms have identical supports. -/
theorem support_eq_of_card_le {n : ℕ} {s t : Finset ℂ} {w v : ℂ → ℝ}
    (hs : s.card ≤ n) (ht : t.card ≤ n)
    (hw : ∀ z ∈ s, 0 < w z) (hv : ∀ z ∈ t, 0 < v z)
    (heq : atomicMatrix n s w = atomicMatrix n t v) : s = t := by
  apply Finset.Subset.antisymm
  · exact support_subset_of_card_le ht hw heq.symm
  · exact support_subset_of_card_le hs hv heq

lemma first_row_lagrange {n : ℕ} {s : Finset ℂ} (w : ℂ → ℝ)
    (hs : s.card ≤ n + 1) {z : ℂ} (hz : z ∈ s) :
    (atomicMatrix n s w *ᵥ coeffVec n (Lagrange.basis s id z)) 0 = (w z : ℂ) := by
  have hd : (Lagrange.basis s id z).natDegree ≤ n := by
    rw [Lagrange.natDegree_basis (v := id) (fun _ _ _ _ h => h) hz]
    have hp : 0 < s.card := Finset.card_pos.mpr ⟨z, hz⟩
    omega
  rw [mulVec_atomic_coeff s w hd]
  simp only [Fin.val_zero, pow_zero, star_one, mul_one]
  rw [Finset.sum_eq_single z]
  · have he : (Lagrange.basis s id z).eval z = 1 := by
      simpa only [id_eq] using
        (Lagrange.eval_basis_self (v := id) (fun _ _ _ _ h => h) hz)
    rw [he, mul_one]
  · intro x hx hxz
    have he : (Lagrange.basis s id z).eval x = 0 := by
      simpa only [id_eq] using (Lagrange.eval_basis_of_ne (v := id) (Ne.symm hxz) hx)
    rw [he, mul_zero]
  · intro h
    exact (h hz).elim

/-- On a fixed support of at most n+1 nodes, the weights are determined by the moments.
No positivity or unit-circle hypothesis is needed for this recovery statement. -/
theorem weights_eq_on_support {n : ℕ} {s : Finset ℂ} {w v : ℂ → ℝ}
    (hs : s.card ≤ n + 1) (heq : atomicMatrix n s w = atomicMatrix n s v) :
    ∀ z ∈ s, w z = v z := by
  intro z hz
  have hm := congrArg (fun T => (T *ᵥ coeffVec n (Lagrange.basis s id z)) 0) heq
  dsimp only at hm
  rw [first_row_lagrange w hs hz, first_row_lagrange v hs hz] at hm
  exact Complex.ofReal_injective hm

lemma first_row_lagrange_subset {n : ℕ} {s t : Finset ℂ} (v : ℂ → ℝ)
    (hs : s.card ≤ n + 1) (ht : t ⊆ s) {z : ℂ} (hz : z ∈ s) :
    (atomicMatrix n t v *ᵥ coeffVec n (Lagrange.basis s id z)) 0 =
      if z ∈ t then (v z : ℂ) else 0 := by
  have hd : (Lagrange.basis s id z).natDegree ≤ n := by
    rw [Lagrange.natDegree_basis (v := id) (fun _ _ _ _ h => h) hz]
    have hp : 0 < s.card := Finset.card_pos.mpr ⟨z, hz⟩
    omega
  rw [mulVec_atomic_coeff t v hd]
  simp only [Fin.val_zero, pow_zero, star_one, mul_one]
  by_cases hzt : z ∈ t
  · rw [if_pos hzt, Finset.sum_eq_single z]
    · have he : (Lagrange.basis s id z).eval z = 1 := by
        simpa only [id_eq] using
          (Lagrange.eval_basis_self (v := id) (fun _ _ _ _ h => h) hz)
      rw [he, mul_one]
    · intro x hx hxz
      have he : (Lagrange.basis s id z).eval x = 0 := by
        simpa only [id_eq] using
          (Lagrange.eval_basis_of_ne (v := id) (Ne.symm hxz) (ht hx))
      rw [he, mul_zero]
    · intro h
      exact (h hzt).elim
  · rw [if_neg hzt]
    apply Finset.sum_eq_zero
    intro x hx
    have hxz : z ≠ x := by
      intro h
      exact hzt (h.symm ▸ hx)
    have he : (Lagrange.basis s id z).eval x = 0 := by
      simpa only [id_eq] using (Lagrange.eval_basis_of_ne (v := id) hxz (ht hx))
    rw [he, mul_zero]

/-- One positive representation with at most n nodes fixes every positive finite competitor.
The competing support needs no cardinality bound. -/
theorem representation_unique_of_card_le {n : ℕ} {s t : Finset ℂ} {w v : ℂ → ℝ}
    (hs : s.card ≤ n) (hw : ∀ z ∈ s, 0 < w z) (hv : ∀ z ∈ t, 0 < v z)
    (heq : atomicMatrix n s w = atomicMatrix n t v) :
    s = t ∧ ∀ z ∈ s, w z = v z := by
  have hts := support_subset_of_card_le hs hv heq
  have hst : s = t := by
    apply Finset.Subset.antisymm ?_ hts
    intro z hz
    by_contra hzt
    have hm := congrArg (fun T => (T *ᵥ coeffVec n (Lagrange.basis s id z)) 0) heq
    dsimp only at hm
    rw [first_row_lagrange w (hs.trans (Nat.le_succ n)) hz,
      first_row_lagrange_subset v (hs.trans (Nat.le_succ n)) hts hz, if_neg hzt] at hm
    have hwz : w z = 0 := Complex.ofReal_injective (by simpa only [Complex.ofReal_zero] using hm)
    exact (ne_of_gt (hw z hz)) hwz
  subst t
  exact ⟨rfl, weights_eq_on_support (hs.trans (Nat.le_succ n)) heq⟩

/-- A singular rank-sized positive reference fixes support and weights of every positive
finite competitor. Off-support values of weight functions are not compared. -/
theorem representation_unique_singular {n : ℕ}
    {T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hrank : T.rank ≤ n)
    {s t : Finset ℂ} {w v : ℂ → ℝ} (hs : s.card = T.rank)
    (hw : ∀ z ∈ s, 0 < w z) (hv : ∀ z ∈ t, 0 < v z)
    (hsT : T = atomicMatrix n s w) (htT : T = atomicMatrix n t v) :
    s = t ∧ ∀ z ∈ s, w z = v z :=
  representation_unique_of_card_le (by omega) hw hv (hsT.symm.trans htT)

/-- Singular PSD Toeplitz matrices have positive atomic data whose support and supported
weights are unique among all positive finite representations. -/
theorem exists_unique_atomic_representation_singular {n : ℕ}
    {T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hpsd : T.PosSemidef) (htoe : IsToeplitz T) (hrank : T.rank ≤ n) :
    ∃ s : Finset ℂ, ∃ w : ℂ → ℝ,
      s.card = T.rank ∧ (∀ z ∈ s, ‖z‖ = 1 ∧ 0 < w z) ∧
      T = atomicMatrix n s w ∧
      ∀ (t : Finset ℂ) (v : ℂ → ℝ),
        (∀ z ∈ t, 0 < v z) → T = atomicMatrix n t v →
          s = t ∧ ∀ z ∈ s, w z = v z := by
  obtain ⟨s, w, hcard, hnodes, hentries⟩ :=
    ToeplitzRepresentation.exists_atomic_representation hpsd htoe
  have heq : T = atomicMatrix n s w := by
    ext i j
    exact hentries i j
  refine ⟨s, w, hcard, hnodes, heq, ?_⟩
  intro t v hv ht
  exact representation_unique_singular hrank hcard (fun z hz => (hnodes z hz).2) hv heq ht

/-- Full rank does not admit an unconditional support-uniqueness theorem:
the one-by-one identity has distinct one-atom representations at 1 and -1. -/
theorem full_rank_counterexample :
    ∃ T : Matrix (Fin 1) (Fin 1) ℂ,
      T.PosSemidef ∧ IsToeplitz T ∧ T.rank = 1 ∧
      atomicMatrix 0 {1} (fun _ => 1) = T ∧
      atomicMatrix 0 {-1} (fun _ => 1) = T ∧
      ({1} : Finset ℂ) ≠ {-1} ∧
      (∀ z ∈ ({1} : Finset ℂ), ‖z‖ = 1 ∧ 0 < (1 : ℝ)) ∧
      (∀ z ∈ ({-1} : Finset ℂ), ‖z‖ = 1 ∧ 0 < (1 : ℝ)) := by
  refine ⟨1, PosSemidef.one, ?_, by simp, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact Fin.elim0 i
  · ext i j
    fin_cases i
    fin_cases j
    norm_num [atomicMatrix]
  · ext i j
    fin_cases i
    fin_cases j
    norm_num [atomicMatrix]
  · norm_num [Finset.singleton_inj]
  · intro z hz
    simp only [Finset.mem_singleton] at hz
    subst z
    norm_num
  · intro z hz
    simp only [Finset.mem_singleton] at hz
    subst z
    norm_num

end Reinmann.ToeplitzUniqueness
