/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Finite complementary-moment determinant expansion, proved by multilinearity. -/
noncomputable section
namespace Reinmann.SplitPairDeterminant
open Finset Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def momentMatrix (c z : ι → ℂ) (s n : ℕ) : Matrix (Fin s) (Fin s) ℂ :=
  fun i j => ∑ k, c k * z k ^ (n + i.val + (s - 1 - j.val))

def coefficient (c z : ι → ℂ) (s : ℕ) (S : Finset ι) : ℂ :=
  Matrix.det (fun i j : Fin s => ∑ k ∈ S, c k * z k ^ (i.val + (s - 1 - j.val)))

def support {s : ℕ} (e : Fin s → ι) : Finset ι := univ.image e

def rowCoefficient (c z : ι → ℂ) {s : ℕ} (e : Fin s → ι) : ℂ :=
  (∏ i, c (e i) * z (e i) ^ i.val) *
    Matrix.det (fun i j : Fin s => z (e i) ^ (s - 1 - j.val))

omit [Fintype ι] [DecidableEq ι] in
/-- Repeated pole choices vanish by alternation. -/
theorem rowCoefficient_zero {c z : ι → ℂ} {s : ℕ} {e : Fin s → ι}
    (he : ¬ Function.Injective e) : rowCoefficient c z e = 0 := by
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp he
  unfold rowCoefficient
  rw [Matrix.det_zero_of_row_eq hne (by
    funext l
    change z (e i) ^ _ = z (e j) ^ _
    rw [hij])]
  simp

omit [DecidableEq ι] in
/-- Exact expansion by all row choices, before grouping them into subsets. -/
theorem row_expansion (c z : ι → ℂ) (s n : ℕ) :
    (momentMatrix c z s n).det =
      ∑ e : Fin s → ι, rowCoefficient c z e * (∏ i, z (e i)) ^ n := by
  let v (i : Fin s) (k : ι) : Fin s → ℂ :=
    (c k * z k ^ (n + i.val)) • (fun j => z k ^ (s - 1 - j.val))
  have hm : momentMatrix c z s n = fun i => ∑ k, v i k := by
    ext i j
    simp [momentMatrix, v, pow_add, mul_assoc]
  change Matrix.detRowAlternating _ = _
  rw [hm]
  change Matrix.detRowAlternating.toMultilinearMap (fun i => ∑ k, v i k) = _
  rw [Matrix.detRowAlternating.toMultilinearMap.map_sum]
  apply sum_congr rfl
  intro e _
  rw [show (fun i => v i (e i)) =
      (fun i => (c (e i) * z (e i) ^ (n+i.val)) •
        (fun j => z (e i) ^ (s - 1 - j.val))) by rfl,
    Matrix.detRowAlternating.toMultilinearMap.map_smul_univ]
  change (∏ i, c (e i) * z (e i) ^ (n+i.val)) *
    Matrix.det (fun i j : Fin s => z (e i) ^ (s-1-j.val)) = _
  simp only [pow_add, prod_mul_distrib, prod_pow, rowCoefficient]
  ring

/-- A subset coefficient is a restricted row expansion. -/
theorem coefficient_row_expansion (c z : ι → ℂ) (s : ℕ) (S : Finset ι) :
    coefficient c z s S =
      ∑ e : Fin s → ι with ∀ i, e i ∈ S, rowCoefficient c z e := by
  let c' : ι → ℂ := fun k => if k ∈ S then c k else 0
  have hm : (fun i j : Fin s => ∑ k ∈ S, c k * z k ^ (i.val+(s-1-j.val))) =
      momentMatrix c' z s 0 := by
    ext i j
    simp only [momentMatrix, zero_add, c', ite_mul, zero_mul]
    simp
  unfold coefficient
  rw [hm, row_expansion]
  simp only [pow_zero, mul_one]
  rw [sum_filter]
  apply sum_congr rfl
  intro e _
  by_cases he : ∀ i, e i ∈ S
  · simp only [if_pos he, rowCoefficient]
    congr 1
    exact prod_congr rfl (fun i _ => by simp [c', he i])
  · simp only [if_neg he]
    push Not at he
    obtain ⟨i, hi⟩ := he
    unfold rowCoefficient
    have hzero : (∏ j, c' (e j) * z (e j) ^ j.val) = 0 :=
      prod_eq_zero (mem_univ i) (by simp [c', hi])
    rw [hzero, zero_mul]

/-- With exactly s poles, all surviving row choices use the whole subset. -/
theorem coefficient_eq_fiber (c z : ι → ℂ) (s : ℕ) {S : Finset ι} (hS : S.card = s) :
    coefficient c z s S =
      ∑ e : Fin s → ι with support e = S, rowCoefficient c z e := by
  rw [coefficient_row_expansion]
  symm
  apply sum_subset
  · intro e he
    simp only [mem_filter, mem_univ, true_and] at he ⊢
    intro i
    rw [← he]
    exact mem_image.mpr ⟨i, mem_univ i, rfl⟩
  · intro e he hnot
    apply rowCoefficient_zero
    intro hi
    have hsub : support e ⊆ S := by
      intro k hk
      obtain ⟨i, _, rfl⟩ := mem_image.mp hk
      exact (mem_filter.mp he).2 i
    have hcard : (support e).card = s := by simp [support, card_image_of_injective _ hi]
    have heq : support e = S := eq_of_subset_of_card_le hsub (by omega)
    exact hnot (mem_filter.mpr ⟨mem_univ e, heq⟩)

omit [DecidableEq ι] in
/-- Cauchy--Binet for the actual complementary determinant. There is no assumed
asymptotic or nonzero leading coefficient in this algebraic identity. -/
theorem subset_expansion (c z : ι → ℂ) (s n : ℕ) :
    (momentMatrix c z s n).det =
      ∑ S ∈ (univ : Finset ι).powersetCard s,
        coefficient c z s S * (∏ k ∈ S, z k) ^ n := by
  classical
  rw [row_expansion]
  have hfilter : (∑ e : Fin s → ι, rowCoefficient c z e * (∏ i, z (e i)) ^ n) =
      ∑ e : Fin s → ι with support e ∈ (univ : Finset ι).powersetCard s,
        rowCoefficient c z e * (∏ i, z (e i)) ^ n := by
    symm
    apply sum_subset (filter_subset _ _)
    intro e _ he
    have hn : ¬ Function.Injective e := by
      intro hi
      apply he
      simp [support, card_image_of_injective _ hi]
    rw [rowCoefficient_zero hn, zero_mul]
  rw [hfilter, ← sum_fiberwise_eq_sum_filter]
  apply sum_congr rfl
  intro S hS
  have hcard : S.card = s := (mem_powersetCard.mp hS).2
  rw [coefficient_eq_fiber c z s hcard, sum_mul]
  apply sum_congr rfl
  intro e he
  have heq : support e = S := (mem_filter.mp he).2
  have hi : Function.Injective e := by
    have h : (univ.image e).card = (univ : Finset (Fin s)).card := by
      change (support e).card = _
      rw [heq, hcard, card_univ, Fintype.card_fin]
    exact fun i j hij => (card_image_iff.mp h) (mem_univ i) (mem_univ j) hij
  rw [← prod_image hi.injOn]
  change rowCoefficient c z e * (∏ k ∈ support e, z k) ^ n = _
  rw [heq]

omit [Fintype ι] [DecidableEq ι] in
/-- Explicit Vandermonde formula for a subset coefficient, independent of the
chosen enumeration. Column reversal supplies the standard determinant sign. -/
theorem coefficient_eq_vandermonde (c z : ι → ℂ) (s : ℕ) (S : Finset ι) (e : Fin s ≃ S) :
    coefficient c z s S =
      ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin s)) : ℤ) : ℂ) *
        (∏ i : Fin s, c (e i).val) *
          (Matrix.vandermonde (fun i : Fin s => z (e i).val)).det ^ 2 := by
  classical
  let v : Fin s → ℂ := fun i => z (e i).val
  let w : Fin s → ℂ := fun i => c (e i).val
  have hsum (f : ι → ℂ) : (∑ i : Fin s, f (e i).val) = ∑ k ∈ S, f k := by
    rw [← Finset.sum_coe_sort S f]
    exact e.sum_comp (fun k : S => f k.val)
  have hm : (fun i j : Fin s => ∑ k ∈ S, c k * z k ^ (i.val+(s-1-j.val))) =
      (Matrix.vandermonde v).transpose * Matrix.diagonal w *
        (Matrix.vandermonde v).submatrix id Fin.revPerm := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply,
      Matrix.submatrix_apply, Matrix.vandermonde_apply, id_eq, Fin.revPerm_apply,
      Fin.val_rev]
    have hj : s - (j.val + 1) = s - 1 - j.val := by omega
    rw [hj, ← hsum (fun k => c k * z k ^ (i.val+(s-1-j.val)))]
    apply sum_congr rfl
    intro k _
    simp only [v, w, pow_add]
    ring
  unfold coefficient
  rw [hm, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal,
    Matrix.det_permute']
  change (Matrix.vandermonde v).det * (∏ i, w i) *
    (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin s)) : ℤ) : ℂ) *
      (Matrix.vandermonde v).det) =
    ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin s)) : ℤ) : ℂ) *
      (∏ i, w i) * (Matrix.vandermonde v).det ^ 2
  ring

omit [Fintype ι] [DecidableEq ι] in
/-- Every subset of the right cardinality has a nonzero computed coefficient:
the two Vandermonde determinants and every residue factor are nonzero. -/
theorem coefficient_ne_zero {c z : ι → ℂ} (hz : Function.Injective z)
    (hc : ∀ i, c i ≠ 0) (s : ℕ) {S : Finset ι} (hS : S.card = s) :
    coefficient c z s S ≠ 0 := by
  classical
  let e : Fin s ≃ S := (Fintype.equivFinOfCardEq (by simpa using hS)).symm
  have hv : (Matrix.vandermonde (fun i : Fin s => z (e i).val)).det ≠ 0 :=
    Matrix.det_vandermonde_ne_zero_iff.mpr
      (hz.comp (Subtype.val_injective.comp e.injective))
  have hw : (∏ i : Fin s, c (e i).val) ≠ 0 := prod_ne_zero_iff.mpr (fun i _ => hc _)
  have hsign : ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin s)) : ℤ) : ℂ) ≠ 0 := by
    exact_mod_cast Units.ne_zero (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin s)))
  rw [coefficient_eq_vandermonde c z s S e]
  exact mul_ne_zero (mul_ne_zero hsign hw) (pow_ne_zero 2 hv)

omit [Fintype ι] in
/-- Conjugation transports the computed subset coefficient, including all
Vandermonde signs, without choosing an ordering of the subset. -/
theorem coefficient_conjugate {c z : ι → ℂ} (σ : ι ≃ ι)
    (hc : ∀ i, c (σ i) = star (c i)) (hz : ∀ i, z (σ i) = star (z i))
    (s : ℕ) (S : Finset ι) :
    coefficient c z s (S.image σ) = star (coefficient c z s S) := by
  have hm : (fun i j : Fin s => ∑ k ∈ S.image σ, c k * z k ^ (i.val+(s-1-j.val))) =
      Matrix.map (fun i j : Fin s => ∑ k ∈ S, c k * z k ^ (i.val+(s-1-j.val)))
        (starRingEnd ℂ) := by
    ext i j
    rw [Finset.sum_image σ.injective.injOn]
    simp [Matrix.map_apply, hc, hz, map_sum, map_mul, map_pow]
  unfold coefficient
  rw [hm]
  exact (RingHom.map_det (starRingEnd ℂ)
    (fun i j : Fin s => ∑ k ∈ S, c k * z k ^ (i.val+(s-1-j.val)))).symm

omit [DecidableEq ι] in
/-- A conjugation-invariant finite pole model has real moment determinants. -/
theorem moment_im_eq_zero {c z : ι → ℂ} (σ : ι ≃ ι)
    (hc : ∀ i, c (σ i) = star (c i)) (hz : ∀ i, z (σ i) = star (z i))
    (s n : ℕ) : ((momentMatrix c z s n).det).im = 0 := by
  have hm : Matrix.map (momentMatrix c z s n) (starRingEnd ℂ) = momentMatrix c z s n := by
    ext i j
    change (starRingEnd ℂ) (∑ k, c k * z k ^ (n+i.val+(s-1-j.val))) = _
    rw [← σ.sum_comp (fun k => c k * z k ^ (n+i.val+(s-1-j.val)))]
    simp [momentMatrix, hc, hz, map_sum, map_mul, map_pow]
  have h := RingHom.map_det (starRingEnd ℂ) (momentMatrix c z s n)
  change star (momentMatrix c z s n).det = _ at h
  rw [show (starRingEnd ℂ).mapMatrix (momentMatrix c z s n) = momentMatrix c z s n from hm] at h
  have hi := congrArg Complex.im h
  change -((momentMatrix c z s n).det).im = ((momentMatrix c z s n).det).im at hi
  linarith

end Reinmann.SplitPairDeterminant
