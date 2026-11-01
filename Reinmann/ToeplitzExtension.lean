/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.ToeplitzAtomic

/-! # Positive Toeplitz extension uniqueness and atomic matrices

Shared finite linear algebra, with the existing coefficient and entry conventions.
-/

noncomputable section

namespace Reinmann.ToeplitzExtension

open Matrix Polynomial Reinmann.ToeplitzKernel Reinmann.ToeplitzAtomic
open scoped ComplexOrder

/-- Delete the final row and column. -/
def leading {n : ℕ} (T : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := T.submatrix Fin.castSucc Fin.castSucc

lemma leading_toeplitz {n : ℕ} {T : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ}
    (ht : IsToeplitz T) : IsToeplitz (leading T) := by
  intro i j
  exact ht i.castSucc j.castSucc

lemma energy_leading {n : ℕ} (T : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)
    (q : ℂ[X]) (hq : q.natDegree < n + 1) :
    energy T (coeffVec (n + 1) q) = energy (leading T) (coeffVec n q) := by
  have hlast : q.coeff (n + 1) = 0 := coeff_eq_zero_of_natDegree_lt hq
  unfold energy
  simp only [dotProduct, mulVec, Pi.star_apply, coeffVec, Finset.mul_sum]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_last, hlast, star_zero, zero_mul, Finset.sum_const_zero, add_zero]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_castSucc]
  simp [hlast, leading]

lemma kernel_lift {n : ℕ} {T : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ}
    (hT : T.PosSemidef) {q : ℂ[X]} (hq : q.natDegree < n + 1)
    (hk : leading T *ᵥ coeffVec n q = 0) : T *ᵥ coeffVec (n + 1) q = 0 := by
  apply (hT.dotProduct_mulVec_zero_iff _).mp
  change energy T (coeffVec (n + 1) q) = 0
  rw [energy_leading T q hq]
  simp [energy, hk]

/-- A short kernel relation with nonzero constant term fixes the next Toeplitz moment. -/
theorem extension_unique {n : ℕ}
    {T E : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ}
    (hT : T.PosSemidef) (hE : E.PosSemidef)
    (ht : IsToeplitz T) (he : IsToeplitz E) (hlead : leading T = leading E)
    {q : ℂ[X]} (hq : q.natDegree < n + 1) (hq0 : q.coeff 0 ≠ 0)
    (hk : leading T *ᵥ coeffVec n q = 0) : T = E := by
  have htk := kernel_lift hT hq hk
  have hek := kernel_lift hE hq (by rw [← hlead]; exact hk)
  have hrow (j : Fin (n + 1)) :
      T (Fin.last (n + 1)) j.succ = E (Fin.last (n + 1)) j.succ := by
    calc
      T (Fin.last (n + 1)) j.succ =
          T (Fin.last n).castSucc j.castSucc := ht (Fin.last n) j
      _ = E (Fin.last n).castSucc j.castSucc := congrFun (congrFun hlead (Fin.last n)) j
      _ = E (Fin.last (n + 1)) j.succ := (he (Fin.last n) j).symm
  have hrest : (∑ j : Fin (n + 1),
      T (Fin.last (n + 1)) j.succ * q.coeff (j.val + 1)) =
      ∑ j : Fin (n + 1), E (Fin.last (n + 1)) j.succ * q.coeff (j.val + 1) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hrow j]
  have htc := congrFun htk (Fin.last (n + 1))
  have hec := congrFun hek (Fin.last (n + 1))
  simp only [mulVec, dotProduct, coeffVec, Pi.zero_apply] at htc hec
  rw [Fin.sum_univ_succ] at htc hec
  simp only [Fin.val_zero, Fin.val_succ] at htc hec
  have hcorner : T (Fin.last (n + 1)) 0 = E (Fin.last (n + 1)) 0 := by
    apply mul_right_cancel₀ hq0
    linear_combination htc - hec - hrest
  have hlast (j : Fin (n + 2)) : T (Fin.last (n + 1)) j = E (Fin.last (n + 1)) j := by
    induction j using Fin.cases with
    | zero => exact hcorner
    | succ j => exact hrow j
  ext i j
  induction i using Fin.lastCases with
  | last => exact hlast j
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      rw [← hT.isHermitian.apply, ← hE.isHermitian.apply, hlast]
    | cast j => exact congrFun (congrFun hlead i) j

/-- Matrix of finite positive unit-circle atoms, in the original entry orientation. -/
def atomicMatrix (n : ℕ) (s : Finset ℂ) (w : ℂ → ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := fun i j =>
  ∑ z ∈ s, (w z : ℂ) * star (z ^ (i : ℕ)) * z ^ (j : ℕ)

lemma atomicMatrix_leading (n : ℕ) (s : Finset ℂ) (w : ℂ → ℝ) :
    leading (atomicMatrix (n + 1) s w) = atomicMatrix n s w := rfl

lemma atomicMatrix_toeplitz (n : ℕ) (s : Finset ℂ) (w : ℂ → ℝ)
    (hs : ∀ z ∈ s, ‖z‖ = 1) : IsToeplitz (atomicMatrix n s w) := by
  intro i j
  apply Finset.sum_congr rfl
  intro z hz
  have hu : star z * z = 1 := by
    change starRingEnd ℂ z * z = 1
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hs z hz]
    norm_num
  change (w z : ℂ) * star (z ^ (i.val + 1)) * z ^ (j.val + 1) = _
  rw [pow_succ, pow_succ, star_mul]
  calc
    _ = ((w z : ℂ) * star (z ^ i.val) * z ^ j.val) * (star z * z) := by ring
    _ = _ := by simp only [hu, mul_one, Fin.val_castSucc]

lemma atomicMatrix_posSemidef (n : ℕ) (s : Finset ℂ) (w : ℂ → ℝ)
    (hw : ∀ z ∈ s, 0 ≤ w z) : (atomicMatrix n s w).PosSemidef := by
  have heq : atomicMatrix n s w = ∑ z ∈ s,
      (w z : ℂ) • vecMulVec (star (fun i : Fin (n + 1) => z ^ (i : ℕ)))
        (fun i : Fin (n + 1) => z ^ (i : ℕ)) := by
    ext i j
    simp [atomicMatrix, Matrix.sum_apply, vecMulVec, mul_assoc]
  rw [heq]
  apply posSemidef_sum
  intro z hz
  apply (posSemidef_vecMulVec_star_self _).smul
  exact_mod_cast hw z hz

/-- Atomic matrices have rank at most the number of nodes. -/
theorem rank_atomicMatrix_le (n : ℕ) (s : Finset ℂ) (w : ℂ → ℝ) :
    (atomicMatrix n s w).rank ≤ s.card := by
  let A : Matrix (Fin (n + 1)) s ℂ := fun i z =>
    (w z : ℂ) * star ((z : ℂ) ^ (i : ℕ))
  let B : Matrix s (Fin (n + 1)) ℂ := fun z j => (z : ℂ) ^ (j : ℕ)
  have heq : atomicMatrix n s w = A * B := by
    ext i j
    change (∑ z ∈ s, (w z : ℂ) * star (z ^ (i : ℕ)) * z ^ (j : ℕ)) =
      ∑ z : s, (w z : ℂ) * star ((z : ℂ) ^ (i : ℕ)) * (z : ℂ) ^ (j : ℕ)
    exact (Finset.sum_coe_sort s
      (fun z : ℂ => (w z : ℂ) * star (z ^ (i : ℕ)) * z ^ (j : ℕ))).symm
  rw [heq]
  exact (rank_mul_le_left A B).trans ((rank_le_card_width A).trans_eq (by simp))

lemma atomicMatrix_kernel {n : ℕ} (s : Finset ℂ) (w : ℂ → ℝ)
    {q : ℂ[X]} (hq : q.natDegree ≤ n) (hz : ∀ z ∈ s, q.eval z = 0) :
    atomicMatrix n s w *ᵥ coeffVec n q = 0 := by
  ext i
  simp only [mulVec, dotProduct, atomicMatrix, coeffVec, Pi.zero_apply]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro z hzs
  calc
    (∑ j : Fin (n + 1), ((w z : ℂ) * star (z ^ (i : ℕ)) * z ^ (j : ℕ)) * q.coeff j) =
        ((w z : ℂ) * star (z ^ (i : ℕ))) * ∑ j : Fin (n + 1), q.coeff j * z ^ (j : ℕ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ((w z : ℂ) * star (z ^ (i : ℕ))) * q.eval z := by
      congr 1
      exact (Fin.sum_univ_eq_sum_range (fun j : ℕ => q.coeff j * z ^ j) (n + 1)).trans
        (eval_eq_sum_range' (by omega : q.natDegree < n + 1) z).symm
    _ = 0 := by rw [hz z hzs, mul_zero]

lemma nodal_coeff_zero_ne (s : Finset ℂ) (hs : ∀ z ∈ s, ‖z‖ = 1) :
    (Lagrange.nodal s id).coeff 0 ≠ 0 := by
  rw [coeff_zero_eq_eval_zero, Lagrange.eval_nodal]
  apply Finset.prod_ne_zero_iff.mpr
  intro z hz
  have hz0 : z ≠ 0 := by
    intro h
    exact zero_ne_one (by simpa only [h, norm_zero] using hs z hz)
  simpa only [id_eq, zero_sub, neg_ne_zero] using hz0

/-- Add a positive atom at 1, merging its weight if 1 was already a node. -/
lemma atomicMatrix_add_positive_one (n : ℕ) (s : Finset ℂ) (w : ℂ → ℝ)
    (hw : ∀ z ∈ s, 0 < w z) {a : ℝ} (ha : 0 < a) :
    ∃ v : ℂ → ℝ, (∀ z ∈ insert 1 s, 0 < v z) ∧
      atomicMatrix n (insert 1 s) v =
        atomicMatrix n s w + (Matrix.of (fun _ _ : Fin (n + 1) => (a : ℂ))) := by
  let v : ℂ → ℝ := fun z => (if z ∈ s then w z else 0) + if z = 1 then a else 0
  refine ⟨v, ?_, ?_⟩
  · intro z hz
    by_cases hz1 : z = 1
    · subst z
      by_cases h1 : (1 : ℂ) ∈ s
      · simpa only [v, if_pos h1, if_pos rfl] using add_pos (hw 1 h1) ha
      · simpa only [v, if_neg h1, if_pos rfl, zero_add] using ha
    · have hzs : z ∈ s := (Finset.mem_insert.mp hz).resolve_left hz1
      simpa only [v, if_pos hzs, if_neg hz1, add_zero] using hw z hzs
  · have hv (z : ℂ) : (v z : ℂ) =
        (if z ∈ s then (w z : ℂ) else 0) + if z = 1 then (a : ℂ) else 0 := by
      dsimp only [v]
      split_ifs <;> simp
    ext i j
    have hb : (∑ z ∈ insert 1 s, (if z ∈ s then (w z : ℂ) else 0) *
        star (z ^ (i : ℕ)) * z ^ (j : ℕ)) = atomicMatrix n s w i j := by
      by_cases h1 : (1 : ℂ) ∈ s
      · rw [Finset.insert_eq_of_mem h1]
        apply Finset.sum_congr rfl
        intro z hz
        rw [if_pos hz]
      · rw [Finset.sum_insert h1]
        simp only [if_neg h1, zero_mul, zero_add]
        apply Finset.sum_congr rfl
        intro z hz
        rw [if_pos hz]
    have hd : (∑ z ∈ insert 1 s, (if z = 1 then (a : ℂ) else 0) *
        star (z ^ (i : ℕ)) * z ^ (j : ℕ)) = (a : ℂ) := by
      rw [Finset.sum_eq_single 1]
      · simp
      · intro z _ hz
        simp [hz]
      · intro h
        exact (h (Finset.mem_insert_self 1 s)).elim
    change (∑ z ∈ insert 1 s, (v z : ℂ) * star (z ^ (i : ℕ)) * z ^ (j : ℕ)) = _
    simp_rw [hv, add_mul]
    rw [Finset.sum_add_distrib, hb, hd]
    rfl

end Reinmann.ToeplitzExtension
