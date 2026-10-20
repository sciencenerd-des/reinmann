/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Fintype.Perm

/-! Rectangular matrix products and a function-indexed Cauchy–Binet identity.
The sum over all functions counts each injective minor `k!` times; repeated
indices contribute zero. This form avoids choosing subset enumerations. -/
noncomputable section
namespace Reinmann.MatrixMinorProduct
open Finset Matrix

variable {R : Type*} [CommRing R]
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- Multilinearity expands the determinant into choices of intermediate rows. -/
theorem det_mul_rowChoices (A : Matrix n m R) (B : Matrix m n R) :
    (A * B).det = ∑ p : n → m, (∏ i, A i (p i)) * (B.submatrix p id).det := by
  classical
  have h : A * B = fun i => ∑ j, A i j • B j := by
    ext i k
    simp [Matrix.mul_apply, Finset.sum_apply, smul_eq_mul]
  rw [h]
  change Matrix.detRowAlternating.toMultilinearMap (fun i => ∑ j, A i j • B j) = _
  rw [Matrix.detRowAlternating.toMultilinearMap.map_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [Matrix.detRowAlternating.toMultilinearMap.map_smul_univ]
  rfl

/-- Cauchy–Binet summed over functions rather than subsets. -/
theorem factorial_mul_det_mul (A : Matrix n m R) (B : Matrix m n R) :
    ((Fintype.card n).factorial : R) * (A * B).det =
      ∑ p : n → m, (A.submatrix id p).det * (B.submatrix p id).det := by
  classical
  symm
  calc
    _ = ∑ σ : Equiv.Perm n, ∑ p : n → m,
        (Equiv.Perm.sign σ : R) * (∏ i, A (σ i) (p i)) *
          (B.submatrix p id).det := by
      simp only [Matrix.det_apply', Matrix.submatrix_apply, id_eq, Finset.sum_mul]
      rw [Finset.sum_comm]
    _ = ∑ _σ : Equiv.Perm n, (A * B).det := by
      apply Finset.sum_congr rfl
      intro σ _
      let e : (n → m) ≃ (n → m) := Equiv.arrowCongr σ.symm (Equiv.refl m)
      rw [← e.sum_comp (fun p => (Equiv.Perm.sign σ : R) *
        (∏ i, A (σ i) (p i)) * (B.submatrix p id).det)]
      rw [det_mul_rowChoices]
      apply Finset.sum_congr rfl
      intro p _
      have he : e p = fun i => p (σ i) := rfl
      rw [he]
      have hb : (B.submatrix (fun i => p (σ i)) id).det =
          (Equiv.Perm.sign σ : R) * (B.submatrix p id).det :=
        Matrix.det_permute σ (B.submatrix p id)
      have hprod : (∏ i, A (σ i) (p (σ i))) = ∏ i, A i (p i) :=
        Fintype.prod_equiv σ _ _ (fun _ => rfl)
      rw [hb, hprod]
      have hs : (Equiv.Perm.sign σ : R) * (Equiv.Perm.sign σ : R) = 1 := by
        simp only [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self,
          Units.val_one, Int.cast_one]
      calc
        _ = ((Equiv.Perm.sign σ : R) * (Equiv.Perm.sign σ : R)) *
            ((∏ i, A i (p i)) * (B.submatrix p id).det) := by ring
        _ = _ := by rw [hs, one_mul]
    _ = _ := by simp [Fintype.card_perm]

omit [Fintype m] in
/-- The two permutation signs cancel in each paired minor. -/
theorem minor_pair_permute (A : Matrix n m R) (B : Matrix m n R)
    (p : n → m) (σ : Equiv.Perm n) :
    (A.submatrix id (p ∘ σ)).det * (B.submatrix (p ∘ σ) id).det =
      (A.submatrix id p).det * (B.submatrix p id).det := by
  have ha : (A.submatrix id (p ∘ σ)).det =
      (Equiv.Perm.sign σ : R) * (A.submatrix id p).det :=
    Matrix.det_permute' σ (A.submatrix id p)
  have hb : (B.submatrix (p ∘ σ) id).det =
      (Equiv.Perm.sign σ : R) * (B.submatrix p id).det :=
    Matrix.det_permute σ (B.submatrix p id)
  rw [ha, hb]
  have hs : (Equiv.Perm.sign σ : R) * (Equiv.Perm.sign σ : R) = 1 := by
    simp only [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self,
      Units.val_one, Int.cast_one]
  calc
    _ = ((Equiv.Perm.sign σ : R) * (Equiv.Perm.sign σ : R)) *
        ((A.submatrix id p).det * (B.submatrix p id).det) := by ring
    _ = _ := by rw [hs, one_mul]

end Reinmann.MatrixMinorProduct
