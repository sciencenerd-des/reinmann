import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Tactic.Ring

/-! The shift-one Toeplitz minor of (1,2c,1), including its determinant bridge. -/

noncomputable section

namespace Reinmann.ToeplitzQuadraticChebyshev

open Matrix Polynomial

def tri (n : ℕ) (c : ℝ) : Matrix (Fin n) (Fin n) ℝ := fun i j =>
  if i.val = j.val then 2*c else if i.val+1 = j.val ∨ j.val+1 = i.val then 1 else 0

@[simp] theorem tri_diag (n : ℕ) (c : ℝ) (i : Fin n) : tri n c i i = 2*c := by
  simp [tri]

@[simp] theorem tri_succ (n : ℕ) (c : ℝ) (i j : Fin n) :
    tri (n+1) c i.succ j.succ = tri n c i j := by
  simp [tri, Fin.val_succ, Nat.add_assoc]

@[simp] theorem tri_zero_one (n : ℕ) (c : ℝ) :
    tri (n+2) c 0 1 = 1 := by simp [tri]

@[simp] theorem tri_one_zero (n : ℕ) (c : ℝ) :
    tri (n+2) c 1 0 = 1 := by simp [tri]

@[simp] theorem tri_zero_far (n : ℕ) (c : ℝ) (j : Fin n) :
    tri (n+2) c 0 j.succ.succ = 0 := by
  simp [tri, Fin.val_succ, show ¬(0 = j.val+1+1) by omega,
    show ¬(0+1 = j.val+1+1 ∨ j.val+1+1+1 = 0) by omega]

@[simp] theorem tri_far_zero (n : ℕ) (c : ℝ) (j : Fin n) :
    tri (n+2) c j.succ.succ 0 = 0 := by
  simp [tri, Fin.val_succ, show ¬(j.val+1+1 = 0) by omega,
    show ¬(j.val+1+1+1 = 0 ∨ 0+1 = j.val+1+1) by omega]

theorem trailing_submatrix (n : ℕ) (c : ℝ) :
    (tri (n+1) c).submatrix Fin.succ Fin.succ = tri n c := by
  ext i j
  exact tri_succ n c i j

theorem removed_second_column (n : ℕ) (c : ℝ) :
    ((tri (n+2) c).submatrix Fin.succ (1 : Fin (n+2)).succAbove).det
      = (tri n c).det := by
  let B := (tri (n+2) c).submatrix Fin.succ (1 : Fin (n+2)).succAbove
  change B.det = _
  have h00 : B 0 0 = 1 := by simp [B, Matrix.submatrix_apply, Fin.one_succAbove_zero]
  have hcol (i : Fin n) : B i.succ 0 = 0 := by
    simp [B, Matrix.submatrix_apply, Fin.one_succAbove_zero]
  have hsub : B.submatrix Fin.succ Fin.succ = tri n c := by
    ext i j
    simp [B, Matrix.submatrix_apply, Fin.one_succAbove_succ]
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_mul, h00, hcol, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero, Fin.succAbove_zero]
  rw [hsub]

theorem determinant_recurrence (n : ℕ) (c : ℝ) :
    (tri (n+2) c).det = 2*c*(tri (n+1) c).det-(tri n c).det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_mul, Fin.succ_zero_eq_one,
    tri_diag, tri_zero_one, Fin.val_one, pow_one, mul_one,
    tri_zero_far, mul_zero, zero_mul, Finset.sum_const_zero, add_zero,
    Fin.succAbove_zero, trailing_submatrix, removed_second_column]
  ring

/-- The actual shift-one Toeplitz determinant equals the Chebyshev polynomial. -/
theorem determinant_eq_U (n : ℕ) (c : ℝ) :
    (tri n c).det = (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval c := by
  induction n using Nat.twoStepInduction with
  | zero => simp [Matrix.det_fin_zero]
  | one => simp [Matrix.det_fin_one, tri]
  | more n ih0 ih1 =>
    rw [determinant_recurrence, ih0, ih1]
    have hz : ((n+2 : ℕ) : ℤ) = (n : ℤ)+2 := by omega
    rw [hz, Polynomial.Chebyshev.U_add_two]
    simp [Polynomial.eval_sub, Polynomial.eval_mul, Nat.cast_add]

/-- The sine quotient is used instead of an unstable interval recurrence. -/
theorem determinant_cos (n : ℕ) (phi : ℝ) (hphi : Real.sin phi ≠ 0) :
    (tri n (Real.cos phi)).det = Real.sin (((n : ℝ)+1)*phi)/Real.sin phi := by
  rw [determinant_eq_U, eq_div_iff hphi]
  simpa using Polynomial.Chebyshev.U_real_cos phi (n : ℤ)

end Reinmann.ToeplitzQuadraticChebyshev
