import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.LinearAlgebra.QuadraticForm.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Tactic.Ring


/-!
Finite-dimensional Schur inertia after an explicitly supplied completion of
the square. No operator-domain assertion or positivity instance is supplied.
-/

noncomputable section
open QuadraticMap

namespace Reinmann.WeilSchurInertia

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]
  [Module ℝ M] [Module ℝ N] [FiniteDimensional ℝ M] [FiniteDimensional ℝ N]

theorem sigNeg_le_of_injective_domination
    (Q : QuadraticForm ℝ M) (R : QuadraticForm ℝ N)
    (f : M →ₗ[ℝ] N) (hf : Function.Injective f)
    (hdom : ∀ x, R (f x) ≤ Q x) : sigNeg Q ≤ sigNeg R := by
  obtain ⟨V, hdim, hV⟩ := exists_finrank_eq_sigNeg_and_negDef Q
  let g : V →ₗ[ℝ] N := f.comp V.subtype
  have hg : Function.Injective g := hf.comp V.subtype_injective
  have hneg : ((-R).restrict (LinearMap.range g)).PosDef := by
    intro w hw
    obtain ⟨v, hv⟩ := w.property
    have hv0 : v ≠ 0 := by
      intro h
      apply hw
      apply Subtype.ext
      simpa [h] using hv.symm
    have hp := hV v hv0
    change 0 < -Q (v : M) at hp
    change 0 < -R (w : N)
    rw [← hv]
    exact lt_of_lt_of_le hp (neg_le_neg (hdom (v : M)))
  have hle := le_sigNeg_of_negDef R hneg
  rw [LinearMap.finrank_range_of_inj hg, hdim] at hle
  exact hle

theorem sigNeg_prod_of_nonneg (S : QuadraticForm ℝ M) (D : QuadraticForm ℝ N)
    (hD : ∀ y, 0 ≤ D y) : sigNeg (S.prod D) = sigNeg S := by
  apply Nat.le_antisymm
  · obtain ⟨V, hdim, hV⟩ := exists_finrank_eq_sigNeg_and_negDef (S.prod D)
    let f : V →ₗ[ℝ] M := (LinearMap.fst ℝ M N).comp V.subtype
    have hf : Function.Injective f := by
      intro u v huv
      by_contra hne
      have hnonzero : u-v ≠ 0 := sub_ne_zero.mpr hne
      have hp := hV (u-v) hnonzero
      have hz : ((u-v : V) : M × N).1 = 0 := by
        change f (u-v) = 0
        simp [huv]
      change 0 < -(S (((u-v : V) : M × N).1) + D (((u-v : V) : M × N).2)) at hp
      rw [hz, map_zero, zero_add] at hp
      linarith [hD (((u-v : V) : M × N).2)]
    have hneg : ((-S).restrict (LinearMap.range f)).PosDef := by
      intro w hw
      obtain ⟨v, hv⟩ := w.property
      have hv0 : v ≠ 0 := by
        intro h
        apply hw
        apply Subtype.ext
        simpa [h] using hv.symm
      have hp := hV v hv0
      change 0 < -(S (v : M × N).1 + D (v : M × N).2) at hp
      change 0 < -S (w : M)
      rw [← hv]
      change 0 < -S (v : M × N).1
      linarith [hD (v : M × N).2]
    have hle := le_sigNeg_of_negDef S hneg
    rw [LinearMap.finrank_range_of_inj hf, hdim] at hle
    exact hle
  · apply sigNeg_le_of_injective_domination S (S.prod D) (LinearMap.inl ℝ M N)
    · intro x y h
      exact congrArg Prod.fst h
    · intro x
      simp

/-- The triangular change of variables used to complete the square. -/
def shear (T : M →ₗ[ℝ] N) : (M × N) ≃ₗ[ℝ] (M × N) where
  toFun v := (v.1, v.2 + T v.1)
  invFun v := (v.1, v.2 - T v.1)
  left_inv v := by ext <;> simp
  right_inv v := by ext <;> simp
  map_add' u v := by ext <;> simp <;> abel
  map_smul' c v := by ext <;> simp [smul_add]

/-- Schur inertia: the coercive complementary square contributes no negative
directions. In a matrix application T = D⁻¹B and S = H - BᵀD⁻¹B. -/
theorem schur_inertia_of_completion
    (Q : QuadraticForm ℝ (M × N)) (S : QuadraticForm ℝ M)
    (D : QuadraticForm ℝ N) (T : M →ₗ[ℝ] N)
    (hD : ∀ y, 0 ≤ D y)
    (hcomplete : ∀ x y, Q (x,y) = S x + D (y + T x)) :
    sigNeg Q = sigNeg S := by
  let e : Q.IsometryEquiv (S.prod D) :=
    { shear T with map_app' := by intro v; exact (hcomplete v.1 v.2).symm }
  exact (QuadraticMap.Equivalent.sigNeg_eq ⟨e⟩).trans (sigNeg_prod_of_nonneg S D hD)

end Reinmann.WeilSchurInertia


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

#print axioms Reinmann.WeilSchurInertia.sigNeg_le_of_injective_domination
#print axioms Reinmann.WeilSchurInertia.sigNeg_prod_of_nonneg
#print axioms Reinmann.WeilSchurInertia.schur_inertia_of_completion
#print axioms Reinmann.ToeplitzQuadraticChebyshev.determinant_recurrence
#print axioms Reinmann.ToeplitzQuadraticChebyshev.determinant_eq_U
#print axioms Reinmann.ToeplitzQuadraticChebyshev.determinant_cos
