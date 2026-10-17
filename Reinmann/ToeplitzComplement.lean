/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.Linarith

/-! Finite Toeplitz convolution and the complementary determinant identity.
The block identity needs no invertibility of either selected minor. -/
noncomputable section
namespace Reinmann.ToeplitzComplement
open Matrix Finset

variable {R m n : Type*} [CommRing R]
  [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Jacobi's complementary identity in block coordinates. In contrast to a
Schur-complement proof, this remains valid when the complementary block is singular. -/
theorem jacobi_block {M N : Matrix (m ⊕ n) (m ⊕ n) R} (hMN : M * N = 1) :
    M.toBlocks₂₂.det = M.det * N.toBlocks₁₁.det := by
  let X := fromBlocks N.toBlocks₁₁ 0 N.toBlocks₂₁ (1 : Matrix n n R)
  have hx : M * X = fromBlocks 1 M.toBlocks₁₂ 0 M.toBlocks₂₂ := by
    have h11 := congrArg Matrix.toBlocks₁₁ hMN
    have h21 := congrArg Matrix.toBlocks₂₁ hMN
    rw [← fromBlocks_toBlocks M, ← fromBlocks_toBlocks N, fromBlocks_multiply] at h11 h21
    simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₁] at h11 h21
    have ho11 : (1 : Matrix (m ⊕ n) (m ⊕ n) R).toBlocks₁₁ = 1 := by
      ext i j; simp [Matrix.toBlocks₁₁, Matrix.one_apply]
    have ho21 : (1 : Matrix (m ⊕ n) (m ⊕ n) R).toBlocks₂₁ = 0 := by
      ext i j; simp [Matrix.toBlocks₂₁]
    rw [ho11] at h11
    rw [ho21] at h21
    dsimp only [X]
    rw [← fromBlocks_toBlocks M, fromBlocks_multiply]
    simp only [h11, h21, Matrix.mul_zero, Matrix.mul_one, zero_add,
      toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₂]
  have hd := congrArg Matrix.det hx
  simpa only [Matrix.det_mul, X, det_fromBlocks_zero₁₂,
    det_fromBlocks_zero₂₁, det_one, mul_one, one_mul] using hd.symm

/-- Zero-extended ordinary coefficient, with integer indices encoded as a pair. -/
def entry (f : PowerSeries R) (i j : ℕ) : R :=
  if j ≤ i then PowerSeries.coeff (i-j) f else 0

def toeplitz (f : PowerSeries R) (N : ℕ) : Matrix (Fin N) (Fin N) R :=
  fun i j => entry f i.val j.val

/-- Multiplication of finite lower triangular Toeplitz matrices is exactly
ordinary power-series convolution; there is no discarded boundary term. -/
theorem toeplitz_mul (f g : PowerSeries R) (N : ℕ) :
    toeplitz (f * g) N = toeplitz f N * toeplitz g N := by
  classical
  ext i j
  rw [Matrix.mul_apply]
  change entry (f * g) i.val j.val = ∑ k : Fin N, entry f i.val k.val * entry g k.val j.val
  by_cases hij : j.val ≤ i.val
  · have hs : (∑ k : Fin N, entry f i.val k.val * entry g k.val j.val) =
        ∑ k ∈ univ.filter (fun k : Fin N => j.val ≤ k.val ∧ k.val ≤ i.val),
          PowerSeries.coeff (i.val-k.val) f * PowerSeries.coeff (k.val-j.val) g := by
      rw [sum_filter]
      apply sum_congr rfl
      intro k _
      by_cases hki : k.val ≤ i.val <;> by_cases hjk : j.val ≤ k.val <;>
        simp [entry, hki, hjk]
    change entry (f * g) i.val j.val = _
    rw [hs, entry, if_pos hij, PowerSeries.coeff_mul]
    symm
    apply sum_bij (fun k _ => (i.val-k.val, k.val-j.val))
    · intro k hk
      simp only [mem_filter, mem_univ, true_and] at hk
      apply Finset.mem_antidiagonal.mpr
      omega
    · intro k hk l hl he
      simp only [mem_filter, mem_univ, true_and] at hk hl
      have := congrArg Prod.snd he
      apply Fin.ext
      dsimp at this
      omega
    · intro p hp
      have hp' := Finset.mem_antidiagonal.mp hp
      refine ⟨⟨p.2+j.val, by have := i.isLt; omega⟩, ?_, ?_⟩
      · simp only [mem_filter, mem_univ, true_and]
        omega
      · apply Prod.ext <;> dsimp <;> omega
    · intro k _
      rfl
  · change entry (f * g) i.val j.val = _
    rw [entry, if_neg hij]
    symm
    apply sum_eq_zero
    intro k _
    by_cases hki : k.val ≤ i.val
    · have hjk : ¬ j.val ≤ k.val := by omega
      simp [entry, hjk]
    · simp [entry, hki]

@[simp] theorem toeplitz_one (N : ℕ) : toeplitz (1 : PowerSeries R) N = 1 := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [toeplitz, entry]
  · have hv : i.val ≠ j.val := fun he => h (Fin.ext he)
    simp only [toeplitz, entry, PowerSeries.coeff_one, Matrix.one_apply, h, if_false]
    split_ifs <;> simp_all
    all_goals omega

/-- A two-sided inverse of series yields actual finite matrix inverses. -/
theorem toeplitz_inverse {f g : PowerSeries R} (h : f * g = 1) (N : ℕ) :
    toeplitz f N * toeplitz g N = 1 := by
  rw [← toeplitz_mul, h, toeplitz_one]

theorem toeplitz_det {f : PowerSeries R} (hf : PowerSeries.coeff 0 f = 1) (N : ℕ) :
    (toeplitz f N).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · simp [toeplitz, entry, hf]
  · intro i j hij
    have h : ¬ j.val ≤ i.val := by exact not_le.mpr hij
    simp [toeplitz, entry, h]

/-- The rank and shift convention of the paper, including negative-index zeros. -/
def minor (f : PowerSeries R) (size shift : ℕ) : R :=
  Matrix.det (fun i j : Fin size => entry f (shift+i.val) j.val)

private theorem cycle_sign (s r : ℕ) (hs : 0 < s) :
    (finCycle (⟨r, by omega⟩ : Fin (s+r))).sign = (-1)^(s*r) := by
  have hp : finCycle (⟨r, by omega⟩ : Fin (s+r)) = (finRotate (s+r))^r := by
    ext i
    rw [Equiv.Perm.coe_pow]
    exact congrArg Fin.val (congrFun
      (finCycle_eq_finRotate_iterate (k := (⟨r, by omega⟩ : Fin (s+r)))) i)
  rw [hp, map_pow, sign_finRotate, ← pow_mul]
  cases r with
  | zero => simp
  | succ r =>
    have he : (s+(r+1)-1)*(r+1) = s*(r+1) + (r+1)*r := by
      have h : s+(r+1)-1 = s+r := by omega
      rw [h]; ring
    rw [he, pow_add]
    have hv := (Nat.even_mul_pred_self (r+1)).neg_one_pow (α := ℤˣ)
    simp only [Nat.add_sub_cancel] at hv
    rw [hv, mul_one]

/-- Jacobi's identity for ordinary coefficients and their reciprocal series.
The sign is essential: it disappears when f(z) is the original F(-z). -/
theorem complementary_minor {f g : PowerSeries R} (hfg : f * g = 1)
    (hf : PowerSeries.coeff 0 f = 1) (s r : ℕ) :
    minor f r s = (-1 : R)^(s*r) * minor g s r := by
  classical
  by_cases hs : s = 0
  · subst s
    simp only [minor, Matrix.det_fin_zero, Nat.zero_mul, pow_zero, mul_one]
    simpa [toeplitz, Nat.zero_add] using toeplitz_det hf r
  have hs0 : 0 < s := Nat.pos_of_ne_zero hs
  let e : (Fin s ⊕ Fin r) ≃ Fin (s+r) := finSumFinEquiv
  let π : Equiv.Perm (Fin (s+r)) := finCycle ⟨r, by omega⟩
  let d := e.trans π
  let M := (toeplitz f (s+r)).submatrix e d
  let N := (toeplitz g (s+r)).submatrix d e
  have hMN : M*N = 1 := by
    dsimp only [M, N]
    rw [Matrix.submatrix_mul_equiv, toeplitz_inverse hfg]
    exact Matrix.submatrix_one_equiv e
  have hd : M.det = (-1 : R)^(s*r) := by
    have hm : M = ((toeplitz f (s+r)).submatrix (Equiv.refl _) π).submatrix e e := rfl
    rw [hm, Matrix.det_submatrix_equiv_self]
    change ((toeplitz f (s+r)).submatrix id π).det = _
    rw [Matrix.det_permute', toeplitz_det hf]
    simp only [π, cycle_sign s r hs0, Units.val_pow_eq_pow_val, Int.cast_pow,
      Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, mul_one]
  have hleft (i : Fin s) : d (Sum.inl i) = ⟨r+i.val, by omega⟩ := by
    apply Fin.ext
    simp only [d, e, π, Equiv.trans_apply, finSumFinEquiv_apply_left,
      finCycle_apply, Fin.val_add, Fin.val_castAdd]
    rw [Nat.mod_eq_of_lt (by have := i.isLt; omega)]
    omega
  have hright (j : Fin r) : d (Sum.inr j) = ⟨j.val, by omega⟩ := by
    apply Fin.ext
    simp only [d, e, π, Equiv.trans_apply, finSumFinEquiv_apply_right,
      finCycle_apply, Fin.val_add, Fin.val_natAdd]
    have h : s+j.val+r = j.val+(s+r) := by omega
    rw [h, Nat.add_mod_right, Nat.mod_eq_of_lt (by have := j.isLt; omega)]
  have h22 : M.toBlocks₂₂ = fun i j : Fin r => entry f (s+i.val) j.val := by
    ext i j
    change entry f (e (Sum.inr i)).val (d (Sum.inr j)).val = _
    rw [hright]
    rfl
  have h11 : N.toBlocks₁₁ = fun i j : Fin s => entry g (r+i.val) j.val := by
    ext i j
    change entry g (d (Sum.inl i)).val (e (Sum.inl j)).val = _
    rw [hleft]
    rfl
  have hc := jacobi_block hMN
  rw [hd, h22, h11] at hc
  exact hc

end Reinmann.ToeplitzComplement
