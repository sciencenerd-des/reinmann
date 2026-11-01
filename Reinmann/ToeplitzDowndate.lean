/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.ToeplitzExtension

/-! # A positive constant rank-one downdate

The constant matrix preserves Toeplitz invariance. Shared finite linear algebra.
-/

noncomputable section

namespace Reinmann.ToeplitzDowndate

open Matrix
open scoped ComplexOrder

lemma rank_le_of_nonzero_kernel {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {u : Fin (n + 1) → ℂ} (hu : u ≠ 0) (hku : A *ᵥ u = 0) : A.rank ≤ n := by
  have hk : LinearMap.ker A.mulVecLin ≠ ⊥ := by
    intro h
    have hm : u ∈ LinearMap.ker A.mulVecLin := hku
    rw [h] at hm
    exact hu (by simpa using hm)
  have hd : Module.finrank ℂ (LinearMap.ker A.mulVecLin) ≠ 0 := by
    intro h
    exact hk (Submodule.finrank_eq_zero.mp h)
  have hn := A.mulVecLin.finrank_range_add_finrank_ker
  rw [← Matrix.rank] at hn
  simp only [Module.finrank_pi, Fintype.card_fin] at hn
  omega

lemma posDef_of_full_rank {n : ℕ}
    {T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hT : T.PosSemidef) (hrank : T.rank = n + 1) : T.PosDef := by
  apply hT.posDef_iff_isUnit.mpr
  apply Matrix.mulVec_injective_iff_isUnit.mp
  have hn := T.mulVecLin.finrank_range_add_finrank_ker
  rw [← Matrix.rank, hrank] at hn
  simp only [Module.finrank_pi, Fintype.card_fin] at hn
  have hd : Module.finrank ℂ (LinearMap.ker T.mulVecLin) = 0 := by omega
  exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hd)

/-- Subtracting a strictly positive constant matrix can make a positive definite
matrix singular while preserving positive semidefiniteness. -/
theorem exists_constant_downdate {n : ℕ}
    {T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hT : T.PosDef) :
    ∃ a : ℝ, 0 < a ∧
      (T - (Matrix.of (fun _ _ : Fin (n + 1) => (a : ℂ)))).PosSemidef ∧
      (T - (Matrix.of (fun _ _ : Fin (n + 1) => (a : ℂ)))).rank ≤ n := by
  let B : Matrix (Fin (n + 1)) Unit ℂ := fun _ _ => 1
  let D : Matrix Unit Unit ℂ := Bᴴ * T⁻¹ * B
  have hB : Function.Injective B.mulVec := by
    intro x y h
    funext j
    have he := congrFun h (0 : Fin (n + 1))
    simpa [B, mulVec, dotProduct] using he
  have hD : D.PosDef := hT.inv.conjTranspose_mul_mul_same hB
  letI := hT.isUnit.invertible
  letI := hD.isUnit.invertible
  have hblock : (fromBlocks T B Bᴴ D).PosSemidef := by
    apply (PosDef.fromBlocks₁₁ B D hT).mpr
    change (D - D).PosSemidef
    rw [sub_self]
    exact PosSemidef.zero
  have hA := (PosDef.fromBlocks₂₂ T B hD).mp hblock
  let g := D⁻¹ () ()
  have hg : 0 < g := hD.inv.diag_pos
  have hgre : 0 < g.re := (RCLike.pos_iff.mp hg).1
  have hreal : (g.re : ℂ) = g := by
    apply Complex.ext
    · rfl
    · exact (RCLike.pos_iff.mp hg).2.symm
  have hcorr : B * D⁻¹ * Bᴴ = (Matrix.of (fun _ _ : Fin (n + 1) => g)) := by
    ext i j
    simp [B, g, mul_apply, conjTranspose_apply]
  let u := T⁻¹ *ᵥ (fun _ : Fin (n + 1) => (1 : ℂ))
  have hTu : T *ᵥ u = (fun _ => (1 : ℂ)) := by
    dsimp only [u]
    rw [mulVec_mulVec, mul_inv_of_invertible, one_mulVec]
  have hu : u ≠ 0 := by
    intro h
    rw [h, mulVec_zero] at hTu
    have he := congrFun hTu (0 : Fin (n + 1))
    exact zero_ne_one he
  have hDu : D () () = ∑ j, u j := by
    change (Bᴴ * T⁻¹ * B) () () = _
    rw [Matrix.mul_assoc]
    simp [B, u, mul_apply, conjTranspose_apply, mulVec, dotProduct]
  have hgd : g * D () () = 1 := by
    have he := congrFun (congrFun (inv_mul_of_invertible D) ()) ()
    simpa [mul_apply, g] using he
  have hku : (T - (Matrix.of (fun _ _ : Fin (n + 1) => g))) *ᵥ u = 0 := by
    rw [sub_mulVec, hTu]
    ext i
    simp only [Pi.sub_apply, Pi.zero_apply, mulVec, dotProduct, Matrix.of_apply]
    rw [← Finset.mul_sum, ← hDu, hgd, sub_self]
  have hr := rank_le_of_nonzero_kernel hu hku
  refine ⟨g.re, hgre, ?_, ?_⟩
  · rw [hreal]
    rwa [hcorr] at hA
  · simpa only [hreal] using hr

end Reinmann.ToeplitzDowndate
