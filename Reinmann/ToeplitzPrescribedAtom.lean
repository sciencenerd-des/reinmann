/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.ToeplitzUniqueness

/-! # Positive Toeplitz representations with a prescribed unit-circle atom

Shared finite linear algebra. No arithmetic positivity is supplied.
-/

noncomputable section

namespace Reinmann.ToeplitzPrescribedAtom

open Matrix Polynomial Reinmann.ToeplitzKernel Reinmann.ToeplitzAtomic
  Reinmann.ToeplitzExtension Reinmann.ToeplitzDowndate
open scoped ComplexOrder

/-- A positive definite matrix admits a positive rank-one downdate at any complex node.
The unit-circle restriction is needed later for Toeplitz invariance, not here. -/
theorem exists_node_downdate {n : ℕ}
    {T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hT : T.PosDef) (z : ℂ) :
    ∃ a : ℝ, 0 < a ∧
      (T - atomicMatrix n {z} (fun _ => a)).PosSemidef ∧
      (T - atomicMatrix n {z} (fun _ => a)).rank ≤ n := by
  let B : Matrix (Fin (n + 1)) Unit ℂ := fun i _ => star (z ^ (i : ℕ))
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
  let C : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
    of (fun i j => g * star (z ^ (i : ℕ)) * z ^ (j : ℕ))
  have hcorr : B * D⁻¹ * Bᴴ = C := by
    ext i j
    simp only [mul_apply, Fintype.sum_unique, conjTranspose_apply, B, C,
      of_apply, star_star]
    ring
  let u := T⁻¹ *ᵥ (fun i : Fin (n + 1) => star (z ^ (i : ℕ)))
  have hTu : T *ᵥ u = (fun i : Fin (n + 1) => star (z ^ (i : ℕ))) := by
    dsimp only [u]
    rw [mulVec_mulVec, mul_inv_of_invertible, one_mulVec]
  have hu : u ≠ 0 := by
    intro h
    rw [h, mulVec_zero] at hTu
    have he := congrFun hTu (0 : Fin (n + 1))
    exact zero_ne_one (by
      simpa only [Pi.zero_apply, Fin.val_zero, pow_zero, star_one] using he)
  have hDu : D () () = ∑ j : Fin (n + 1), z ^ (j : ℕ) * u j := by
    change (Bᴴ * T⁻¹ * B) () () = _
    rw [Matrix.mul_assoc]
    simp [B, u, mul_apply, conjTranspose_apply, mulVec, dotProduct]
  have hgd : g * D () () = 1 := by
    have he := congrFun (congrFun (inv_mul_of_invertible D) ()) ()
    simpa [mul_apply, g] using he
  have hku : (T - C) *ᵥ u = 0 := by
    rw [sub_mulVec, hTu]
    ext i
    simp only [Pi.sub_apply, Pi.zero_apply, mulVec, dotProduct, C, of_apply]
    have hs : (∑ j : Fin (n + 1),
        (g * star (z ^ (i : ℕ)) * z ^ (j : ℕ)) * u j) =
        star (z ^ (i : ℕ)) * (g * D () ()) := by
      rw [hDu, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hs, hgd, mul_one, sub_self]
  have hr := rank_le_of_nonzero_kernel hu hku
  have hatom : atomicMatrix n {z} (fun _ => g.re) = C := by
    ext i j
    simp [atomicMatrix, C, hreal]
  refine ⟨g.re, hgre, ?_, ?_⟩
  · rw [hatom]
    rwa [hcorr] at hA
  · rw [hatom]
    exact hr

lemma atomicMatrix_add_positive_node (n : ℕ) (s : Finset ℂ) (w : ℂ → ℝ)
    (hw : ∀ z ∈ s, 0 < w z) (x : ℂ) {a : ℝ} (ha : 0 < a) :
    ∃ v : ℂ → ℝ, (∀ z ∈ insert x s, 0 < v z) ∧
      atomicMatrix n (insert x s) v =
        atomicMatrix n s w + atomicMatrix n {x} (fun _ => a) := by
  let v : ℂ → ℝ := fun z => (if z ∈ s then w z else 0) + if z = x then a else 0
  refine ⟨v, ?_, ?_⟩
  · intro z hz
    by_cases hzx : z = x
    · subst z
      by_cases hx : x ∈ s
      · simpa only [v, if_pos hx, if_pos rfl] using add_pos (hw x hx) ha
      · simpa only [v, if_neg hx, if_pos rfl, zero_add] using ha
    · have hzs : z ∈ s := (Finset.mem_insert.mp hz).resolve_left hzx
      simpa only [v, if_pos hzs, if_neg hzx, add_zero] using hw z hzs
  · have hv (z : ℂ) : (v z : ℂ) =
        (if z ∈ s then (w z : ℂ) else 0) + if z = x then (a : ℂ) else 0 := by
      dsimp only [v]
      split_ifs <;> simp
    ext i j
    have hb : (∑ z ∈ insert x s, (if z ∈ s then (w z : ℂ) else 0) *
        star (z ^ (i : ℕ)) * z ^ (j : ℕ)) = atomicMatrix n s w i j := by
      by_cases hx : x ∈ s
      · rw [Finset.insert_eq_of_mem hx]
        apply Finset.sum_congr rfl
        intro z hz
        rw [if_pos hz]
      · rw [Finset.sum_insert hx]
        simp only [if_neg hx, zero_mul, zero_add]
        apply Finset.sum_congr rfl
        intro z hz
        rw [if_pos hz]
    have hd : (∑ z ∈ insert x s, (if z = x then (a : ℂ) else 0) *
        star (z ^ (i : ℕ)) * z ^ (j : ℕ)) =
        (a : ℂ) * star (x ^ (i : ℕ)) * x ^ (j : ℕ) := by
      rw [Finset.sum_eq_single x]
      · simp
      · intro z _ hz
        simp [hz]
      · intro h
        exact (h (Finset.mem_insert_self x s)).elim
    change (∑ z ∈ insert x s, (v z : ℂ) * star (z ^ (i : ℕ)) * z ^ (j : ℕ)) = _
    simp_rw [hv, add_mul]
    rw [Finset.sum_add_distrib, hb, hd]
    simp [atomicMatrix]

/-- Every unit-circle node can be included in a positive rank-sized representation
of any positive definite Toeplitz matrix. -/
theorem exists_representation_containing {n : ℕ}
    {T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hT : T.PosDef) (htoe : IsToeplitz T) {z : ℂ} (hz : ‖z‖ = 1) :
    ∃ s : Finset ℂ, ∃ w : ℂ → ℝ,
      s.card = T.rank ∧ z ∈ s ∧ (∀ x ∈ s, ‖x‖ = 1 ∧ 0 < w x) ∧
      T = atomicMatrix n s w := by
  obtain ⟨a, ha, hApsd, hArank⟩ := exists_node_downdate hT z
  let C := atomicMatrix n {z} (fun _ => a)
  let A := T - C
  have hCtoe : IsToeplitz C := by
    apply atomicMatrix_toeplitz
    intro x hx
    have hxz := Finset.mem_singleton.mp hx
    simpa only [hxz] using hz
  have hAtoe : IsToeplitz A := by
    intro i j
    change T i.succ j.succ - C i.succ j.succ = T i.castSucc j.castSucc - C i.castSucc j.castSucc
    rw [htoe i j, hCtoe i j]
  obtain ⟨s, w, hcard, hnodes, hentries⟩ :=
    ToeplitzRepresentation.exists_atomic_representation_singular hApsd hAtoe hArank
  have hAeq : A = atomicMatrix n s w := by
    ext i j
    exact hentries i j
  obtain ⟨v, hv, heq⟩ := atomicMatrix_add_positive_node n s w
    (fun x hx => (hnodes x hx).2) z ha
  have hTeq : T = atomicMatrix n (insert z s) v := by
    rw [heq, ← hAeq]
    exact (sub_add_cancel T C).symm
  have hrank : T.rank = n + 1 := by
    simpa only [Fintype.card_fin] using T.rank_of_isUnit hT.isUnit
  have hc : (insert z s).card = T.rank := by
    apply le_antisymm
    · calc
        (insert z s).card ≤ s.card + 1 := Finset.card_insert_le _ _
        _ = A.rank + 1 := by rw [hcard]
        _ ≤ n + 1 := Nat.add_le_add_right hArank 1
        _ = T.rank := hrank.symm
    · rw [hTeq]
      exact rank_atomicMatrix_le _ _ _
  refine ⟨insert z s, v, hc, Finset.mem_insert_self z s, ?_, hTeq⟩
  intro x hx
  refine ⟨?_, hv x hx⟩
  rcases Finset.mem_insert.mp hx with h | h
  · simpa only [h] using hz
  · exact (hnodes x h).1

end Reinmann.ToeplitzPrescribedAtom
