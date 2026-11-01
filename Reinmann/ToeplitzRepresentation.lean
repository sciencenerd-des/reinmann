/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.ToeplitzDowndate

/-! # Atomic representations beyond corank one

Shared finite linear algebra under explicit PSD and Toeplitz hypotheses.
-/

noncomputable section

namespace Reinmann.ToeplitzRepresentation

open Matrix Polynomial Reinmann.ToeplitzKernel Reinmann.ToeplitzAtomic
  Reinmann.ToeplitzExtension Reinmann.ToeplitzDowndate
open scoped ComplexOrder

/-- Every singular positive Toeplitz matrix has exactly its rank many positive atoms. -/
theorem exists_atomic_representation_singular {n : ℕ}
    {T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hpsd : T.PosSemidef) (htoe : IsToeplitz T) (hrank : T.rank ≤ n) :
    HasAtomicRepresentation T T.rank := by
  induction n with
  | zero =>
    have heq : T.rank = 0 := by omega
    simpa only [heq] using ToeplitzAtomic.exists_atomic_representation hpsd htoe heq
  | succ n ih =>
    by_cases hcorank : T.rank = n + 1
    · simpa only [hcorank] using ToeplitzAtomic.exists_atomic_representation hpsd htoe hcorank
    have hrsmall : T.rank ≤ n := by omega
    have hlead_rank : (leading T).rank ≤ n :=
      (T.rank_submatrix_le Fin.castSucc Fin.castSucc).trans hrsmall
    obtain ⟨s, w, hcard, hnodes, hentries⟩ :=
      ih (hpsd.submatrix Fin.castSucc) (leading_toeplitz htoe) hlead_rank
    let E := atomicMatrix (n + 1) s w
    have hEpos : E.PosSemidef :=
      atomicMatrix_posSemidef _ s w (fun z hz => (hnodes z hz).2.le)
    have hEtoe : IsToeplitz E :=
      atomicMatrix_toeplitz _ s w (fun z hz => (hnodes z hz).1)
    have hlead : leading T = leading E := by
      ext i j
      exact hentries i j
    let q := Lagrange.nodal s id
    have hq : q.natDegree < n + 1 := by
      rw [Lagrange.natDegree_nodal, hcard]
      exact Nat.lt_succ_of_le hlead_rank
    have hq0 : q.coeff 0 ≠ 0 :=
      nodal_coeff_zero_ne s (fun z hz => (hnodes z hz).1)
    have hqk : leading T *ᵥ coeffVec n q = 0 := by
      rw [hlead]
      apply atomicMatrix_kernel s w (Nat.le_of_lt_succ hq)
      intro z hz
      simpa only [id_eq] using (Lagrange.eval_nodal_at_node (v := id) hz)
    have hTE : T = E := extension_unique hpsd hEpos htoe hEtoe hlead hq hq0 hqk
    have hcardT : T.rank = s.card := by
      apply le_antisymm
      · rw [hTE]
        exact rank_atomicMatrix_le _ s w
      · rw [hcard]
        exact T.rank_submatrix_le Fin.castSucc Fin.castSucc
    refine ⟨s, w, hcardT.symm, hnodes, ?_⟩
    intro i j
    rw [hTE]
    rfl

/-- The finite Caratheodory--Fejer representation for arbitrary rank,
including zero and full rank, with exactly rank(T) positive unit-circle atoms. -/
theorem exists_atomic_representation {n : ℕ}
    {T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hpsd : T.PosSemidef) (htoe : IsToeplitz T) : HasAtomicRepresentation T T.rank := by
  by_cases hs : T.rank ≤ n
  · exact exists_atomic_representation_singular hpsd htoe hs
  have hrank : T.rank = n + 1 := by
    have hb := T.rank_le_width
    omega
  have hpd := posDef_of_full_rank hpsd hrank
  obtain ⟨a, ha, hApsd, hArank⟩ := exists_constant_downdate hpd
  let C : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := of (fun _ _ => (a : ℂ))
  let A := T - C
  have hAtoe : IsToeplitz A := by
    intro i j
    change T i.succ j.succ - (a : ℂ) = T i.castSucc j.castSucc - (a : ℂ)
    rw [htoe i j]
  obtain ⟨s, w, hcard, hnodes, hentries⟩ :=
    exists_atomic_representation_singular hApsd hAtoe hArank
  have hAeq : A = atomicMatrix n s w := by
    ext i j
    exact hentries i j
  obtain ⟨v, hv, heq⟩ := atomicMatrix_add_positive_one n s w
    (fun z hz => (hnodes z hz).2) ha
  have hT : T = atomicMatrix n (insert 1 s) v := by
    rw [heq, ← hAeq]
    exact (sub_add_cancel T C).symm
  have hcardT : (insert 1 s).card = T.rank := by
    apply le_antisymm
    · calc
        (insert 1 s).card ≤ s.card + 1 := Finset.card_insert_le _ _
        _ = A.rank + 1 := by rw [hcard]
        _ ≤ n + 1 := Nat.add_le_add_right hArank 1
        _ = T.rank := hrank.symm
    · rw [hT]
      exact rank_atomicMatrix_le _ _ _
  refine ⟨insert 1 s, v, hcardT, ?_, ?_⟩
  · intro z hz
    refine ⟨?_, hv z hz⟩
    rcases Finset.mem_insert.mp hz with h | h
    · simp [h]
    · exact (hnodes z h).1
  · intro i j
    rw [hT]
    rfl

end Reinmann.ToeplitzRepresentation
