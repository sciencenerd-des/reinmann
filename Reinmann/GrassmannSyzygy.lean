/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.LinearCombination

/-!
# The generic Grassmann syzygy and three-term minor identity

This module is Xi-free multilinear algebra.  It formalizes, at every order,
the engine behind Fekete's gap-shrinking induction:

* **The syzygy** (`maxMinor_syzygy`): for `q + 3` row vectors in `R^(q+2)`, the
  alternating sum of the maximal `(q+2) × (q+2)` minors against any coordinate
  vanishes: `∑ i, (-1)^i · W i c · M i = 0`, where `M i` deletes row `i`.
  Proof: a `(q+3) × (q+3)` determinant with a duplicated column, Laplace
  expanded along the extra column.

* **The three-term identity** (`grassmann_three_term`): contracting the syzygy
  with the cofactor functional of `q` fixed "spectator" rows kills all but
  three terms, and sorting the surviving sub-minors into ascending row order
  (via `Fin.cycleRange` signs) gives, for any interior index `0 < t < last`,

  `M t · S(drop 0, last) = M 0 · S(drop t, last) + M last · S(drop 0, t)`,

  where `S(drop u, v)` is the order-`(q+1)` minor on the first `q + 1` columns
  whose rows are the ascending complement of `{u, v}`.

At `q = 0, 1` this specializes to the `ring`-verified gap-shrinking identities
of `Reinmann/FeketeRowGap.lean`; here it holds for **every** order, which is
what the all-orders Fekete induction consumes.
-/

namespace Reinmann

open Matrix Finset Equiv

variable {R : Type*} [CommRing R]

variable {q : ℕ}

/-! ## Row-selection embeddings and their value forms -/

/-- Value form of `Fin.succAbove`: skip the value `p`. -/
theorem val_succAbove {n : ℕ} (p : Fin (n + 1)) (i : Fin n) :
    ((p.succAbove i : Fin (n + 1)) : ℕ) =
      if (i : ℕ) < (p : ℕ) then (i : ℕ) else (i : ℕ) + 1 := by
  rcases lt_or_ge (Fin.castSucc i) p with h | h
  · rw [Fin.succAbove_of_castSucc_lt _ _ h]
    have hv : (i : ℕ) < (p : ℕ) := by simpa [Fin.lt_def] using h
    simp [hv]
  · rw [Fin.succAbove_of_le_castSucc _ _ h]
    have hv : (p : ℕ) ≤ (i : ℕ) := by simpa [Fin.le_def] using h
    simp [Nat.not_lt_of_ge hv]

/-- Ascending enumeration of the complement of the two extreme indices
`{0, last}` in `Fin (q + 3)`. -/
def dropEnds : Fin (q + 1) → Fin (q + 3) := fun a => a.succ.castSucc

/-- Ascending enumeration of the complement of `{t, last}` in `Fin (q + 3)`. -/
def dropMidLast (t : Fin (q + 3)) : Fin (q + 1) → Fin (q + 3) := fun a =>
  if (a : ℕ) < (t : ℕ) then a.castSucc.castSucc else a.succ.castSucc

/-- Ascending enumeration of the complement of `{0, t}` in `Fin (q + 3)`. -/
def dropZeroMid (t : Fin (q + 3)) : Fin (q + 1) → Fin (q + 3) := fun a =>
  if (a : ℕ) + 1 < (t : ℕ) then a.succ.castSucc else a.succ.succ

/-- The `q` spectator rows: the ascending complement of `{0, t, last}`. -/
def specRows (t : Fin (q + 3)) : Fin q → Fin (q + 3) := fun a =>
  dropMidLast t a.succ

theorem val_dropEnds (a : Fin (q + 1)) :
    ((dropEnds a : Fin (q + 3)) : ℕ) = (a : ℕ) + 1 := by
  simp [dropEnds]

theorem val_dropMidLast (t : Fin (q + 3)) (a : Fin (q + 1)) :
    ((dropMidLast t a : Fin (q + 3)) : ℕ) =
      if (a : ℕ) < (t : ℕ) then (a : ℕ) else (a : ℕ) + 1 := by
  unfold dropMidLast
  split_ifs <;> simp

theorem val_dropZeroMid (t : Fin (q + 3)) (a : Fin (q + 1)) :
    ((dropZeroMid t a : Fin (q + 3)) : ℕ) =
      if (a : ℕ) + 1 < (t : ℕ) then (a : ℕ) + 1 else (a : ℕ) + 2 := by
  unfold dropZeroMid
  split_ifs <;> simp

theorem val_specRows (t : Fin (q + 3)) (a : Fin q) :
    ((specRows t a : Fin (q + 3)) : ℕ) =
      if (a : ℕ) + 1 < (t : ℕ) then (a : ℕ) + 1 else (a : ℕ) + 2 := by
  unfold specRows
  rw [val_dropMidLast]
  simp

theorem strictMono_dropEnds : StrictMono (dropEnds (q := q)) := by
  intro a b hab
  rw [Fin.lt_def, val_dropEnds, val_dropEnds]
  exact Nat.add_lt_add_right hab 1

theorem strictMono_dropMidLast (t : Fin (q + 3)) : StrictMono (dropMidLast t) := by
  intro a b hab
  rw [Fin.lt_def, val_dropMidLast, val_dropMidLast]
  have hv : (a : ℕ) < (b : ℕ) := hab
  split_ifs <;> omega

theorem strictMono_dropZeroMid (t : Fin (q + 3)) : StrictMono (dropZeroMid t) := by
  intro a b hab
  rw [Fin.lt_def, val_dropZeroMid, val_dropZeroMid]
  have hv : (a : ℕ) < (b : ℕ) := hab
  split_ifs <;> omega

/-! ## Minors -/

/-- The maximal minor of the `(q+3) × (q+2)` family `W` deleting row `i`. -/
def maxMinor (W : Fin (q + 3) → Fin (q + 2) → R) (i : Fin (q + 3)) : R :=
  (Matrix.of (fun a b => W (i.succAbove a) b)).det

/-- The order-`(q+1)` minor of `W` on the first `q + 1` columns, with rows
selected by `e`. -/
def subMinor (W : Fin (q + 3) → Fin (q + 2) → R) (e : Fin (q + 1) → Fin (q + 3)) : R :=
  (Matrix.of (fun (a b : Fin (q + 1)) => W (e a) b.castSucc)).det

/-! ## Step A: the syzygy -/

/-- **The Grassmann syzygy.**  The alternating sum of maximal minors against
any fixed coordinate of the deleted row vanishes. -/
theorem maxMinor_syzygy (W : Fin (q + 3) → Fin (q + 2) → R) (c : Fin (q + 2)) :
    ∑ i : Fin (q + 3), (-1) ^ (i : ℕ) * W i c * maxMinor W i = 0 := by
  classical
  have hdup : (Matrix.of (fun i (j : Fin (q + 3)) => Fin.cons (W i c) (W i) j)).det = 0 := by
    apply Matrix.det_zero_of_column_eq (Fin.succ_ne_zero c).symm
    intro k
    simp
  have h : ∑ i : Fin (q + 3), (-1) ^ (i : ℕ) * W i c * maxMinor W i =
      (Matrix.of (fun i (j : Fin (q + 3)) => Fin.cons (W i c) (W i) j)).det := by
    rw [Matrix.det_succ_column_zero]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Matrix.of_apply, Fin.cons_zero]
    congr 1
  rw [h, hdup]

/-! ## Sorting a pulled-out row back into place -/

/-- Pulling row `p` of a square matrix to the front multiplies the determinant
by `(-1)^p`. -/
theorem det_cons_perm {N : ℕ} (A : Matrix (Fin (N + 1)) (Fin (N + 1)) R) (p : Fin (N + 1)) :
    (Matrix.of (Fin.cons (A p) (fun a => A (p.succAbove a)))).det =
      (-1) ^ (p : ℕ) * A.det := by
  have h0 : (p.cycleRange⁻¹) 0 = p := by
    rw [← Fin.cycleRange_self p]
    simp
  have hmat : Matrix.of (Fin.cons (A p) (fun a => A (p.succAbove a))) =
      A.submatrix (⇑(p.cycleRange⁻¹)) id := by
    ext i j
    refine Fin.cases ?_ ?_ i
    · simp [Matrix.submatrix_apply]
    · intro a
      have ha : (p.cycleRange⁻¹) a.succ = p.succAbove a := by
        rw [← Fin.cycleRange_succAbove p a]
        simp
      simp [Matrix.submatrix_apply]
  rw [hmat, Matrix.det_permute]
  rw [Equiv.Perm.sign_inv, Fin.sign_cycleRange]
  simp

/-! ## Step B: the cofactor contraction -/

/-- The order-`(q+1)` determinant with variable first row `x` (restricted to
the first `q + 1` columns) above the spectator rows. -/
def consMinor (W : Fin (q + 3) → Fin (q + 2) → R) (t : Fin (q + 3))
    (x : Fin (q + 2) → R) : R :=
  (Matrix.of (Fin.cons (fun b : Fin (q + 1) => x b.castSucc)
    (fun a b => W (specRows t a) b.castSucc))).det

/-- Laplace expansion of `consMinor` along its variable first row.  The
cofactors do not depend on `x`. -/
theorem consMinor_expand (W : Fin (q + 3) → Fin (q + 2) → R) (t : Fin (q + 3))
    (x : Fin (q + 2) → R) :
    consMinor W t x =
      ∑ b : Fin (q + 1), (-1) ^ (b : ℕ) *
        (Matrix.of (fun (a' b' : Fin q) =>
          W (specRows t a') (b.succAbove b').castSucc)).det *
        x b.castSucc := by
  unfold consMinor
  rw [Matrix.det_succ_row_zero]
  apply Finset.sum_congr rfl
  intro b _
  simp only [Matrix.of_apply, Fin.cons_zero]
  have hsub : ((Matrix.of (Fin.cons (fun b : Fin (q + 1) => x b.castSucc)
      (fun a b => W (specRows t a) b.castSucc))).submatrix Fin.succ b.succAbove) =
      Matrix.of (fun (a' b' : Fin q) =>
        W (specRows t a') (b.succAbove b').castSucc) := by
    ext a' b'
    simp [Matrix.submatrix_apply]
  rw [hsub]
  ring

/-- **Contraction of the syzygy.**  Summing the alternating minors against the
spectator cofactor functional gives zero. -/
theorem consMinor_contraction (W : Fin (q + 3) → Fin (q + 2) → R) (t : Fin (q + 3)) :
    ∑ i : Fin (q + 3), (-1) ^ (i : ℕ) * maxMinor W i * consMinor W t (W i) = 0 := by
  have hstep : ∀ i : Fin (q + 3),
      (-1) ^ (i : ℕ) * maxMinor W i * consMinor W t (W i) =
        ∑ b : Fin (q + 1),
          ((-1) ^ (b : ℕ) *
            (Matrix.of (fun (a' b' : Fin q) =>
              W (specRows t a') (b.succAbove b').castSucc)).det) *
          ((-1) ^ (i : ℕ) * W i b.castSucc * maxMinor W i) := by
    intro i
    rw [consMinor_expand, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  calc ∑ i : Fin (q + 3), (-1) ^ (i : ℕ) * maxMinor W i * consMinor W t (W i)
      = ∑ i : Fin (q + 3), ∑ b : Fin (q + 1),
          ((-1) ^ (b : ℕ) *
            (Matrix.of (fun (a' b' : Fin q) =>
              W (specRows t a') (b.succAbove b').castSucc)).det) *
          ((-1) ^ (i : ℕ) * W i b.castSucc * maxMinor W i) :=
        Finset.sum_congr rfl (fun i _ => hstep i)
    _ = ∑ b : Fin (q + 1), ∑ i : Fin (q + 3),
          ((-1) ^ (b : ℕ) *
            (Matrix.of (fun (a' b' : Fin q) =>
              W (specRows t a') (b.succAbove b').castSucc)).det) *
          ((-1) ^ (i : ℕ) * W i b.castSucc * maxMinor W i) := Finset.sum_comm
    _ = 0 := by
        apply Finset.sum_eq_zero
        intro b _
        rw [← Finset.mul_sum, maxMinor_syzygy, mul_zero]

/-- Spectator rows annihilate the contraction functional: repeating a
spectator row gives a zero determinant. -/
theorem consMinor_spec_eq_zero (W : Fin (q + 3) → Fin (q + 2) → R) (t : Fin (q + 3))
    (a : Fin q) : consMinor W t (W (specRows t a)) = 0 := by
  unfold consMinor
  apply Matrix.det_zero_of_row_eq (Fin.succ_ne_zero a).symm
  funext b
  simp

/-! ## The three sorted evaluations -/

/-- Evaluating the contraction functional at the bottom row `W 0` gives the
`{t, last}`-dropped minor, with no sign. -/
theorem consMinor_zero (W : Fin (q + 3) → Fin (q + 2) → R) (t : Fin (q + 3))
    (ht0 : 0 < t) :
    consMinor W t (W 0) = subMinor W (dropMidLast t) := by
  unfold consMinor subMinor
  congr 1
  ext i b
  refine Fin.cases ?_ ?_ i
  · have h0 : dropMidLast t 0 = 0 := by
      apply Fin.ext
      rw [val_dropMidLast]
      have hv : (0 : ℕ) < (t : ℕ) := ht0
      simp [hv]
    simp [h0]
  · intro a
    simp [specRows]

/-- Evaluating at the inserted row `W t` gives the `{0, last}`-dropped minor
with sign `(-1)^(t-1)`. -/
theorem consMinor_mid (W : Fin (q + 3) → Fin (q + 2) → R) (t : Fin (q + 3))
    (ht0 : 0 < t) (htl : t < Fin.last (q + 2)) :
    consMinor W t (W t) =
      (-1) ^ ((t : ℕ) - 1) * subMinor W (dropEnds (q := q)) := by
  have htval : 1 ≤ (t : ℕ) := ht0
  have htub : (t : ℕ) < q + 2 := htl
  obtain ⟨p, hpv⟩ : ∃ p : Fin (q + 1), (p : ℕ) = (t : ℕ) - 1 :=
    ⟨⟨(t : ℕ) - 1, by omega⟩, rfl⟩
  have hrow : (Matrix.of (fun (a b : Fin (q + 1)) => W (dropEnds a) b.castSucc)) p =
      fun b : Fin (q + 1) => W t b.castSucc := by
    funext b
    have he : dropEnds p = t := by
      apply Fin.ext
      rw [val_dropEnds, hpv]
      omega
    simp [he]
  have hrest : (fun a =>
      (Matrix.of (fun (a b : Fin (q + 1)) => W (dropEnds a) b.castSucc)) (p.succAbove a)) =
      fun (a : Fin q) (b : Fin (q + 1)) => W (specRows t a) b.castSucc := by
    funext a b
    have he : dropEnds (p.succAbove a) = specRows t a := by
      apply Fin.ext
      rw [val_dropEnds, val_specRows, val_succAbove, hpv]
      split_ifs <;> omega
    simp [he]
  have hkey := det_cons_perm
    (Matrix.of (fun (a b : Fin (q + 1)) => W (dropEnds a) b.castSucc)) p
  rw [hrow, hrest] at hkey
  unfold consMinor subMinor
  rw [hkey, hpv]

/-- Evaluating at the top row `W last` gives the `{0, t}`-dropped minor with
sign `(-1)^q`. -/
theorem consMinor_last (W : Fin (q + 3) → Fin (q + 2) → R) (t : Fin (q + 3))
    (htl : t < Fin.last (q + 2)) :
    consMinor W t (W (Fin.last (q + 2))) =
      (-1) ^ q * subMinor W (dropZeroMid t) := by
  have htub : (t : ℕ) < q + 2 := htl
  have hlastv : ((Fin.last (q + 2) : Fin (q + 3)) : ℕ) = q + 2 := rfl
  obtain ⟨p, hpv⟩ : ∃ p : Fin (q + 1), (p : ℕ) = q := ⟨Fin.last q, rfl⟩
  have hrow : (Matrix.of (fun (a b : Fin (q + 1)) => W (dropZeroMid t a) b.castSucc)) p =
      fun b : Fin (q + 1) => W (Fin.last (q + 2)) b.castSucc := by
    funext b
    have he : dropZeroMid t p = Fin.last (q + 2) := by
      apply Fin.ext
      rw [val_dropZeroMid, hpv, hlastv]
      split_ifs <;> omega
    simp [he]
  have hrest : (fun a =>
      (Matrix.of (fun (a b : Fin (q + 1)) => W (dropZeroMid t a) b.castSucc))
        (p.succAbove a)) =
      fun (a : Fin q) (b : Fin (q + 1)) => W (specRows t a) b.castSucc := by
    funext a b
    have ha := a.isLt
    have he : dropZeroMid t (p.succAbove a) = specRows t a := by
      apply Fin.ext
      rw [val_dropZeroMid, val_specRows, val_succAbove, hpv]
      split_ifs <;> omega
    simp [he]
  have hkey := det_cons_perm
    (Matrix.of (fun (a b : Fin (q + 1)) => W (dropZeroMid t a) b.castSucc)) p
  rw [hrow, hrest] at hkey
  unfold consMinor subMinor
  rw [hkey, hpv]

/-- Coverage: every index of the extended family is `0`, `t`, `last`, or a
spectator. -/
theorem eq_or_mem_specRows (t : Fin (q + 3)) (ht0 : 0 < t)
    (htl : t < Fin.last (q + 2)) (i : Fin (q + 3))
    (h0 : i ≠ 0) (ht : i ≠ t) (hl : i ≠ Fin.last (q + 2)) :
    ∃ a : Fin q, specRows t a = i := by
  have htlow : 1 ≤ (t : ℕ) := ht0
  have htub : (t : ℕ) < q + 2 := htl
  have hi0 : 1 ≤ (i : ℕ) :=
    Nat.pos_of_ne_zero fun h => h0 (Fin.ext (by simpa using h))
  have hil : (i : ℕ) ≤ q + 1 := by
    have hlt := i.isLt
    have hne : (i : ℕ) ≠ q + 2 := fun h => hl (Fin.ext (by simpa using h))
    omega
  have hit : (i : ℕ) ≠ (t : ℕ) := fun h => ht (Fin.ext h)
  by_cases hlt : (i : ℕ) < (t : ℕ)
  · obtain ⟨a, hav⟩ : ∃ a : Fin q, (a : ℕ) = (i : ℕ) - 1 :=
      ⟨⟨(i : ℕ) - 1, by omega⟩, rfl⟩
    refine ⟨a, Fin.ext ?_⟩
    rw [val_specRows, hav]
    split_ifs <;> omega
  · obtain ⟨a, hav⟩ : ∃ a : Fin q, (a : ℕ) = (i : ℕ) - 2 :=
      ⟨⟨(i : ℕ) - 2, by omega⟩, rfl⟩
    refine ⟨a, Fin.ext ?_⟩
    rw [val_specRows, hav]
    split_ifs <;> omega

private theorem neg_one_pow_mul_self (n : ℕ) : ((-1 : R)) ^ n * (-1) ^ n = 1 := by
  rw [← pow_add]
  exact Even.neg_one_pow ⟨n, by ring⟩

/-! ## The generic three-term identity -/

/-- **The generic Grassmann three-term identity.**  For any interior index
`0 < t < last` of the `(q+3) × (q+2)` family `W`:

`M t · S(drop 0, last) = M 0 · S(drop t, last) + M last · S(drop 0, t)`.

This is the all-orders gap-shrinking engine for the Fekete induction. -/
theorem grassmann_three_term (W : Fin (q + 3) → Fin (q + 2) → R) (t : Fin (q + 3))
    (ht0 : 0 < t) (htl : t < Fin.last (q + 2)) :
    maxMinor W t * subMinor W (dropEnds (q := q)) =
      maxMinor W 0 * subMinor W (dropMidLast t) +
        maxMinor W (Fin.last (q + 2)) * subMinor W (dropZeroMid t) := by
  classical
  have htval : 1 ≤ (t : ℕ) := ht0
  set f : Fin (q + 3) → R :=
    fun i => (-1) ^ (i : ℕ) * maxMinor W i * consMinor W t (W i) with hf
  have hsum : ∑ i : Fin (q + 3), f i = 0 := consMinor_contraction W t
  have hne0t : (0 : Fin (q + 3)) ≠ t := ht0.ne
  have hne0l : (0 : Fin (q + 3)) ≠ Fin.last (q + 2) := (ht0.trans htl).ne
  have hnetl : t ≠ Fin.last (q + 2) := htl.ne
  have hvanish : ∀ i ∈ Finset.univ,
      i ∉ ({0, t, Fin.last (q + 2)} : Finset (Fin (q + 3))) → f i = 0 := by
    intro i _ hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    obtain ⟨a, ha⟩ := eq_or_mem_specRows t ht0 htl i hi.1 hi.2.1 hi.2.2
    simp only [hf]
    rw [← ha, consMinor_spec_eq_zero]
    ring
  have hthree : f 0 + (f t + f (Fin.last (q + 2))) = 0 := by
    have hsubset := Finset.sum_subset
      (Finset.subset_univ ({0, t, Fin.last (q + 2)} : Finset (Fin (q + 3)))) hvanish
    rw [Finset.sum_insert (by simp [hne0t, hne0l]),
        Finset.sum_insert (by simp [hnetl]),
        Finset.sum_singleton] at hsubset
    rw [hsubset, hsum]
  have hf0 : f 0 = maxMinor W 0 * subMinor W (dropMidLast t) := by
    simp only [hf]
    rw [consMinor_zero W t ht0]
    simp
  have hft : f t = -(maxMinor W t * subMinor W (dropEnds (q := q))) := by
    simp only [hf]
    rw [consMinor_mid W t ht0 htl]
    obtain ⟨n, hn⟩ : ∃ n, (t : ℕ) = n + 1 := ⟨(t : ℕ) - 1, by omega⟩
    rw [hn]
    simp only [Nat.add_sub_cancel]
    linear_combination (-(maxMinor W t * subMinor W (dropEnds (q := q)))) *
      neg_one_pow_mul_self (R := R) n
  have hfl : f (Fin.last (q + 2)) =
      maxMinor W (Fin.last (q + 2)) * subMinor W (dropZeroMid t) := by
    simp only [hf]
    rw [consMinor_last W t htl, Fin.val_last]
    linear_combination (maxMinor W (Fin.last (q + 2)) * subMinor W (dropZeroMid t)) *
      neg_one_pow_mul_self (R := R) (q + 1)
  rw [hf0, hft, hfl] at hthree
  linear_combination -hthree

end Reinmann
