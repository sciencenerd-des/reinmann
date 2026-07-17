/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

/-!
# Dodgson's Condensation and Sylvester's Determinant Identity

This module states Dodgson's condensation identity (Sylvester's identity
for minors of size k-1 and k-2) for square matrices. This serves as the
algebraic foundation for the inductive lift from contiguous to arbitrary minors
in the Toeplitz total positivity proof.  The identity is kept as a theorem
target until its determinant proof is formalized.
-/

noncomputable section

open Matrix

namespace Reinmann

/-- Sylvester's determinant identity (Dodgson's condensation) for a matrix A of size k ≥ 2.
We represent the submatrices by shifting indices:
- `A_tl` (top-left): remove last row and last column.
- `A_br` (bottom-right): remove first row and first column.
- `A_tr` (top-right): remove last row and first column.
- `A_bl` (bottom-left): remove first row and last column.
- `A_mid` (middle): remove first and last rows and columns.
-/
def DodgsonCondensationIdentity : Prop :=
  ∀ (k : ℕ), 2 ≤ k → ∀ A : Matrix (Fin k) (Fin k) ℝ,
    let A_tl := Matrix.of (fun (i j : Fin (k - 1)) => A ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)
    let A_br := Matrix.of (fun (i j : Fin (k - 1)) =>
      A ⟨i.val + 1, by omega⟩ ⟨j.val + 1, by omega⟩)
    let A_tr := Matrix.of (fun (i j : Fin (k - 1)) =>
      A ⟨i.val, by omega⟩ ⟨j.val + 1, by omega⟩)
    let A_bl := Matrix.of (fun (i j : Fin (k - 1)) =>
      A ⟨i.val + 1, by omega⟩ ⟨j.val, by omega⟩)
    let A_mid := Matrix.of (fun (i j : Fin (k - 2)) =>
      A ⟨i.val + 1, by omega⟩ ⟨j.val + 1, by omega⟩)
    A.det * A_mid.det = A_tl.det * A_br.det - A_tr.det * A_bl.det

/-- The size-two base case of Dodgson condensation.  This is the ordinary
`2 × 2` determinant identity; the all-size induction remains a separate
theorem target. -/
theorem dodgsonCondensationIdentity_fin_two (A : Matrix (Fin 2) (Fin 2) ℝ) :
    let A_tl := Matrix.of (fun (i j : Fin (2 - 1)) =>
      A ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)
    let A_br := Matrix.of (fun (i j : Fin (2 - 1)) =>
      A ⟨i.val + 1, by omega⟩ ⟨j.val + 1, by omega⟩)
    let A_tr := Matrix.of (fun (i j : Fin (2 - 1)) =>
      A ⟨i.val, by omega⟩ ⟨j.val + 1, by omega⟩)
    let A_bl := Matrix.of (fun (i j : Fin (2 - 1)) =>
      A ⟨i.val + 1, by omega⟩ ⟨j.val, by omega⟩)
    let A_mid := Matrix.of (fun (i j : Fin (2 - 2)) =>
      A ⟨i.val + 1, by omega⟩ ⟨j.val + 1, by omega⟩)
    A.det * A_mid.det = A_tl.det * A_br.det - A_tr.det * A_bl.det := by
  simp [Matrix.det_fin_two]

/-- The explicit size-three condensation case.  This checks the first
nontrivial instance of the identity before attempting a generic determinant
proof. -/
theorem dodgsonCondensationIdentity_fin_three (A : Matrix (Fin 3) (Fin 3) ℝ) :
    let A_tl := Matrix.of (fun (i j : Fin (3 - 1)) =>
      A ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)
    let A_br := Matrix.of (fun (i j : Fin (3 - 1)) =>
      A ⟨i.val + 1, by omega⟩ ⟨j.val + 1, by omega⟩)
    let A_tr := Matrix.of (fun (i j : Fin (3 - 1)) =>
      A ⟨i.val, by omega⟩ ⟨j.val + 1, by omega⟩)
    let A_bl := Matrix.of (fun (i j : Fin (3 - 1)) =>
      A ⟨i.val + 1, by omega⟩ ⟨j.val, by omega⟩)
    let A_mid := Matrix.of (fun (i j : Fin (3 - 2)) =>
      A ⟨i.val + 1, by omega⟩ ⟨j.val + 1, by omega⟩)
    A.det * A_mid.det = A_tl.det * A_br.det - A_tr.det * A_bl.det := by
  simp [Matrix.det_fin_three, Matrix.det_fin_two]
  ring

end Reinmann
