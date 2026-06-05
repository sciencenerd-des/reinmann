/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.RiemannSpine
import Reinmann.HilbertPolyaExperiment
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Constructing Symmetric Operators with Prescribed Real Spectrum

## What this file does (and does not) construct

The Hilbert–Pólya *operator* — a self-adjoint operator whose spectrum is exactly
the imaginary parts of the zeta zeros — cannot be constructed unconditionally:
`symmetric_eigenvalue_conj_eq` shows symmetry forces real eigenvalues, so producing
such an operator with the zeros as spectrum would *prove* RH. That is the open
problem.

What we *can* construct, genuinely and verifiably, is the **converse engine**: for
any prescribed real spectrum we build a concrete symmetric operator realizing it.
Concretely, on `EuclideanSpace ℂ ι` (finite `ι`), the real diagonal operator
`diagOp d` is symmetric (its matrix is Hermitian) and has each `d i` as an
eigenvalue with eigenvector `single i 1`.

This shows the *spectral side* of Hilbert–Pólya is not the obstruction: symmetric
operators with arbitrary real spectra are routine. The entire difficulty is
arithmetic — making the spectrum *equal the zeta zeros* — which is exactly the part
no construction here (or anywhere, yet) supplies.

## Relation to the reduction

`riemannHypothesis_of_symmetric_eigendata` (Experiment B) consumes precisely an
operator of this shape. This file demonstrates such operators exist for any real
spectrum; the missing instance is the infinite one indexed by the zeros with
eigenvalues `μ(s) = -i(s - 1/2)`, which is real iff RH.
-/

noncomputable section

open Complex Matrix
open scoped ComplexConjugate

namespace Reinmann

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A real diagonal matrix (entries cast into `ℂ`) is Hermitian. -/
theorem diagonal_real_isHermitian (d : ι → ℝ) :
    (Matrix.diagonal fun j => (d j : ℂ)).IsHermitian := by
  rw [Matrix.isHermitian_diagonal_iff]
  intro i
  change star ((d i : ℂ)) = (d i : ℂ)
  rw [Complex.star_def, Complex.conj_ofReal]

/-- The real diagonal operator on `EuclideanSpace ℂ ι`. -/
def diagOp (d : ι → ℝ) : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι :=
  (Matrix.diagonal fun j => (d j : ℂ)).toEuclideanLin

/-- The real diagonal operator is symmetric (self-adjoint), because its matrix is
Hermitian. -/
theorem diagOp_isSymmetric (d : ι → ℝ) : (diagOp d).IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.mpr (diagonal_real_isHermitian d)

/-- Each standard basis vector is an eigenvector of `diagOp d` with eigenvalue
`d i` (a real number, cast into `ℂ`). -/
theorem diagOp_eigen (d : ι → ℝ) (i : ι) :
    diagOp d (EuclideanSpace.single i 1) = (d i : ℂ) • EuclideanSpace.single i 1 := by
  apply WithLp.ofLp_injective
  unfold diagOp
  rw [Matrix.ofLp_toEuclideanLin_apply, WithLp.ofLp_smul, PiLp.ofLp_single]
  funext k
  rw [Matrix.mulVec_diagonal]
  by_cases h : k = i <;> simp [Pi.single_apply, h]

/-- **Prescribed real spectrum is realizable by a symmetric operator.**
For any finite real spectrum `d`, there is a symmetric operator on a complex
inner-product space with eigenvalue `d i` (eigenvector `single i 1`) for each `i`. -/
theorem prescribed_real_spectrum_realizable (d : ι → ℝ) :
    ∃ T : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι,
      T.IsSymmetric ∧
        ∀ i : ι, T (EuclideanSpace.single i 1) = (d i : ℂ) • EuclideanSpace.single i 1
          ∧ EuclideanSpace.single i (1 : ℂ) ≠ 0 := by
  refine ⟨diagOp d, diagOp_isSymmetric d, fun i => ⟨diagOp_eigen d i, ?_⟩⟩
  simp [EuclideanSpace.single_eq_zero_iff]

end Reinmann
