/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.HilbertPolyaExperiment

/-!
# Pseudo-Hermitian / PT Reduction to RH (Lever 3)

An *independent* operator-positivity route, distinct from the symmetric
Hilbert–Pólya reduction (`HilbertPolyaExperiment`).  The naive Hilbert–Pólya
operator is self-adjoint w.r.t. the *ambient* inner product; that is exactly the
obstruction (no such bounded/total operator is known).  The pseudo-Hermitian
viewpoint (Mostafazadeh; Bender–Brody–Müller) **drops the ambient inner product
entirely** and asks only for a *positive metric* `η` — a positive-definite
sesquilinear form — with respect to which the operator is self-adjoint.

The key fact, proved here from the form laws alone (no `InnerProductSpace`
instance, no completeness, no boundedness):

> **An operator self-adjoint w.r.t. a nondegenerate sesquilinear form has, on any
> eigenvector, an eigenvalue fixed by conjugation — hence real.**

This is the operator-theoretic analogue of "unbroken PT ⟺ real spectrum": the
positivity (nondegeneracy) of the metric `η` forces reality of the spectrum.

* `PseudoHermitianForm` — a metric `η` making `T` `η`-self-adjoint, with `η`
  nondegenerate (the trace of positive-definiteness actually used).
* `PseudoHermitianForm.eigenvalue_conj_eq` — `η`-self-adjoint ⟹ real eigenvalues.
* `riemannHypothesis_of_pseudoHermitian_eigendata` — if the critical-strip zeros
  are realized as the `η`-self-adjoint spectrum via `spectralParam s = -i(s-1/2)`,
  then RH.

## Honest scope

This is a **reduction**, formalized and verified: it converts RH into the
*existence* of `(E, T, η)` with `η` a positive metric and the prescribed spectrum.
That existence is the open analytic/operator-theoretic content (BBM gave only a
formal construction).  Nothing here proves that existence; the reduction is
assumption-free (reduces only to `[propext, Classical.choice, Quot.sound]`) and
uses only the metric, never the ambient inner product — so it is genuinely
independent of the symmetric route.
-/

noncomputable section

open Complex
open scoped ComplexConjugate

namespace Reinmann

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- A **positive (pseudo-Hermitian) metric** `η` making the operator `T`
`η`-self-adjoint.  `η` is sesquilinear (linear in the left slot, conjugate-linear
in the right) and **nondegenerate** (`η x x ≠ 0` for `x ≠ 0`) — the property that a
positive-definite metric supplies.  No ambient inner product is used. -/
structure PseudoHermitianForm (T : E →ₗ[ℂ] E) where
  /-- The metric form. -/
  η : E → E → ℂ
  /-- Linearity in the left slot. -/
  smul_left : ∀ (c : ℂ) (x y : E), η (c • x) y = c * η x y
  /-- Conjugate-linearity in the right slot. -/
  smul_right : ∀ (c : ℂ) (x y : E), η x (c • y) = conj c * η x y
  /-- `T` is self-adjoint with respect to `η`. -/
  selfAdjoint : ∀ x y : E, η (T x) y = η x (T y)
  /-- The metric is nondegenerate (supplied by positive-definiteness). -/
  nondegenerate : ∀ x : E, x ≠ 0 → η x x ≠ 0

/-- **`η`-self-adjoint ⟹ real eigenvalues.** For an eigenpair `T v = μ • v` with
`v ≠ 0`, the eigenvalue is fixed by conjugation.  Proof from the metric laws:
`μ · η v v = η(Tv,v) = η(v,Tv) = conj μ · η v v`, and `η v v ≠ 0`. -/
theorem PseudoHermitianForm.eigenvalue_conj_eq {T : E →ₗ[ℂ] E}
    (P : PseudoHermitianForm T) {μ : ℂ} {v : E} (hv : v ≠ 0) (hev : T v = μ • v) :
    conj μ = μ := by
  have h1 : P.η (T v) v = μ * P.η v v := by rw [hev, P.smul_left]
  have h2 : P.η v (T v) = conj μ * P.η v v := by rw [hev, P.smul_right]
  have hsa : P.η (T v) v = P.η v (T v) := P.selfAdjoint v v
  rw [h1, h2] at hsa
  exact (mul_right_cancel₀ (P.nondegenerate v hv) hsa).symm

/-- **Pseudo-Hermitian reduction to RH.** If there is a complex vector space `E`, an
operator `T`, and a positive metric `η` making `T` `η`-self-adjoint, such that every
critical-strip zero `s` has a nonzero eigenvector with eigenvalue
`μ(s) = -i(s - 1/2)`, then RH holds.

Reality of `μ(s)` is *proved* from `η`-positivity (not assumed); it pins
`Re s = 1/2`. -/
theorem riemannHypothesis_of_pseudoHermitian_eigendata
    (T : E →ₗ[ℂ] E) (P : PseudoHermitianForm T)
    (v : ℂ → E)
    (hv : ∀ s, riemannZeta s = 0 → 0 < s.re → s.re < 1 → v s ≠ 0)
    (heig : ∀ s, riemannZeta s = 0 → 0 < s.re → s.re < 1 →
        T (v s) = spectralParam s • v s) :
    RiemannHypothesis := by
  rw [← criticalStripObligations_iff_riemannHypothesis]
  refine ⟨fun s hpos hlt hz => ?_⟩
  have hμ : conj (spectralParam s) = spectralParam s :=
    P.eigenvalue_conj_eq (hv s hz hpos hlt) (heig s hz hpos hlt)
  have him : (spectralParam s).im = 0 := Complex.conj_eq_iff_im.mp hμ
  exact (spectralParam_real_iff s).mp him

/-- A bundled pseudo-Hermitian witness for RH. -/
structure PseudoHermitianWitness where
  /-- The carrier space. -/
  E : Type
  [addCommGroup : AddCommGroup E]
  [module : Module ℂ E]
  /-- The operator. -/
  T : E →ₗ[ℂ] E
  /-- The positive metric making `T` self-adjoint. -/
  form : PseudoHermitianForm T
  /-- Eigenvectors indexed by zeros. -/
  v : ℂ → E
  v_ne : ∀ s, riemannZeta s = 0 → 0 < s.re → s.re < 1 → v s ≠ 0
  eig : ∀ s, riemannZeta s = 0 → 0 < s.re → s.re < 1 →
      T (v s) = spectralParam s • v s

attribute [instance] PseudoHermitianWitness.addCommGroup PseudoHermitianWitness.module

/-- A pseudo-Hermitian witness proves RH. -/
theorem riemannHypothesis_of_pseudoHermitianWitness (W : PseudoHermitianWitness) :
    RiemannHypothesis :=
  riemannHypothesis_of_pseudoHermitian_eigendata W.T W.form W.v W.v_ne W.eig

end Reinmann
