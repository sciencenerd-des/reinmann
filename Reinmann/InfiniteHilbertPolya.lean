/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.HilbertPolyaExperiment
import Reinmann.RiemannSpine

/-!
# The Infinite-Dimensional Hilbert–Pólya Witness

`riemannHypothesis_of_symmetric_eigendata` is already **polymorphic in the carrier
space `E`**: it accepts any complex inner-product space, finite- or
infinite-dimensional. So the *sufficiency* direction of Hilbert–Pólya holds
verbatim for an infinite operator — no new theorem is needed. This file simply
**packages** the infinite witness as a bundled structure and records the honest
status of its existence.

* `HilbertPolyaWitness'`: a complex inner-product space with a symmetric operator
  carrying eigenvalue `μ(s) = -i(s-1/2)` at a nonzero eigenvector for **every**
  critical-strip zero `s`.
* `riemannHypothesis_of_hilbertPolyaWitness'`: such a witness implies RH.

## Honest status of existence (open mathematics)

Constructing a witness is the **Hilbert–Pólya conjecture** — open since 1914. The
naive model (diagonal "multiplication by the height" on `ℓ²` over the zero set)
**fails to be a total linear operator**: the heights `γ_n → ∞`, so the diagonal
multiplier is unbounded and is *not defined on all of `ℓ²`* (only on a dense
domain). A genuine witness therefore needs either unbounded self-adjoint operator
theory (domains, essential self-adjointness) or a fundamentally different
construction (de Branges spaces, a geometric/spectral realization). None is
available, here or anywhere. We do **not** assert existence.
-/

noncomputable section

open Complex

namespace Reinmann

/-- A bundled (possibly infinite-dimensional) Hilbert–Pólya witness. -/
structure HilbertPolyaWitness' where
  /-- The carrier Hilbert space. -/
  E : Type
  [normedAddCommGroup : NormedAddCommGroup E]
  [innerProductSpace : InnerProductSpace ℂ E]
  /-- The (symmetric) operator. -/
  T : E →ₗ[ℂ] E
  /-- Symmetry of `T`. -/
  hT : T.IsSymmetric
  /-- The eigenvector attached to each zero. -/
  v : ℂ → E
  /-- Eigenvectors are nonzero on the critical strip. -/
  hv : ∀ s, riemannZeta s = 0 → 0 < s.re → s.re < 1 → v s ≠ 0
  /-- `μ(s) = -i(s-1/2)` is the eigenvalue at `v s`. -/
  heig : ∀ s, riemannZeta s = 0 → 0 < s.re → s.re < 1 →
    T (v s) = spectralParam s • v s

attribute [instance] HilbertPolyaWitness'.normedAddCommGroup
  HilbertPolyaWitness'.innerProductSpace

/-- **An infinite-dimensional Hilbert–Pólya witness implies RH.** (Sufficiency is
inherited verbatim from the polymorphic `riemannHypothesis_of_symmetric_eigendata`;
existence of a witness is the open Hilbert–Pólya conjecture.) -/
theorem riemannHypothesis_of_hilbertPolyaWitness' (w : HilbertPolyaWitness') :
    RiemannHypothesis :=
  riemannHypothesis_of_symmetric_eigendata w.T w.hT w.v w.hv w.heig

end Reinmann
