/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Basic
import Mathlib.Algebra.Polynomial.Roots

/-!
# Hermite-Poulter-Obreschkoff Theorem

This module formalizes the theorem that the locally uniform limit of polynomials
with purely real roots is an entire function whose zeros are also purely real
(or the function is identically zero).
-/

noncomputable section

open Set Metric Filter Complex Topology

namespace Reinmann

/-- The Hermite-Poulter-Obreschkoff theorem in its limit form:
If a sequence of real-rooted polynomials (or more generally, entire functions
with only real zeros) converges locally uniformly to a limit function `g`,
then `g` also has only real zeros (or is identically zero). -/
def HermitePoulterObreschkoff : Prop :=
  ∀ {ι : Type*} {p : Filter ι} [NeBot p]
    {f : ι → ℂ → ℂ} {g : ℂ → ℂ},
    TendstoLocallyUniformlyOn f g p univ →
    (∀ᶠ n in p, DifferentiableOn ℂ (f n) univ) →
    (∀ᶠ n in p, ∀ z : ℂ, f n z = 0 → z.im = 0) →
    (∀ z : ℂ, g z = 0) ∨ (∀ z : ℂ, g z = 0 → z.im = 0)

end Reinmann
