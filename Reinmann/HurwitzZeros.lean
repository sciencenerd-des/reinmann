/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Hurwitz's Theorem on Zeros of Holomorphic Functions

This module formalizes the statement of Hurwitz's theorem, which is essential
for establishing that the locally uniform limit of real-rooted polynomials
(or entire functions) can only have real roots.

The core mechanism is that if the limit function has an isolated zero,
the argument principle forces the approximants to eventually have zeros
arbitrarily close to it.
-/

noncomputable section

open Set Metric Filter Complex Topology

namespace Reinmann

/-- Hurwitz's theorem states that if a sequence of holomorphic functions `f_n`
converges locally uniformly to a non-constant limit `f` on an open set `U`,
and `z₀ ∈ U` is an isolated zero of `f`, then for every sufficiently small
radius `r > 0`, the approximants `f_n` must eventually have a zero in the
disk `ball z₀ r`. -/
def HurwitzTheoremIsolatedZero : Prop :=
  ∀ {ι : Type*} {p : Filter ι} [NeBot p]
    {f : ι → ℂ → ℂ} {g : ℂ → ℂ} {U : Set ℂ} {z₀ : ℂ} {r : ℝ},
    IsOpen U →
    z₀ ∈ U →
    TendstoLocallyUniformlyOn f g p U →
    (∀ᶠ n in p, DifferentiableOn ℂ (f n) U) →
    g z₀ = 0 →
    (∃ δ > 0, closedBall z₀ δ ⊆ U ∧ ∀ z ∈ closedBall z₀ δ, z ≠ z₀ → g z ≠ 0) →
    (0 < r) →
    closedBall z₀ r ⊆ U →
    (∀ z ∈ sphere z₀ r, g z ≠ 0) →
    ∀ᶠ n in p, ∃ z ∈ ball z₀ r, f n z = 0

/-- A corollary of Hurwitz's theorem for zero-free regions: if all `f_n` are
zero-free on an open connected set `U`, and they converge locally uniformly to
`g`, then `g` is either identically zero on `U` or zero-free on `U`.
(We state the local contrapositive: if `g` has a zero and is not identically zero,
then `f_n` must have zeros.) -/
def HurwitzTheoremZeroFree : Prop :=
  ∀ {ι : Type*} {p : Filter ι} [NeBot p]
    {f : ι → ℂ → ℂ} {g : ℂ → ℂ} {U : Set ℂ},
    IsOpen U →
    IsConnected U →
    TendstoLocallyUniformlyOn f g p U →
    (∀ᶠ n in p, DifferentiableOn ℂ (f n) U) →
    (∀ᶠ n in p, ∀ z ∈ U, f n z ≠ 0) →
    (∀ z ∈ U, g z = 0) ∨ (∀ z ∈ U, g z ≠ 0)

end Reinmann
