/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.ConjugateHalfPlane
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Hadamard

/-!
# ζ Growth Bounds on Vertical Lines (Prerequisite M4)

Toward a strip zero-free region, the Hadamard three-lines interpolation
(**already in Mathlib**: `Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'`)
needs *edge bounds* on `ζ`. This file supplies the right edge: on any line
`Re s = σ > 1`, `ζ` is bounded by the convergent real Dirichlet series, a bound
that **depends only on `σ`**.

* `norm_dirichlet_term`: `‖1/(n:ℂ)^s‖ = (n:ℝ)^(-Re s)` for `n ≥ 1`.
* `norm_riemannZeta_le_realSeries`: `‖ζ(s)‖ ≤ ∑' n, [n=0 ↦ 0 | (n:ℝ)^(-Re s)]`.
* `norm_riemannZeta_bddAbove_re_eq`: the bound is constant along each vertical line.

The Hadamard three-lines theorem (M3) is identified below as the Mathlib lemma to
combine with these edge bounds and a functional-equation bound on the left edge to
obtain the strip convexity estimate. That assembly (plus the left-edge functional
bound) is the remaining work for a genuine quantitative region.
-/

noncomputable section

open Complex

namespace Reinmann

/-- The Dirichlet-series term norm depends only on `Re s`. -/
theorem norm_dirichlet_term {n : ℕ} (hn : 0 < n) (s : ℂ) :
    ‖1 / (n : ℂ) ^ s‖ = (n : ℝ) ^ (-s.re) := by
  rw [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos hn,
    Real.rpow_neg (Nat.cast_nonneg n), one_div]

/-- The real Dirichlet majorant at real part `σ`. -/
def reSeriesMajorant (σ : ℝ) : ℝ :=
  ∑' n : ℕ, (if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-σ))

/-- **ζ edge bound.** On `Re s > 1`, `‖ζ(s)‖` is bounded by the convergent real
Dirichlet series at `Re s` — a bound depending only on `Re s`. -/
theorem norm_riemannZeta_le_realSeries {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZeta s‖ ≤ reSeriesMajorant s.re := by
  rw [dirichletSeries_eq_riemannZeta s hs]
  refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq ?_)
  · -- summability of the norms
    have h : Summable fun n : ℕ => ‖(if n = 0 then (0 : ℂ) else 1 / (n : ℂ) ^ s)‖ :=
      (summable_dirichletSeries_terms s hs).norm
    exact h
  · -- termwise norm = real majorant term
    unfold reSeriesMajorant
    congr 1
    funext n
    by_cases hn : n = 0
    · simp [hn]
    · simp only [hn, if_false]
      exact norm_dirichlet_term (Nat.pos_of_ne_zero hn) s

/-!
## The Hadamard three-lines prerequisite (M3) — available in Mathlib

The log-convex interpolation bound is
`Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'`:
for `f` bounded, continuous on `re ⁻¹' [l,u]`, differentiable on `re ⁻¹' (l,u)`,
with `‖f‖ ≤ a` on `Re = l` and `‖f‖ ≤ b` on `Re = u`,

  `‖f z‖ ≤ a ^ (1 - (z.re - l)/(u - l)) · b ^ ((z.re - l)/(u - l))`.

Combined with `norm_riemannZeta_le_realSeries` (the right edge `Re = u > 1`) and a
functional-equation bound on a left edge, this yields the strip growth estimate
that drives a quantitative zero-free region. That assembly (and the left-edge
functional bound) is the remaining work.
-/

end Reinmann
