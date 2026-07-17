/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.JensenProgram
import Mathlib.Analysis.Complex.Polynomial.GaussLucas
import Mathlib.Analysis.Calculus.LocalExtr.Polynomial

/-!
# The derivative leg of the Hermite--Poulain route

This file records the part of the route that is already elementary and
formalizable: Gauss--Lucas preserves the real axis under differentiation.
The full Hermite--Poulain composition theorem and the coefficient-convergence
bridge remain separate inputs.
-/

noncomputable section

open Set Polynomial

namespace Reinmann

/-- Gauss--Lucas preserves the real axis for a positive-degree complex
polynomial whose roots already lie on the real axis. -/
theorem rootSet_derivative_subset_realAxis
    (p : ℂ[X]) (hdeg : 0 < p.degree)
    (hroot : p.rootSet ℂ ⊆ {w : ℂ | w.im = 0}) :
    p.derivative.rootSet ℂ ⊆ {w : ℂ | w.im = 0} := by
  intro z hz
  have hzmem : z ∈ p.derivative.rootSet ℂ := hz
  have hconv : Convex ℝ {w : ℂ | w.im = 0} := by
    rw [show {w : ℂ | w.im = 0} = {w : ℂ | w.im ≤ 0} ∩ {w : ℂ | 0 ≤ w.im} by
      ext w
      simp only [mem_setOf_eq, mem_inter_iff]
      constructor
      · intro hw
        exact ⟨le_of_eq hw, le_of_eq hw.symm⟩
      · rintro ⟨hle, hge⟩
        exact le_antisymm hle hge]
    exact (convex_halfSpace_im_le 0).inter (convex_halfSpace_im_ge 0)
  have hz_hull := rootSet_derivative_subset_convexHull_rootSet hdeg hzmem
  exact (convexHull_min hroot hconv) hz_hull

/-- The same statement for a real polynomial after scalar extension to `ℂ`.
The explicit map keeps the real-to-complex boundary visible to later
hyperbolicity adapters. -/
theorem mapped_derivative_rootSet_subset_realAxis
    (p : ℝ[X]) (hdeg : 0 < p.degree)
    (hroot : (p.map (algebraMap ℝ ℂ)).rootSet ℂ ⊆ {w : ℂ | w.im = 0}) :
    ((p.derivative).map (algebraMap ℝ ℂ)).rootSet ℂ ⊆ {w : ℂ | w.im = 0} := by
  simpa only [Polynomial.derivative_map] using
    rootSet_derivative_subset_realAxis (p.map (algebraMap ℝ ℂ)) (by simpa using hdeg) hroot

/-- Hyperbolicity supplies the real-axis hypothesis needed by the mapped
derivative lemma. -/
theorem polynomialHyperbolic_mapped_rootSet_subset_realAxis
    (p : ℝ[X]) (hp : PolynomialHyperbolic p) :
    (p.map (algebraMap ℝ ℂ)).rootSet ℂ ⊆ {w : ℂ | w.im = 0} := by
  intro z hz
  apply hp z
  simpa only [Polynomial.coe_aeval_eq_eval] using
    Polynomial.aeval_eq_zero_of_mem_rootSet hz

set_option maxHeartbeats 1000000 in
-- The real-to-complex root-set normalization needs the larger elaboration budget.
/-- The real-polynomial derivative leg, with the scalar extension made
explicit.  The positive-degree assumption excludes the zero derivative. -/
theorem polynomialHyperbolic_derivative_of_degree_pos
    (p : ℝ[X]) (hdeg : 0 < p.degree) (hp : PolynomialHyperbolic p) :
    PolynomialHyperbolic p.derivative := by
  intro z hz
  have hnat : 0 < p.natDegree := natDegree_pos_iff_degree_pos.mpr hdeg
  have hder : p.derivative ≠ 0 := by
    intro hzero
    have hnat0 : p.natDegree = 0 := natDegree_eq_zero_of_derivative_eq_zero hzero
    exact (Nat.ne_of_gt hnat) hnat0
  have hdermap : (p.derivative.map (algebraMap ℝ ℂ)) ≠ 0 := by
    rw [Polynomial.map_ne_zero_iff (FaithfulSMul.algebraMap_injective ℝ ℂ)]
    exact hder
  have hzmem : z ∈ (p.derivative.map (algebraMap ℝ ℂ)).rootSet ℂ := by
    rw [Polynomial.mem_rootSet]
    refine ⟨hdermap, ?_⟩
    simpa only [Polynomial.coe_aeval_eq_eval] using hz
  exact mapped_derivative_rootSet_subset_realAxis p hdeg
    (polynomialHyperbolic_mapped_rootSet_subset_realAxis p hp) hzmem

/-- Mathlib's Rolle/Gauss--Lucas root-counting bound, exposed on the RH
surface so downstream certificates can cite the exact library theorem. -/
theorem polynomial_root_count_le_derivative (p : ℝ[X]) :
    Multiset.card p.roots ≤ Multiset.card p.derivative.roots + 1 :=
  Polynomial.card_roots_le_derivative p

end Reinmann
