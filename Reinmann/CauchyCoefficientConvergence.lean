/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Finite-degree coefficient convergence

For a uniformly bounded polynomial degree, values at `D + 1` distinct real
nodes determine every coefficient by Lagrange interpolation.  Consequently,
pointwise convergence of the polynomial evaluations at those nodes implies
coefficient convergence.  This is the finite-dimensional algebraic core of the
Cauchy-coefficient leg; the analytic step is only the extraction of nodewise
limits from locally uniform convergence.
-/

noncomputable section

open Filter Polynomial

namespace Reinmann

/-- Locally uniform convergence on the whole complex plane specializes to the
pointwise convergence needed at every real interpolation node. -/
theorem locallyUniformlyOn_univ_tendsto_real_node
    {ι : Type*} {φ : Filter ι} {F : ι → ℂ → ℂ} {g : ℂ → ℂ}
    (hF : TendstoLocallyUniformlyOn F g φ Set.univ) (x : ℝ) :
    Tendsto (fun n => F n (x : ℂ)) φ (nhds (g (x : ℂ))) :=
  hF.tendsto_at (Set.mem_univ _)

/- The same extraction with the real polynomial boundary made explicit.  This
is the form consumed by the interpolation theorem below: a complex locally
uniform limit of mapped real polynomials gives convergence of their real
evaluations at every real node. -/
theorem locallyUniformlyOn_univ_tendsto_mapped_real_node
    {ι : Type*} {φ : Filter ι} {p : ι → Polynomial ℝ} {f : Polynomial ℝ}
    (hF : TendstoLocallyUniformlyOn
      (fun n z => Polynomial.eval z ((p n).map (algebraMap ℝ ℂ)))
      (fun z => Polynomial.eval z (f.map (algebraMap ℝ ℂ))) φ Set.univ)
    (x : ℝ) :
    Tendsto (fun n => (p n).eval x) φ (nhds (f.eval x)) := by
  have hc := hF.tendsto_at (Set.mem_univ (x : ℂ))
  have hr := (Complex.continuous_re.tendsto _).comp hc
  have heval (q : Polynomial ℝ) :
      Polynomial.eval₂ (algebraMap ℝ ℂ) (x : ℂ) q =
        ((Polynomial.eval x q : ℝ) : ℂ) := by
    rw [show (x : ℂ) = algebraMap ℝ ℂ x by rfl,
      Polynomial.eval₂_at_apply]
    rfl
  simp only [Polynomial.eval_map] at hr
  simpa only [Function.comp_apply, heval, Complex.ofReal_re] using hr

theorem polynomial_coeff_tendsto_of_bounded_degree
    {D : ℕ} (p : ℕ → Polynomial ℝ) (f : Polynomial ℝ)
    (hdeg : ∀ j, (p j).natDegree ≤ D) (hfdeg : f.natDegree ≤ D)
    (hconv : ∀ x : ℝ,
      Tendsto (fun j => (p j).eval x) atTop (nhds (f.eval x))) :
    ∀ k : ℕ, Tendsto (fun j => (p j).coeff k) atTop (nhds (f.coeff k)) := by
  let s : Finset (Fin (D + 1)) := Finset.univ
  let v : Fin (D + 1) → ℝ := fun i => (i.val : ℝ)
  have hvs : Set.InjOn v (s : Set (Fin (D + 1))) := by
    intro i _ j _ hij
    change (i.val : ℝ) = (j.val : ℝ) at hij
    exact Fin.ext (by exact_mod_cast hij)
  have hcard : s.card = D + 1 := by
    simp [s, Fintype.card_fin]
  have hdegree_lt : ∀ j, (p j).degree < (s.card : WithBot ℕ) := by
    intro j
    rw [hcard]
    have hsucc : (D : WithBot ℕ) < ((D + 1 : ℕ) : WithBot ℕ) := by
      exact_mod_cast Nat.lt_succ_self D
    exact lt_of_le_of_lt ((Polynomial.natDegree_le_iff_degree_le).mp (hdeg j)) hsucc
  have hfdegree_lt : f.degree < (s.card : WithBot ℕ) := by
    rw [hcard]
    have hsucc : (D : WithBot ℕ) < ((D + 1 : ℕ) : WithBot ℕ) := by
      exact_mod_cast Nat.lt_succ_self D
    exact lt_of_le_of_lt ((Polynomial.natDegree_le_iff_degree_le).mp hfdeg) hsucc
  have hp_interp (j : ℕ) :
      p j = Lagrange.interpolate s v (fun i => (p j).eval (v i)) :=
    Lagrange.eq_interpolate hvs (hdegree_lt j)
  have hf_interp :
      f = Lagrange.interpolate s v (fun i => f.eval (v i)) :=
    Lagrange.eq_interpolate hvs hfdegree_lt
  intro k
  have hcoeff (j : ℕ) :
      (p j).coeff k =
        ∑ i ∈ s, (p j).eval (v i) * (Lagrange.basis s v i).coeff k := by
    calc
      (p j).coeff k =
          (Lagrange.interpolate s v (fun i => (p j).eval (v i))).coeff k := by
            exact congrArg (fun q : Polynomial ℝ => q.coeff k) (hp_interp j)
      _ = ∑ i ∈ s, (p j).eval (v i) * (Lagrange.basis s v i).coeff k := by
        rw [Lagrange.interpolate_apply, ← Polynomial.lcoeff_apply, map_sum]
        simp only [Polynomial.lcoeff_apply, Polynomial.coeff_C_mul]
  have hcoeff_f :
      f.coeff k =
        ∑ i ∈ s, f.eval (v i) * (Lagrange.basis s v i).coeff k := by
    calc
      f.coeff k =
          (Lagrange.interpolate s v (fun i => f.eval (v i))).coeff k := by
            exact congrArg (fun q : Polynomial ℝ => q.coeff k) hf_interp
      _ = ∑ i ∈ s, f.eval (v i) * (Lagrange.basis s v i).coeff k := by
        rw [Lagrange.interpolate_apply, ← Polynomial.lcoeff_apply, map_sum]
        simp only [Polynomial.lcoeff_apply, Polynomial.coeff_C_mul]
  have hsum :
      Tendsto
        (fun j => ∑ i ∈ s, (p j).eval (v i) * (Lagrange.basis s v i).coeff k)
        atTop
        (nhds (∑ i ∈ s, f.eval (v i) * (Lagrange.basis s v i).coeff k)) := by
    apply tendsto_finsetSum s
    intro i hi
    exact (hconv (v i)).mul_const _
  simpa only [hcoeff, hcoeff_f] using hsum

end Reinmann
