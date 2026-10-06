import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Coupled Galerkin rank energy

The inner product represents the positive shifted-form energy. Instantiating
it for the infinite Weil form requires a separately proved coercivity result.
No constrained gap or boundary estimate is assumed to have been established.
-/
noncomputable section
namespace Reinmann.CoupledRankEnergy
open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Galerkin agreement on the old space makes the increment orthogonal to it. -/
theorem galerkin_increment_orthogonal (K : Submodule ℝ H) (u v : H)
    (h : ∀ x ∈ K, inner ℝ u x = inner ℝ v x) :
    ∀ x ∈ K, inner ℝ (v - u) x = 0 := by
  intro x hx
  rw [inner_sub_left, ← h x hx, sub_self]

/-- Exact energy gain, with cancellation retained. -/
theorem energy_increment (u v : H) (h : inner ℝ (v - u) u = 0) :
    ‖v - u‖ ^ 2 = ‖v‖ ^ 2 - ‖u‖ ^ 2 := by
  have he := norm_add_sq_real (v - u) u
  simp only [sub_add_cancel, h, mul_zero, add_zero] at he
  linarith

/-- Mixed old-space terms vanish before estimating the new pairing. -/
theorem pairing_increment (u v g h : H)
    (h₁ : inner ℝ (v - u) g = 0) (h₂ : inner ℝ u (h - g) = 0) :
    inner ℝ v h - inner ℝ u g = inner ℝ (v - u) (h - g) := by
  simp only [inner_sub_left, inner_sub_right] at *
  linarith

/-- A finite cumulative budget couples the same rank increments. -/
theorem cumulative_pairing_budget {ι : Type*} (s : Finset ι)
    (du dg : ι → H) :
    (∑ i ∈ s, |inner ℝ (du i) (dg i)|) ^ 2 ≤
      (∑ i ∈ s, ‖du i‖ ^ 2) * (∑ i ∈ s, ‖dg i‖ ^ 2) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
  · intro i hi
    positivity
  · intro i hi
    positivity
  · intro i hi
    have h := abs_real_inner_le_norm (du i) (dg i)
    have hs := sq_le_sq₀ (abs_nonneg (inner ℝ (du i) (dg i)))
      (mul_nonneg (norm_nonneg (du i)) (norm_nonneg (dg i)))
    simpa only [mul_pow] using hs.2 h

/-- Nested Galerkin increments telescope to endpoint energy differences. -/
theorem cumulative_galerkin_budget (u g : ℕ → H) (N : ℕ)
    (hu : ∀ i, inner ℝ (u (i + 1) - u i) (u i) = 0)
    (hg : ∀ i, inner ℝ (g (i + 1) - g i) (g i) = 0)
    (hug : ∀ i, inner ℝ (u (i + 1) - u i) (g i) = 0)
    (hgu : ∀ i, inner ℝ (u i) (g (i + 1) - g i) = 0) :
    (∑ i ∈ Finset.range N,
      |inner ℝ (u (i + 1)) (g (i + 1)) - inner ℝ (u i) (g i)|) ^ 2 ≤
      (‖u N‖ ^ 2 - ‖u 0‖ ^ 2) * (‖g N‖ ^ 2 - ‖g 0‖ ^ 2) := by
  have he : (∑ i ∈ Finset.range N, ‖u (i + 1) - u i‖ ^ 2) =
      ‖u N‖ ^ 2 - ‖u 0‖ ^ 2 := by
    simp_rw [energy_increment _ _ (hu _)]
    exact Finset.sum_range_sub (fun i => ‖u i‖ ^ 2) N
  have hd : (∑ i ∈ Finset.range N, ‖g (i + 1) - g i‖ ^ 2) =
      ‖g N‖ ^ 2 - ‖g 0‖ ^ 2 := by
    simp_rw [energy_increment _ _ (hg _)]
    exact Finset.sum_range_sub (fun i => ‖g i‖ ^ 2) N
  simp_rw [pairing_increment _ _ _ _ (hug _) (hgu _)]
  simpa only [he, hd] using cumulative_pairing_budget (Finset.range N)
    (fun i => u (i + 1) - u i) (fun i => g (i + 1) - g i)

/-- The finite estimate at every rank, under explicit endpoint-energy bounds. -/
theorem uniform_galerkin_budget (u g : ℕ → H) (Eu Eg : ℝ)
    (hEu : 0 ≤ Eu) (hEg : 0 ≤ Eg)
    (hu : ∀ i, inner ℝ (u (i + 1) - u i) (u i) = 0)
    (hg : ∀ i, inner ℝ (g (i + 1) - g i) (g i) = 0)
    (hug : ∀ i, inner ℝ (u (i + 1) - u i) (g i) = 0)
    (hgu : ∀ i, inner ℝ (u i) (g (i + 1) - g i) = 0)
    (hbu : ∀ N, ‖u N‖ ^ 2 - ‖u 0‖ ^ 2 ≤ Eu)
    (hbg : ∀ N, ‖g N‖ ^ 2 - ‖g 0‖ ^ 2 ≤ Eg) (N : ℕ) :
    (∑ i ∈ Finset.range N,
      |inner ℝ (u (i + 1)) (g (i + 1)) - inner ℝ (u i) (g i)|) ≤
      Real.sqrt (Eu * Eg) := by
  have hgpos : 0 ≤ ‖g N‖ ^ 2 - ‖g 0‖ ^ 2 := by
    have hs : (∑ i ∈ Finset.range N, ‖g (i + 1) - g i‖ ^ 2) =
        ‖g N‖ ^ 2 - ‖g 0‖ ^ 2 := by
      simp_rw [energy_increment _ _ (hg _)]
      exact Finset.sum_range_sub (fun i => ‖g i‖ ^ 2) N
    rw [← hs]
    exact Finset.sum_nonneg (fun i hi => sq_nonneg _)
  apply Real.le_sqrt_of_sq_le
  exact (cumulative_galerkin_budget u g N hu hg hug hgu).trans
    (mul_le_mul (hbu N) (hbg N) hgpos hEu)

/-- A genuine infinite-series conclusion; the energy bounds remain hypotheses.
This is not an assertion that the Weil ground family satisfies those bounds. -/
theorem absolute_rank_summability (u g : ℕ → H) (Eu Eg : ℝ)
    (hEu : 0 ≤ Eu) (hEg : 0 ≤ Eg)
    (hu : ∀ i, inner ℝ (u (i + 1) - u i) (u i) = 0)
    (hg : ∀ i, inner ℝ (g (i + 1) - g i) (g i) = 0)
    (hug : ∀ i, inner ℝ (u (i + 1) - u i) (g i) = 0)
    (hgu : ∀ i, inner ℝ (u i) (g (i + 1) - g i) = 0)
    (hbu : ∀ N, ‖u N‖ ^ 2 - ‖u 0‖ ^ 2 ≤ Eu)
    (hbg : ∀ N, ‖g N‖ ^ 2 - ‖g 0‖ ^ 2 ≤ Eg) :
    Summable (fun i =>
      |inner ℝ (u (i + 1)) (g (i + 1)) - inner ℝ (u i) (g i)|) ∧
    (∑' i, |inner ℝ (u (i + 1)) (g (i + 1)) - inner ℝ (u i) (g i)|) ≤
      Real.sqrt (Eu * Eg) := by
  have hb := uniform_galerkin_budget u g Eu Eg hEu hEg hu hg hug hgu hbu hbg
  exact ⟨summable_of_sum_range_le (fun i => abs_nonneg _) hb,
    Real.tsum_le_of_sum_range_le (fun i => abs_nonneg _) hb⟩

end Reinmann.CoupledRankEnergy
