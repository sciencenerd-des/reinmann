/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.FinitePFAnalyticLimits
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn

/-!
# Analytic limits of genus-zero linear products

For summable inverse-zero norms, the finite linear products converge locally
uniformly, are entire in the limit, and converge coefficientwise with ordinary
Taylor normalization. Repeated parameters and equal moduli are allowed. This
does not identify folded Xi with such a product or prove a sector theorem.
-/
noncomputable section
namespace Reinmann.GenusZeroProductLimits
open Filter
open scoped Topology

/-- The genus-zero linear product converges locally uniformly on the whole
plane. No simplicity, modulus ordering, or nonvanishing of factors is required. -/
theorem linearProduct_locallyUniformly {ι : Type*} {u : ι → ℂ}
    (hu : Summable (fun i => ‖u i‖)) :
    HasProdLocallyUniformlyOn (fun i (z : ℂ) => 1 + u i * z)
      (fun z => ∏' i, (1 + u i * z)) Set.univ := by
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hK
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  apply Summable.hasProdUniformlyOn_one_add hK (hu.mul_right R)
  · exact Filter.Eventually.of_forall (fun i z hz => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hR z hz) (norm_nonneg _))
  · intro i
    fun_prop

/-- The limit of these finite products is entire, including at their zeros. -/
theorem linearProduct_differentiable {ι : Type*} {u : ι → ℂ}
    (hu : Summable (fun i => ‖u i‖)) :
    Differentiable ℂ (fun z => ∏' i, (1 + u i * z)) := by
  classical
  have hp : ∀ᶠ s : Finset ι in atTop,
      DifferentiableOn ℂ (fun z => ∏ i ∈ s, (1 + u i * z)) Set.univ := by
    filter_upwards with s
    fun_prop
  exact differentiableOn_univ.mp
    ((linearProduct_locallyUniformly hu).differentiableOn hp isOpen_univ)

/-- The finite-product net converges in every ordinary Taylor coefficient at
every complex centre. Repetitions are retained as separate indexed factors. -/
theorem linearProduct_ordinaryCoeff_tendsto {ι : Type*} {u : ι → ℂ}
    (hu : Summable (fun i => ‖u i‖)) (c : ℂ) (n : ℕ) :
    Tendsto (fun s : Finset ι =>
      iteratedDeriv n (fun z => ∏ i ∈ s, (1 + u i * z)) c / (n.factorial : ℂ))
      atTop (𝓝 (iteratedDeriv n (fun z => ∏' i, (1 + u i * z)) c /
        (n.factorial : ℂ))) := by
  classical
  apply FinitePFAnalyticLimits.ordinaryCoeff_tendsto
    (linearProduct_locallyUniformly hu) _ isOpen_univ (Set.mem_univ c) n
  filter_upwards with s
  fun_prop

end Reinmann.GenusZeroProductLimits
