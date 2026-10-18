/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.SplitPairPatchedRemainder
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow

/-! Actual ordinary Taylor coefficients of the patched reciprocal.
The factorial normalization is explicit; these are not Jensen coefficients. -/
noncomputable section
namespace Reinmann.SplitPairCoefficientIdentity
open Set Filter Finset
open scoped Topology

/-- The residue sign and geometric ratio in the principal-part Taylor series. -/
theorem principal_coefficient {a r : ℂ} (ha : a ≠ 0) (n : ℕ) :
    SplitPairCauchyTail.coefficient (fun z => r / (z - a)) n = (-r / a) * (1 / a) ^ n := by
  have hb := iteratedDerivWithin_one_div (𝕜 := ℂ) n isOpen_univ (x := -a) (mem_univ _)
  rw [iteratedDerivWithin_univ] at hb
  dsimp only at hb
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero n)
  unfold SplitPairCauchyTail.coefficient
  rw [show (fun z : ℂ => r / (z - a)) = (fun z => r * (1 / (z - a))) by ext z; ring,
    iteratedDeriv_const_mul_field, iteratedDeriv_comp_sub_const]
  simp only [zero_sub]
  rw [hb]
  rw [show (-1 - (n : ℤ)) = -((n + 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast,
    pow_succ, neg_pow]
  field_simp [ha, hn]
  have hc : a^n*a⁻¹^n = 1 := by rw [← mul_pow, mul_inv_cancel₀ ha, one_pow]
  linear_combination r*(-1)^n*hc

/-- Function equality in a neighbourhood produces coefficient equality;
the decomposition is proved from the functions, not assumed for the sequence. -/
theorem coefficient_identity {ι : Type*} [Fintype ι]
    {F g : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) (hF0 : F 0 ≠ 0)
    (hg : AnalyticAt ℂ g 0) (a r : ι → ℂ) (ha : ∀ i, a i ≠ 0)
    (heq : ∀ z, (∀ i, z ≠ a i) → (F z)⁻¹ = (∑ i, r i / (z - a i)) + g z)
    (n : ℕ) :
    SplitPairCauchyTail.coefficient (fun z => (F z)⁻¹) n =
      (∑ i, (-r i / a i) * (1 / a i) ^ n) + SplitPairCauchyTail.coefficient g n := by
  have hp (i : ι) : AnalyticAt ℂ (fun z => r i / (z - a i)) 0 :=
    analyticAt_const.div (analyticAt_id.sub analyticAt_const)
      (by simpa using ha i)
  have hx : (fun z => (F z)⁻¹) =ᶠ[𝓝 0] (fun z => (∑ i, r i / (z - a i)) + g z) := by
    have hne : ∀ᶠ z in 𝓝 (0 : ℂ), ∀ i, z ≠ a i :=
      eventually_all.mpr (fun i => eventually_ne_nhds (Ne.symm (ha i)))
    filter_upwards [hne] with z hz
    exact heq z hz
  have hd := hx.iteratedDeriv_eq n
  rw [iteratedDeriv_fun_add (Finset.analyticAt_fun_sum _ (fun i _ => hp i)).contDiffAt
      hg.contDiffAt, iteratedDeriv_fun_sum (fun i _ => (hp i).contDiffAt)] at hd
  unfold SplitPairCauchyTail.coefficient
  rw [hd, add_div, sum_div]
  congr 1
  apply sum_congr rfl
  intro i _
  exact principal_coefficient (ha i) n

/-- An actual common analytic remainder with the exact ordinary coefficient
identity. This standalone simple-pole statement is not a general Edrei theorem. -/
theorem actual_remainder_with_coefficients {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : ℂ → ℂ} (hF : Differentiable ℂ F) (hF0 : F 0 ≠ 0) (a : ι → ℂ)
    (ha : Function.Injective a) (hzero : ∀ i, F (a i) = 0)
    (hsimple : ∀ i, deriv F (a i) ≠ 0) {R : ℝ} (hR : 0 < R)
    (hall : ∀ z ∈ Metric.closedBall 0 R, F z = 0 → ∃ i, z = a i) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (Metric.closedBall 0 R) ∧
      ∀ n, SplitPairCauchyTail.coefficient (fun z => (F z)⁻¹) n =
        (∑ i, (-(deriv F (a i))⁻¹ / a i) * (1 / a i) ^ n) + SplitPairCauchyTail.coefficient g n := by
  obtain ⟨g, hg, heq⟩ := SplitPairPatchedRemainder.actual_simple_pole_remainder
    hF a ha hzero hsimple (Metric.closedBall 0 R) hall
  refine ⟨g, hg, ?_⟩
  intro n
  apply coefficient_identity (hF.analyticAt 0) hF0
    (hg 0 (by simp [hR.le])) a (fun i => (deriv F (a i))⁻¹) ?_ heq n
  intro i hi
  exact hF0 (hi ▸ hzero i)

/-- Cauchy decay now follows from the constructed common analytic remainder;
neither the coefficient decomposition nor its exponential error is assumed. -/
theorem actual_reciprocal_coefficient_error {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : ℂ → ℂ} (hF : Differentiable ℂ F) (hF0 : F 0 ≠ 0) (a : ι → ℂ)
    (ha : Function.Injective a) (hzero : ∀ i, F (a i) = 0)
    (hsimple : ∀ i, deriv F (a i) ≠ 0) {R : ℝ} (hR : 0 < R)
    (hall : ∀ z ∈ Metric.closedBall 0 R, F z = 0 → ∃ i, z = a i) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
      ‖SplitPairCauchyTail.coefficient (fun z => (F z)⁻¹) n -
        ∑ i, (-(deriv F (a i))⁻¹/a i)*(1/a i)^n‖ ≤ C/R^n := by
  obtain ⟨g,hg,heq⟩ := actual_remainder_with_coefficients hF hF0 a ha hzero hsimple hR hall
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    hg.continuousOn
  have hC0 : 0 ≤ C := (norm_nonneg (g 0)).trans (hC 0 (by simp [hR.le]))
  refine ⟨C,hC0,?_⟩
  intro n
  exact SplitPairCauchyTail.finite_pole_coefficient_error heq hR
    (hg.differentiableOn.diffContOnCl_ball (Set.Subset.refl _))
    (fun z hz => hC z (Metric.sphere_subset_closedBall hz)) n

end Reinmann.SplitPairCoefficientIdentity
