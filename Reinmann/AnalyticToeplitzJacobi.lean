/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.AnalyticSplitPair
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-! Jacobi's identity for the actual ordinary Taylor series of analytic functions. -/
noncomputable section
namespace Reinmann.AnalyticToeplitzJacobi
open Finset Filter
open scoped Topology

def taylorSeries (F : ℂ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (SplitPairCauchyTail.coefficient F)

/-- Factorial normalization turns Leibniz's rule into ordinary convolution. -/
theorem coefficient_mul {F G : ℂ → ℂ} (hF : AnalyticAt ℂ F 0)
    (hG : AnalyticAt ℂ G 0) (n : ℕ) :
    SplitPairCauchyTail.coefficient (fun z => F z*G z) n =
      ∑ i ∈ range (n+1), SplitPairCauchyTail.coefficient F i *
        SplitPairCauchyTail.coefficient G (n-i) := by
  unfold SplitPairCauchyTail.coefficient
  rw [iteratedDeriv_fun_mul hF.contDiffAt hG.contDiffAt, sum_div]
  apply sum_congr rfl
  intro i hi
  have hle : i ≤ n := Nat.le_of_lt_succ (mem_range.mp hi)
  have hfac : (n.choose i : ℂ)*(i.factorial : ℂ)*((n-i).factorial : ℂ) = (n.factorial : ℂ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hle
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hi' : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  have hni : ((n-i).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n-i)
  field_simp [hn,hi',hni]
  linear_combination (iteratedDeriv i F 0)*(iteratedDeriv (n-i) G 0)*hfac

/-- The actual Taylor-series construction respects analytic multiplication. -/
theorem taylorSeries_mul {F G : ℂ → ℂ} (hF : AnalyticAt ℂ F 0)
    (hG : AnalyticAt ℂ G 0) :
    taylorSeries (fun z => F z*G z) = taylorSeries F*taylorSeries G := by
  ext n
  rw [PowerSeries.coeff_mul]
  simp only [taylorSeries,PowerSeries.coeff_mk]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  exact coefficient_mul hF hG n

/-- The reciprocal convolution is derived from function equality near zero. -/
theorem taylorSeries_reciprocal {F : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) (h0 : F 0 ≠ 0) :
    taylorSeries F*taylorSeries (fun z => (F z)⁻¹) = 1 := by
  have hm := taylorSeries_mul (F := F) (G := fun z => (F z)⁻¹) hF (hF.inv h0)
  rw [← hm]
  have heq : (fun z => F z*(F z)⁻¹) =ᶠ[𝓝 0] (fun _ => (1 : ℂ)) := by
    have hn : ∀ᶠ z in 𝓝 (0 : ℂ), F z ≠ 0 :=
      hF.continuousAt.eventually_ne h0
    filter_upwards [hn] with z hz
    exact mul_inv_cancel₀ hz
  ext n
  simp only [taylorSeries,PowerSeries.coeff_mk,SplitPairCauchyTail.coefficient]
  rw [heq.iteratedDeriv_eq n,iteratedDeriv_const,PowerSeries.coeff_one]
  cases n with
  | zero => simp
  | succ n => simp

/-- Sign-free complementary identity for actual Taylor coefficients, with the
explicit z -> -z convention and the original rank r=n+s-1. -/
theorem reciprocalMinor_eq_original {F : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) (h0 : F 0 = 1)
    (s n : ℕ) :
    AnalyticSplitPair.reciprocalMinor F s n =
      ToeplitzComplement.minor (PowerSeries.rescale (-1) (taylorSeries F)) (n+(s-1)) s := by
  have hfg := taylorSeries_reciprocal hF (by rw [h0]; norm_num)
  have hres : PowerSeries.rescale (-1 : ℂ) (PowerSeries.rescale (-1) (taylorSeries F)) =
      taylorSeries F := by
    ext k
    simp only [PowerSeries.coeff_rescale,← mul_assoc]
    rw [← pow_add,← two_mul,pow_mul]
    simp
  have hf0 : PowerSeries.coeff 0 (PowerSeries.rescale (-1) (taylorSeries F)) = 1 := by
    simp [taylorSeries,SplitPairCauchyTail.coefficient,h0]
  have hj := ToeplitzComplement.complementary_minor_signed
    (f := PowerSeries.rescale (-1) (taylorSeries F)) (g := taylorSeries (fun z => (F z)⁻¹))
    (by rw [hres]; exact hfg) hf0 s (n+(s-1))
  rw [← hj]
  unfold AnalyticSplitPair.reciprocalMinor ToeplitzComplement.minor
  congr 1
  funext i j
  have hidx : n+i.val+(s-1-j.val) = n+(s-1)+i.val-j.val := by have hj := j.isLt; omega
  simp only [ToeplitzComplement.entry,taylorSeries,PowerSeries.coeff_mk,
    if_pos (show j.val ≤ n+(s-1)+i.val by have hj := j.isLt; omega),hidx]

/-- Both signs transfer to the actual original Taylor-series minors, with the
explicit rescaling convention. This is a standalone analytic theorem. -/
theorem entire_original_both_signs {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : ℂ → ℂ} (hF : Differentiable ℂ F) (hF0 : F 0 = 1)
    (hFconj : ∀ z, F (star z) = star (F z)) (a : ι → ℂ)
    (ha : Function.Injective a) (hzero : ∀ i, F (a i) = 0)
    (hsimple : ∀ i, deriv F (a i) ≠ 0) (σ : ι ≃ ι)
    (hconj : ∀ i, a (σ i) = star (a i)) {R : ℝ} (hR : 0 < R)
    (hall : ∀ z ∈ Metric.closedBall 0 R, F z = 0 → ∃ i, z = a i)
    (s : ℕ) (S : Finset ι) (hS : S.card = s) (p q : ι) (hp : p ∈ S) (hq : q ∉ S)
    (hσp : σ p = q) (hswap : S.image σ = insert q (S.erase p))
    (hangle : (∏ i ∈ S, (a i)⁻¹).im ≠ 0) (hpR : ‖a p‖ < R)
    (hmax : ∀ x ∈ S, ∀ y ∉ S, ‖(a y)⁻¹‖ ≤ ‖(a x)⁻¹‖)
    (hequal : ∀ x ∈ S, ∀ y ∉ S, ‖(a y)⁻¹‖ = ‖(a x)⁻¹‖ → x = p ∧ y = q) :
    let f := PowerSeries.rescale (-1) (taylorSeries F)
    (∀ M, ∃ r ≥ M, (ToeplitzComplement.minor f r s).re < 0) ∧
    (∀ M, ∃ r ≥ M, 0 < (ToeplitzComplement.minor f r s).re) := by
  have h0 : F 0 ≠ 0 := by rw [hF0]; norm_num
  have h := AnalyticSplitPair.entire_split_pair_of_boundary hF h0 hFconj a ha hzero hsimple
    σ hconj hR hall s S hS p q hp hq hσp hswap hangle hpR hmax hequal
  constructor
  · intro M
    obtain ⟨n,hn,hsign⟩ := h.1 M
    refine ⟨n+(s-1),by omega,?_⟩
    rwa [← reciprocalMinor_eq_original (hF.analyticAt 0) hF0]
  · intro M
    obtain ⟨n,hn,hsign⟩ := h.2 M
    refine ⟨n+(s-1),by omega,?_⟩
    rwa [← reciprocalMinor_eq_original (hF.analyticAt 0) hF0]

end Reinmann.AnalyticToeplitzJacobi
