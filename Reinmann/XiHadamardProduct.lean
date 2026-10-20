/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.XiCanonicalProductSector
import Reinmann.PNTPlus.Mathlib.NumberTheory.LSeries.RiemannZetaHadamard

/-! Actual folded-Xi genus-zero factorization, using the attributed PNT+
Hadamard backport. The order bound is strictly below one; all zero indices
retain their analytic multiplicities. -/
noncomputable section
namespace Reinmann.XiHadamardProduct
open Complex Complex.Hadamard XiCanonicalProductSector

/-- The imported classical entire Xi has exactly our normalization. -/
theorem riemannXi_eq_xiCompleted : Complex.riemannXi = xiCompleted := by
  funext s
  unfold Complex.riemannXi xiCompleted
  ring

/-- An order-one Xi bound becomes a fixed order-3/4 bound after folding. -/
theorem foldedXi_order : EntireOfOrderAtMost (3 / 4 : ℝ) foldedXi := by
  have hxi : EntireOfOrderAtMost (1 : ℝ) xiCompleted := by
    rw [← riemannXi_eq_xiCompleted]
    exact riemannXi_entireOfOrderAtMost_one
  obtain ⟨C, hC, hbound⟩ := hxi.exists_bound (by norm_num : (0 : ℝ) < 1 / 2)
  apply EntireOfOrderAtMost.of_norm_le_exp differentiable_foldedXi
  refine ⟨C * (5 / 2 : ℝ) ^ (3 / 2 : ℝ), by positivity, ?_⟩
  intro z
  let R : ℝ := 1 + ‖z‖
  have hR : 1 ≤ R := by dsimp [R]; linarith [norm_nonneg z]
  have hRp : 0 ≤ R := le_trans zero_le_one hR
  have hnorm : ‖Complex.sqrt z‖ ^ 2 = ‖z‖ := by
    rw [← norm_pow, complex_sqrt_sq]
  have hsqrt : ‖Complex.sqrt z‖ ≤ Real.sqrt R := by
    apply (Real.le_sqrt (norm_nonneg _) hRp).2
    rw [hnorm]
    dsimp [R]
    linarith
  have hsqrt1 : 1 ≤ Real.sqrt R := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hR
  have hbase : 1 + ‖1 / 2 + Complex.sqrt z‖ ≤ (5 / 2 : ℝ) * Real.sqrt R := by
    have hn := norm_add_le (1 / 2 : ℂ) (Complex.sqrt z)
    norm_num at hn
    linarith
  have hpow : (1 + ‖1 / 2 + Complex.sqrt z‖) ^ (3 / 2 : ℝ) ≤
      (5 / 2 : ℝ) ^ (3 / 2 : ℝ) * R ^ (3 / 4 : ℝ) := by
    calc
      _ ≤ ((5 / 2 : ℝ) * Real.sqrt R) ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hbase (by norm_num)
      _ = _ := by
        rw [Real.mul_rpow (by norm_num) (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
          ← Real.rpow_mul hRp]
        norm_num
  rw [foldedXi_eq_sqrt]
  apply (hbound (1 / 2 + Complex.sqrt z)).trans
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left hpow hC.le
  simpa only [show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num, mul_assoc] using h

/-- The divisor's natural multiplicity equals the analytic natural order. -/
theorem divisor_multiplicity (z : ℂ) :
    Int.toNat (MeromorphicOn.divisor foldedXi Set.univ z) =
      analyticOrderNatAt foldedXi z := by
  have han : AnalyticOnNhd ℂ foldedXi Set.univ :=
    fun w _ => differentiable_foldedXi.analyticAt w
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply han (Set.mem_univ z)]
  rw [← Nat.cast_analyticOrderNatAt
    (CanonicalZeroIndex.order_ne_top differentiable_foldedXi foldedXi_zero_ne z)]
  simp

/-- The repository's index is equivalent to the Hadamard divisor index. -/
def zeroIndexEquiv : Index ≃ divisorZeroIndex₀ foldedXi Set.univ where
  toFun i := ⟨⟨value i, ⟨i.val.2, by rw [divisor_multiplicity]; exact i.property⟩⟩,
    value_ne_zero i⟩
  invFun p := ⟨(p.val.1, p.val.2.val), by
    rw [← divisor_multiplicity]
    exact p.val.2.isLt⟩
  left_inv i := by rfl
  right_inv p := by
    rcases p with ⟨⟨z, k⟩, hz⟩
    rfl

/-- Inverse-zero summability is derived from growth, not assumed. -/
theorem summable_inverse_zeros : Summable (fun i : Index => ‖(value i)⁻¹‖) := by
  have hs := foldedXi_order.summable_norm_inv_pow_divisorZeroIndex₀
    (by norm_num : (0 : ℝ) ≤ 3 / 4) ⟨0, foldedXi_zero_ne⟩
  have hfloor : Nat.floor (3 / 4 : ℝ) = 0 := Nat.floor_eq_zero.mpr (by norm_num)
  simp only [hfloor, Nat.zero_add, pow_one] at hs
  have he := hs.comp_injective zeroIndexEquiv.injective
  simpa only [norm_inv] using he

/-- The actual normalized genus-zero product, over all zeros with multiplicities. -/
theorem foldedXi_product (z : ℂ) :
    foldedXi z = (XiMomentCoeff 0 : ℂ) * ∏' i : Index, (1 - (value i)⁻¹ * z) := by
  obtain ⟨P, hdeg, hfac⟩ := hadamard_factorization_of_order_reindex
    (by norm_num : (0 : ℝ) ≤ 3 / 4) ⟨0, foldedXi_zero_ne⟩ foldedXi_order zeroIndexEquiv
  have hfloor : Nat.floor (3 / 4 : ℝ) = 0 := Nat.floor_eq_zero.mpr (by norm_num)
  simp only [hfloor, Nat.cast_zero] at hdeg hfac
  have hP := Polynomial.eq_C_of_degree_le_zero hdeg
  have ho : analyticOrderNatAt foldedXi 0 = 0 := by
    unfold analyticOrderNatAt
    rw [(differentiable_foldedXi.analyticAt 0).analyticOrderAt_eq_zero.mpr foldedXi_zero_ne]
    rfl
  have hf (w : ℂ) : foldedXi w = Complex.exp (P.coeff 0) *
      ∏' i : Index, (1 - (value i)⁻¹ * w) := by
    have h := hfac w
    change foldedXi w = Complex.exp (Polynomial.eval w P) *
      w ^ analyticOrderNatAt foldedXi 0 *
      (∏' i : Index, weierstrassFactor 0 (w / value i)) at h
    rw [hP] at h
    simpa only [Polynomial.eval_C, ho, pow_zero, mul_one, weierstrassFactor_zero,
      div_eq_mul_inv, mul_comm w] using h
  have hconstant : Complex.exp (P.coeff 0) = (XiMomentCoeff 0 : ℂ) := by
    have hc : foldedXi 0 = (XiMomentCoeff 0 : ℂ) := by simpa using foldedXi_taylor 0
    have he : Complex.exp (P.coeff 0) = foldedXi 0 := by simpa using (hf 0).symm
    exact he.trans hc
  rw [hf, hconstant]

/-- The classical sector bridge is now derived for every positive fixed rank. -/
theorem katkovaSectorBridge (m : ℕ) (hm : 0 < m) : KatkovaSectorBridge m :=
  katkovaSectorBridge_of_canonical_product summable_inverse_zeros foldedXi_product hm

end Reinmann.XiHadamardProduct
