/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Actual reciprocal coefficients of a finite product, with nonzero residues. -/
noncomputable section
namespace Reinmann.SplitPairCoefficients
open Finset Polynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def residue (a : ι → ℂ) (i : ι) : ℂ :=
  ∏ j ∈ univ.erase i, (a i - a j)⁻¹ * (-a j)

def factor (a : ℂ) : ℂ[X] := 1 - C a⁻¹ * X

def product (a : ι → ℂ) : ℂ[X] := ∏ i, factor (a i)

def geometric (z : ℂ) : PowerSeries ℂ := PowerSeries.mk fun n => z ^ n

/-- Every simple nonzero pole has a nonzero residue coefficient. -/
theorem residue_ne_zero {a : ι → ℂ} (ha : Function.Injective a) (hz : ∀ i, a i ≠ 0)
    (i : ι) : residue a i ≠ 0 := by
  unfold residue
  apply prod_ne_zero_iff.mpr
  intro j hj
  exact mul_ne_zero (inv_ne_zero (sub_ne_zero.mpr (ha.ne (mem_erase.mp hj).1.symm)))
    (neg_ne_zero.mpr (hz j))

theorem basisDivisor_factor {x y : ℂ} (hy : y ≠ 0) :
    Lagrange.basisDivisor x y = C ((x-y)⁻¹ * (-y)) * factor y := by
  simp only [Lagrange.basisDivisor, factor, mul_sub, mul_one, ← C_mul]
  simp only [← mul_assoc, ← C_mul, C_neg, mul_neg, neg_mul]
  ring_nf
  rw [show y * (x-y)⁻¹ * y⁻¹ = (x-y)⁻¹ by
    calc
      _ = (y * y⁻¹) * (x-y)⁻¹ := by ring
      _ = _ := by rw [mul_inv_cancel₀ hy, one_mul]]
  ring

/-- Polynomial partial fractions obtained from Lagrange interpolation of 1. -/
theorem polynomial_residue_identity [Nonempty ι] {a : ι → ℂ}
    (ha : Function.Injective a) (hz : ∀ i, a i ≠ 0) :
    ∑ i, C (residue a i) * ∏ j ∈ univ.erase i, factor (a j) = 1 := by
  have h := Lagrange.sum_basis (s := (univ : Finset ι)) ha.injOn univ_nonempty
  have hb (i : ι) : Lagrange.basis univ a i =
      C (residue a i) * ∏ j ∈ univ.erase i, factor (a j) := by
    unfold Lagrange.basis residue
    simp_rw [basisDivisor_factor (hz _)]
    rw [prod_mul_distrib, ← map_prod]
  simpa only [hb] using h

theorem factor_mul_geometric (a : ℂ) :
    (factor a : PowerSeries ℂ) * geometric a⁻¹ = 1 := by
  simp only [factor, Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_mul,
    Polynomial.coe_C, Polynomial.coe_X, sub_mul, one_mul]
  ext n
  cases n with
  | zero => simp [geometric]
  | succ n =>
    simp only [map_sub, mul_assoc, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_succ_X_mul, geometric, PowerSeries.coeff_mk,
      PowerSeries.coeff_one, Nat.succ_ne_zero, if_false, sub_eq_zero]
    rw [pow_succ, mul_comm]

/-- The reciprocal power series is the actual inverse of the finite product. -/
theorem inverse_eq_residue_sum [Nonempty ι] {a : ι → ℂ}
    (ha : Function.Injective a) (hz : ∀ i, a i ≠ 0) :
    ((product a : PowerSeries ℂ))⁻¹ =
      ∑ i, PowerSeries.C (residue a i) * geometric (a i)⁻¹ := by
  have hc : PowerSeries.constantCoeff (product a : PowerSeries ℂ) ≠ 0 := by
    change (product a).coeff 0 ≠ 0
    rw [Polynomial.coeff_zero_eq_eval_zero]
    simp [product, factor, Polynomial.eval_prod]
  apply (PowerSeries.inv_eq_iff_mul_eq_one hc).mpr
  rw [sum_mul]
  calc
    (∑ i, PowerSeries.C (residue a i) * geometric (a i)⁻¹ * (product a : PowerSeries ℂ)) =
        ∑ i, ((C (residue a i) * ∏ j ∈ univ.erase i, factor (a j) : ℂ[X]) : PowerSeries ℂ) := by
      apply sum_congr rfl
      intro i _
      have hp : product a = factor (a i) * ∏ j ∈ univ.erase i, factor (a j) := by
        exact (mul_prod_erase _ _ (mem_univ i)).symm
      rw [hp, Polynomial.coe_mul]
      rw [show PowerSeries.C (residue a i) * geometric (a i)⁻¹ *
          ((factor (a i) : PowerSeries ℂ) * ↑(∏ j ∈ univ.erase i, factor (a j))) =
          PowerSeries.C (residue a i) *
          ((factor (a i) : PowerSeries ℂ) * geometric (a i)⁻¹) *
          ↑(∏ j ∈ univ.erase i, factor (a j)) by ring]
      rw [factor_mul_geometric, mul_one]
      simp
    _ = 1 := by
      have h := congrArg (Polynomial.coeToPowerSeries.ringHom : ℂ[X] → PowerSeries ℂ)
        (polynomial_residue_identity ha hz)
      simpa using h

/-- Exact coefficients, rather than an assumed two-term asymptotic. -/
theorem reciprocal_coefficient [Nonempty ι] {a : ι → ℂ}
    (ha : Function.Injective a) (hz : ∀ i, a i ≠ 0) (n : ℕ) :
    PowerSeries.coeff n ((product a : PowerSeries ℂ))⁻¹ =
      ∑ i, residue a i * (a i)⁻¹ ^ n := by
  rw [inverse_eq_residue_sum ha hz, map_sum]
  simp [PowerSeries.coeff_C_mul, geometric]

/-- Residues inherit the conjugation permutation of the actual finite roots. -/
theorem residue_conjugate {a : ι → ℂ} (σ : ι ≃ ι)
    (ha : ∀ i, a (σ i) = star (a i)) (i : ι) :
    residue a (σ i) = star (residue a i) := by
  classical
  have hp : residue a (σ i) =
      ∏ j ∈ univ.erase i, (a (σ i)-a (σ j))⁻¹ * (-a (σ j)) := by
    unfold residue
    symm
    apply prod_bij (fun j _ => σ j)
    · intro j hj
      exact mem_erase.mpr ⟨σ.injective.ne (mem_erase.mp hj).1, mem_univ _⟩
    · intro j _ k _ h
      exact σ.injective h
    · intro j hj
      refine ⟨σ.symm j, mem_erase.mpr ⟨?_, mem_univ _⟩, by simp⟩
      intro h
      apply (mem_erase.mp hj).1
      simpa using congrArg σ h
    · intro j _
      rfl
  rw [hp]
  change _ = (starRingEnd ℂ) (residue a i)
  simp [residue, ha, map_prod, map_mul, map_sub, map_inv₀, map_neg]

end Reinmann.SplitPairCoefficients
