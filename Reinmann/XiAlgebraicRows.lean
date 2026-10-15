/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.XiAlgebraicJetSpace

/-!
# Xi row values and the actual differential action in finite jet coordinates

The zeroth convergent Xi row on any finite jet expansion is its finite sum of
Xi derivatives. The coordinate action is transported from the existing
coefficient differentiation operator, not assigned from an assumed zero set.
-/

noncomputable section
open Complex
open scoped ComplexConjugate

namespace Reinmann.XiAlgebraicRows
open FockEigenvectors XiAnnihilator XiAlgebraicJetSpace

theorem higherJet_row_zero_hasSum (s : ℂ) (p j : ℕ) :
    HasSum (derivativeRowTerm j 0 (higherJet s p)) (iteratedDeriv (j + p) xiCompleted s) := by
  induction p generalizing j with
  | zero => simpa using coherent_derivative_row_hasSum j 0 s
  | succ p hp =>
    apply (hasSum_nat_add_iff' 1).mp
    rw [show j + (p + 1) = (j + 1) + p by omega]
    simpa only [Finset.sum_range_one, higherJet_succ, derivative_row_creation_zero,
      sub_zero, derivative_row_creation_shift] using hp (j + 1)

def xiRow : Expansion →ₗ[ℂ] ℂ :=
  Finsupp.linearCombination ℂ (fun a : Label => iteratedDeriv a.2 xiCompleted a.1)

theorem xiRow_single (a : Label) (b : ℂ) :
    xiRow (Finsupp.single a b) = b * iteratedDeriv a.2 xiCompleted a.1 := by
  simp [xiRow, smul_eq_mul]

theorem realization_row_zero_hasSum (c : Expansion) :
    HasSum (rowTerm 0 (realize c)) (xiRow c) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero =>
    simp only [map_zero]
    have hterm : rowTerm 0 0 = fun _ => 0 := by
      ext k
      simp [rowTerm]
    rw [hterm]
    exact hasSum_zero
  | add c d hc hd =>
    convert hc.add hd using 1
    · ext k
      simp [rowTerm, map_add, mul_add]
    · simp
  | single a b =>
    rcases a with ⟨s, p⟩
    have h := (higherJet_row_zero_hasSum s p 0).mul_left b
    convert h using 1
    · ext k
      simp only [realize_single, rowTerm, derivativeRowTerm, xiDerivativeTaylor_zero,
        map_smul, Pi.smul_apply, smul_eq_mul]
      ring
    · simp [xiRow_single]

def constantRow : Expansion →ₗ[ℂ] ℂ where
  toFun c := realize c 0
  map_add' c d := by simp
  map_smul' a c := by simp

theorem constantRow_single (s : ℂ) (p : ℕ) (b : ℂ) :
    constantRow (Finsupp.single ⟨s, p⟩ b) = if p = 0 then b else 0 := by
  cases p with
  | zero => simp [constantRow, realize_single, coherent]
  | succ p =>
    simp [constantRow, realize_single, higherJet_apply_lt s (by omega : 0 < p + 1)]

def derivativeExpansion : Expansion →ₗ[ℂ] Expansion :=
  coordinatesEquiv.symm.toLinearMap.comp (derivativeOnCore.comp coordinatesEquiv.toLinearMap)

theorem realize_derivativeExpansion (c : Expansion) :
    realize (derivativeExpansion c) = derivativeAction (realize c) := by
  change ((coordinatesEquiv (coordinatesEquiv.symm
    (derivativeOnCore (coordinatesEquiv c)))) : Coeff) = _
  rw [coordinatesEquiv.apply_symm_apply]
  rfl

theorem derivativeExpansion_single (s : ℂ) (p : ℕ) (b : ℂ) :
    derivativeExpansion (Finsupp.single ⟨s, p⟩ b) =
      s • Finsupp.single ⟨s, p⟩ b +
        if p = 0 then 0 else (p : ℂ) • Finsupp.single ⟨s, p - 1⟩ b := by
  apply realize_injective
  rw [realize_derivativeExpansion]
  cases p with
  | zero => simp [realize_single, derivative_coherent, smul_smul, mul_comm]
  | succ p =>
    simp only [map_add, map_smul, realize_single, Nat.succ_ne_zero, if_false,
      Nat.add_sub_cancel, derivative_higherJet_succ, Nat.cast_add, Nat.cast_one]
    module

def spectralExpansion : Expansion →ₗ[ℂ] Expansion :=
  (-I) • (derivativeExpansion - (1 / 2 : ℂ) • LinearMap.id)

def coordinates : arithmeticDomain →ₗ[ℂ] Expansion :=
  coordinatesEquiv.symm.toLinearMap.comp arithmeticDomain.subtype

theorem coordinates_spectral (x : arithmeticDomain) :
    coordinates (arithmeticSpectral x) = spectralExpansion (coordinates x) := by
  change coordinatesEquiv.symm ((-I) •
    (derivativeOnCore (x : core) - (1 / 2 : ℂ) • (x : core))) = _
  simp only [map_smul, map_sub, spectralExpansion, LinearMap.smul_apply,
    LinearMap.sub_apply, LinearMap.id_apply, coordinates, LinearMap.comp_apply,
    LinearEquiv.coe_coe, Submodule.subtype_apply, derivativeExpansion,
    coordinatesEquiv.apply_symm_apply]

theorem xiRow_coordinates_zero (x : arithmeticDomain) : xiRow (coordinates x) = 0 := by
  have h := realization_row_zero_hasSum (coordinates x)
  have hre : realize (coordinates x) = ((x : core) : Coeff) := by
    change ((coordinatesEquiv (coordinatesEquiv.symm (x : core))) : Coeff) = _
    rw [coordinatesEquiv.apply_symm_apply]
  rw [hre] at h
  exact h.tsum_eq.symm.trans (x.property 0).2

end Reinmann.XiAlgebraicRows
