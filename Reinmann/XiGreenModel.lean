/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.XiGreenGram
import Reinmann.XiAlgebraicRows
import Reinmann.XiAlgebraicMass

/-!
# A fixed arithmetic Green form on the existing Xi coefficient domain

The universal Gram recurrence is extended by finite sesquilinearity. Its
boundary term is the actual convergent zeroth Xi row, so it vanishes on the
independently defined arithmetic domain. Mass estimates are established for
this same form. No arbitrarily small relative paired budget is asserted.
-/

noncomputable section
open Complex
open scoped ComplexConjugate

namespace Reinmann.XiGreenModel
open XiAlgebraicJetSpace XiAlgebraicRows XiAnnihilator XiDividedDifference
open XiAlgebraicJetForm PacketMass

def expansionMetric : AdditiveScalarForm Expansion := expansionForm XiGreenGram.gram

def boundary (c d : Expansion) : ℂ :=
  xiRow c * conj (constantRow d) - constantRow c * conj (xiRow d)

def actionDefect (c d : Expansion) : ℂ :=
  expansionMetric.η (spectralExpansion c) d - expansionMetric.η c (spectralExpansion d)

theorem metric_basis (s t : ℂ) (p q : ℕ) :
    expansionMetric.η (Finsupp.single ⟨s, p⟩ 1) (Finsupp.single ⟨t, q⟩ 1) =
      XiGreenGram.gram ⟨s, p⟩ ⟨t, q⟩ := pairing_single _ _ _

theorem metric_zero_left (d : Expansion) : expansionMetric.η 0 d = 0 := by
  simp [expansionMetric, expansionForm, pairing]

theorem metric_zero_right (c : Expansion) : expansionMetric.η c 0 = 0 := by
  simp [expansionMetric, expansionForm, pairing]

theorem spectralExpansion_single_basis (s : ℂ) (p : ℕ) :
    spectralExpansion (Finsupp.single ⟨s, p⟩ 1) =
      spectralParam s • Finsupp.single ⟨s, p⟩ 1 +
        if p = 0 then 0 else (-I * (p : ℂ)) • Finsupp.single ⟨s, p - 1⟩ 1 := by
  change (-I) • (derivativeExpansion _ - (1 / 2 : ℂ) • _) = _
  rw [derivativeExpansion_single]
  cases p <;> simp only [Nat.succ_ne_zero, if_true, if_false, add_zero, spectralParam] <;> module

theorem boundary_basis (s t : ℂ) (p q : ℕ) :
    boundary (Finsupp.single ⟨s, p⟩ 1) (Finsupp.single ⟨t, q⟩ 1) =
      (if q = 0 then iteratedDeriv p xiCompleted s else 0) -
        (if p = 0 then conj (iteratedDeriv q xiCompleted t) else 0) := by
  by_cases hp : p = 0 <;> by_cases hq : q = 0 <;>
    simp [boundary, xiRow_single, constantRow_single, hp, hq]

theorem basis_green (s t : ℂ) (p q : ℕ) :
    actionDefect (Finsupp.single ⟨s, p⟩ 1) (Finsupp.single ⟨t, q⟩ 1) =
      boundary (Finsupp.single ⟨s, p⟩ 1) (Finsupp.single ⟨t, q⟩ 1) := by
  have h := XiGreenGram.gram_balance s t p q
  have hg : (-I) * (XiGreenGram.delta s t * XiGreenGram.gram ⟨s, p⟩ ⟨t, q⟩ +
      (if p = 0 then 0 else (p : ℂ) * XiGreenGram.gram ⟨s, p - 1⟩ ⟨t, q⟩) +
      (if q = 0 then 0 else (q : ℂ) * XiGreenGram.gram ⟨s, p⟩ ⟨t, q - 1⟩)) =
        (if q = 0 then iteratedDeriv p xiCompleted s else 0) -
          (if p = 0 then conj (iteratedDeriv q xiCompleted t) else 0) := by
    rw [h, ← mul_assoc]
    simp
  by_cases hp : p = 0 <;> by_cases hq : q = 0 <;>
    simp only [actionDefect, spectralExpansion_single_basis, hp, hq, if_true, if_false,
      add_zero, expansionMetric.add_left, expansionMetric.add_right,
      expansionMetric.smul_left, expansionMetric.smul_right, metric_basis, boundary_basis,
      spectralParam, map_mul, map_neg, map_sub, map_div₀, map_one, map_ofNat,
      map_natCast, Complex.conj_I, XiGreenGram.delta] at hg ⊢ <;>
    linear_combination hg

theorem actionDefect_add_left (c d e : Expansion) :
    actionDefect (c + d) e = actionDefect c e + actionDefect d e := by
  simp only [actionDefect, map_add, expansionMetric.add_left]
  ring

theorem actionDefect_add_right (c d e : Expansion) :
    actionDefect c (d + e) = actionDefect c d + actionDefect c e := by
  simp only [actionDefect, map_add, expansionMetric.add_right]
  ring

theorem actionDefect_smul_left (a : ℂ) (c d : Expansion) :
    actionDefect (a • c) d = a * actionDefect c d := by
  simp only [actionDefect, map_smul, expansionMetric.smul_left]
  ring

theorem actionDefect_smul_right (a : ℂ) (c d : Expansion) :
    actionDefect c (a • d) = conj a * actionDefect c d := by
  simp only [actionDefect, map_smul, expansionMetric.smul_right]
  ring

theorem boundary_add_left (c d e : Expansion) :
    boundary (c + d) e = boundary c e + boundary d e := by
  simp only [boundary, map_add, add_mul]
  ring

theorem boundary_add_right (c d e : Expansion) :
    boundary c (d + e) = boundary c d + boundary c e := by
  simp only [boundary, map_add, mul_add]
  ring

theorem boundary_smul_left (a : ℂ) (c d : Expansion) :
    boundary (a • c) d = a * boundary c d := by
  simp only [boundary, map_smul, smul_eq_mul]
  ring

theorem boundary_smul_right (a : ℂ) (c d : Expansion) :
    boundary c (a • d) = conj a * boundary c d := by
  simp only [boundary, map_smul, smul_eq_mul, map_mul]
  ring

theorem expansion_green_identity (c d : Expansion) : actionDefect c d = boundary c d := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp [actionDefect, boundary, metric_zero_left]
  | add c e hc he => rw [actionDefect_add_left, boundary_add_left, hc, he]
  | single a b =>
    induction d using Finsupp.induction_linear with
    | zero => simp [actionDefect, boundary, metric_zero_right]
    | add d e hd he => rw [actionDefect_add_right, boundary_add_right, hd, he]
    | single a' b' =>
      have hs : Finsupp.single a b = b • Finsupp.single a 1 := by simp
      have ht : Finsupp.single a' b' = b' • Finsupp.single a' 1 := by simp
      rw [hs, ht, actionDefect_smul_left, actionDefect_smul_right,
        boundary_smul_left, boundary_smul_right, basis_green]

def arithmeticMetric : AdditiveScalarForm arithmeticDomain :=
  pullbackForm expansionMetric coordinates

theorem arithmeticMetric_hermitian (x y : arithmeticDomain) :
    conj (arithmeticMetric.η y x) = arithmeticMetric.η x y :=
  pairing_hermitian XiGreenGram.gram_hermitian _ _

theorem arithmeticMetric_symmetric (x y : arithmeticDomain) :
    arithmeticMetric.η (arithmeticSpectral x) y =
      arithmeticMetric.η x (arithmeticSpectral y) := by
  apply sub_eq_zero.mp
  change expansionMetric.η (coordinates (arithmeticSpectral x)) (coordinates y) -
    expansionMetric.η (coordinates x) (coordinates (arithmeticSpectral y)) = 0
  rw [coordinates_spectral, coordinates_spectral]
  change actionDefect (coordinates x) (coordinates y) = 0
  rw [expansion_green_identity, boundary, xiRow_coordinates_zero, xiRow_coordinates_zero]
  simp

theorem arithmeticMetric_jets (s t : ℂ) (p q : ℕ)
    (hs : ∀ j : ℕ, j ≤ p → iteratedDeriv j xiCompleted s = 0)
    (ht : ∀ j : ℕ, j ≤ q → iteratedDeriv j xiCompleted t = 0) :
    arithmeticMetric.η (jetState s p hs) (jetState t q ht) =
      XiGreenGram.gram ⟨s, p⟩ ⟨t, q⟩ := by
  change pairing XiGreenGram.gram (coordinatesEquiv.symm (jetInCore s p))
    (coordinatesEquiv.symm (jetInCore t q)) = _
  rw [coordinates_jet, coordinates_jet, pairing_single]

theorem coherent_partner_pairing (s : ℂ) (hz : xiCompleted s = 0) (p : ℕ)
    (ht : ∀ j : ℕ, j ≤ p → iteratedDeriv j xiCompleted (1 - conj s) = 0) :
    arithmeticMetric.η (coherentState s hz) (jetState (1 - conj s) p ht) = jetCoupling s p := by
  rw [coherentState, arithmeticMetric_jets, XiGreenGram.gram_reflected_partner]

theorem zero_has_nonzero_cross_pairing {s : ℂ} (hz : xiCompleted s = 0) :
    ∃ w : arithmeticDomain, arithmeticMetric.η (coherentState s hz) w ≠ 0 := by
  obtain ⟨m, hm, hvan, hd⟩ := exists_finite_xi_multiplicity hz
  obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  have ht : ∀ j : ℕ, j ≤ p → iteratedDeriv j xiCompleted (1 - conj s) = 0 := by
    intro j hj
    rw [iteratedDeriv_xi_one_sub, iteratedDeriv_xi_conj, hvan j (by omega), map_zero, mul_zero]
  refine ⟨jetState (1 - conj s) p ht, ?_⟩
  rw [coherent_partner_pairing]
  exact jetCoupling_ne_zero s p hd

theorem isotropic_zero_packet_bounds {s : ℂ} (hz : xiCompleted s = 0)
    (hiso : arithmeticMetric.η (coherentState s hz) (coherentState s hz) = 0) :
    ∃ w : arithmeticDomain, arithmeticMetric.η (coherentState s hz) w ≠ 0 ∧
      ∀ h : ℝ, 0 < h → h ≤ 1 / (1 + |(arithmeticMetric.η w w).re|) →
        let v := coherentState s hz
        let q := mass arithmeticMetric v w h
        let ψ := PacketMass.normalize q (mixture arithmeticMetric v w h)
        arithmeticMetric.η ψ ψ = 1 ∧
          h * ‖arithmeticMetric.η v w‖ ^ 2 ≤ q ∧
          q ≤ 3 * h * ‖arithmeticMetric.η v w‖ ^ 2 ∧
          arithmeticSpectral ψ - spectralParam s • ψ =
            ((Real.sqrt q : ℂ)⁻¹ * (h : ℂ) * arithmeticMetric.η v w) •
              (arithmeticSpectral w - spectralParam s • w) := by
  obtain ⟨w, hB⟩ := zero_has_nonzero_cross_pairing hz
  refine ⟨w, hB, ?_⟩
  intro h hh hsmall
  exact ⟨normalized_mixture_mass arithmeticMetric arithmeticMetric_hermitian hiso hB hh hsmall,
    (mass_bounds arithmeticMetric _ w hh hsmall).1,
    (mass_bounds arithmeticMetric _ w hh hsmall).2,
    normalized_residual_identity arithmeticMetric arithmeticSpectral (coherentState_eigen s hz) h⟩

theorem every_xi_zero_has_unit_absolute_mass {s : ℂ} (hz : xiCompleted s = 0) :
    ∃ ψ : arithmeticDomain, ψ ≠ 0 ∧ ‖arithmeticMetric.η ψ ψ‖ = 1 := by
  by_cases hiso : arithmeticMetric.η (coherentState s hz) (coherentState s hz) = 0
  · obtain ⟨w, hB⟩ := zero_has_nonzero_cross_pairing hz
    let h : ℝ := 1 / (1 + |(arithmeticMetric.η w w).re|)
    have hh : 0 < h := by dsimp [h]; positivity
    have hsmall : h ≤ 1 / (1 + |(arithmeticMetric.η w w).re|) := le_rfl
    refine ⟨PacketMass.normalize (mass arithmeticMetric (coherentState s hz) w h)
      (mixture arithmeticMetric (coherentState s hz) w h),
      normalized_mixture_nonzero arithmeticMetric arithmeticMetric_hermitian hiso hB hh hsmall, ?_⟩
    rw [normalized_mixture_mass arithmeticMetric arithmeticMetric_hermitian hiso hB hh hsmall,
      norm_one]
  · let v := coherentState s hz
    have hs : Real.sqrt ‖arithmeticMetric.η v v‖ ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (norm_pos_iff.mpr hiso))
    have hsc : (Real.sqrt ‖arithmeticMetric.η v v‖ : ℂ) ≠ 0 := by exact_mod_cast hs
    have hv : v ≠ 0 := jetState_nonzero s 0 _
    exact ⟨PacketMass.normalize ‖arithmeticMetric.η v v‖ v,
      smul_ne_zero (inv_ne_zero hsc) hv,
      XiAlgebraicMass.absolute_normalized_mass arithmeticMetric v hiso⟩

theorem every_strip_zero_has_unit_absolute_mass {s : ℂ} (hz : riemannZeta s = 0)
    (hpos : 0 < s.re) (hlt : s.re < 1) :
    ∃ ψ : arithmeticDomain, ψ ≠ 0 ∧ ‖arithmeticMetric.η ψ ψ‖ = 1 :=
  every_xi_zero_has_unit_absolute_mass (xi_zero_of_strip_zero hz hpos hlt)

theorem action_defect_zero (x : arithmeticDomain) :
    arithmeticMetric.toScalarHomogeneousForm.defect x (arithmeticSpectral x) = 0 :=
  sub_eq_zero.mpr (arithmeticMetric_symmetric x x)

theorem paired_residual_norm (s : ℂ) (x : arithmeticDomain) :
    ‖arithmeticMetric.toScalarHomogeneousForm.defect x
      (arithmeticSpectral x - spectralParam s • x)‖ =
        2 * |s.re - 1 / 2| * ‖arithmeticMetric.η x x‖ := by
  have he : arithmeticSpectral x = spectralParam s • x +
      (arithmeticSpectral x - spectralParam s • x) := by abel
  have h := arithmeticMetric.skew_mass_eq_defect_sub_residual he
  rw [action_defect_zero, zero_sub] at h
  have hn := congrArg norm h
  rw [norm_mul, norm_spectralParam_sub_conj, norm_neg] at hn
  exact hn.symm

/-- The remaining quantitative requirement, with the action defect already zero. -/
def GreenUnitMassPairedBudget : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 →
    ∀ ε : ℝ, 0 < ε → ∃ x : arithmeticDomain,
      ‖arithmeticMetric.η x x‖ = 1 ∧
        ‖arithmeticMetric.toScalarHomogeneousForm.defect x
          (arithmeticSpectral x - spectralParam s • x)‖ ≤ 2 * ε

theorem riemannHypothesis_of_green_paired_budget (hbudget : GreenUnitMassPairedBudget) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_localForm_approximation id
    (fun x => arithmeticSpectral x) arithmeticMetric
  intro s hz hpos hlt ε hε
  obtain ⟨x, hm, hb⟩ := hbudget s hz hpos hlt ε hε
  refine ⟨x, arithmeticSpectral x - spectralParam s • x, ?_, ?_, ?_⟩
  · dsimp
    abel
  · have hn : ‖arithmeticMetric.η x x‖ ≠ 0 := by rw [hm]; norm_num
    exact norm_ne_zero_iff.mp hn
  · change ‖arithmeticMetric.toScalarHomogeneousForm.defect x (arithmeticSpectral x)‖ +
      ‖arithmeticMetric.toScalarHomogeneousForm.defect x
        (arithmeticSpectral x - spectralParam s • x)‖ ≤ 2 * ε * ‖arithmeticMetric.η x x‖
    rw [action_defect_zero, norm_zero, zero_add, hm, mul_one]
    exact hb

theorem green_paired_budget_of_riemannHypothesis (hRH : RiemannHypothesis) :
    GreenUnitMassPairedBudget := by
  have hstrip := criticalStripObligations_of_riemannHypothesis hRH
  intro s hz hpos hlt ε hε
  obtain ⟨x, _, hm⟩ := every_strip_zero_has_unit_absolute_mass hz hpos hlt
  refine ⟨x, hm, ?_⟩
  have hs : s.re = 1 / 2 := hstrip.strip_zero_on_line s hpos hlt hz
  rw [paired_residual_norm, hs, sub_self, abs_zero, mul_zero, zero_mul]
  positivity

theorem green_paired_budget_iff_riemannHypothesis :
    GreenUnitMassPairedBudget ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_green_paired_budget, green_paired_budget_of_riemannHypothesis⟩

/-- A Fock coefficient-series identity, separate from the Green metric.
It is used to make ordinary packet norm constants explicit. -/
theorem fock_coherent_jet_hasSum (s t : ℂ) (p : ℕ) :
    HasSum (fun n => (n.factorial : ℂ) * FockEigenvectors.coherent s n *
      conj (higherJet t p n)) (s ^ p * Complex.exp (s * conj t)) := by
  apply (hasSum_nat_add_iff' p).mp
  have hz : (∑ k ∈ Finset.range p, (k.factorial : ℂ) *
      FockEigenvectors.coherent s k * conj (higherJet t p k)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [higherJet_apply_lt t (Finset.mem_range.mp hk), map_zero, mul_zero]
  rw [hz, sub_zero]
  convert (FockEigenvectors.coherent_pairing_hasSum s t).mul_left (s ^ p) using 1
  ext k
  rw [higherJet_apply_add]
  simp only [FockEigenvectors.coherent, map_div₀, map_pow, map_natCast, pow_add]
  have hf : ((k + p).factorial : ℂ) ≠ 0 := by exact_mod_cast (k + p).factorial_ne_zero
  have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  field_simp

theorem fock_coherent_jet_pairing (s t : ℂ) (p : ℕ) :
    FockEigenvectors.pairing (FockEigenvectors.coherent s) (higherJet t p) =
      s ^ p * Complex.exp (s * conj t) :=
  (fock_coherent_jet_hasSum s t p).tsum_eq

end Reinmann.XiGreenModel
