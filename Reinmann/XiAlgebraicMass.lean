/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.XiAlgebraicJetForm

/-!
# Actual arithmetic packet masses for one fixed algebraic form

Every Xi zero has a nonzero cross partner in the independently defined
arithmetic domain. The same fixed Hermitian form supplies explicit positive
packet mass bounds in the isotropic case and absolute unit mass at every
zero. The exact residual formula is checked without introducing a norm on
the algebraic state space. Operator-form symmetry and the paired RH budget
are not inferred from these mass estimates.
-/

noncomputable section
open Complex
open scoped ComplexConjugate

namespace Reinmann.XiAlgebraicMass
open XiAlgebraicJetSpace XiAlgebraicJetForm XiAnnihilator PacketMass

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem absolute_normalized_mass (F : AdditiveScalarForm V) (v : V)
    (hm : F.η v v ≠ 0) :
    ‖F.η (normalize ‖F.η v v‖ v) (normalize ‖F.η v v‖ v)‖ = 1 := by
  have hq : 0 < ‖F.η v v‖ := norm_pos_iff.mpr hm
  have hs : Real.sqrt ‖F.η v v‖ ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hq)
  rw [PacketMass.normalize, F.smul_left, F.smul_right]
  simp only [norm_mul, norm_conj, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  have hsq := Real.sq_sqrt hq.le
  field_simp
  nlinarith

theorem isotropic_zero_has_packet_mass_bounds {s : ℂ} (hz : xiCompleted s = 0)
    (hiso : arithmeticForm.η (coherentState s hz) (coherentState s hz) = 0) :
    ∃ w : arithmeticDomain, arithmeticForm.η (coherentState s hz) w ≠ 0 ∧
      ∀ h : ℝ, 0 < h → h ≤ 1 / (1 + |(arithmeticForm.η w w).re|) →
        let v := coherentState s hz
        let q := mass arithmeticForm v w h
        let ψ := normalize q (mixture arithmeticForm v w h)
        arithmeticForm.η ψ ψ = 1 ∧
          h * ‖arithmeticForm.η v w‖ ^ 2 ≤ q ∧
          q ≤ 3 * h * ‖arithmeticForm.η v w‖ ^ 2 ∧
          arithmeticSpectral ψ - spectralParam s • ψ =
            ((Real.sqrt q : ℂ)⁻¹ * (h : ℂ) * arithmeticForm.η v w) •
              (arithmeticSpectral w - spectralParam s • w) := by
  obtain ⟨w, hB⟩ := zero_has_nonzero_arithmetic_cross_pairing hz
  refine ⟨w, hB, ?_⟩
  intro h hh hsmall
  exact ⟨normalized_mixture_mass arithmeticForm arithmeticForm_hermitian hiso hB hh hsmall,
    (mass_bounds arithmeticForm _ w hh hsmall).1,
    (mass_bounds arithmeticForm _ w hh hsmall).2,
    normalized_residual_identity arithmeticForm arithmeticSpectral (coherentState_eigen s hz) h⟩

theorem every_xi_zero_has_unit_absolute_mass {s : ℂ} (hz : xiCompleted s = 0) :
    ∃ ψ : arithmeticDomain, ψ ≠ 0 ∧ ‖arithmeticForm.η ψ ψ‖ = 1 := by
  by_cases hiso : arithmeticForm.η (coherentState s hz) (coherentState s hz) = 0
  · obtain ⟨w, hB⟩ := zero_has_nonzero_arithmetic_cross_pairing hz
    let h : ℝ := 1 / (1 + |(arithmeticForm.η w w).re|)
    have hh : 0 < h := by dsimp [h]; positivity
    have hsmall : h ≤ 1 / (1 + |(arithmeticForm.η w w).re|) := le_rfl
    refine ⟨normalize (mass arithmeticForm (coherentState s hz) w h)
      (mixture arithmeticForm (coherentState s hz) w h),
      normalized_mixture_nonzero arithmeticForm arithmeticForm_hermitian hiso hB hh hsmall, ?_⟩
    rw [normalized_mixture_mass arithmeticForm arithmeticForm_hermitian hiso hB hh hsmall,
      norm_one]
  · let v := coherentState s hz
    have hs : Real.sqrt ‖arithmeticForm.η v v‖ ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (norm_pos_iff.mpr hiso))
    have hsc : (Real.sqrt ‖arithmeticForm.η v v‖ : ℂ) ≠ 0 := by exact_mod_cast hs
    have hv : v ≠ 0 := jetState_nonzero s 0 _
    exact ⟨normalize ‖arithmeticForm.η v v‖ v,
      smul_ne_zero (inv_ne_zero hsc) hv, absolute_normalized_mass arithmeticForm v hiso⟩

theorem every_strip_zero_has_unit_absolute_mass {s : ℂ} (hz : riemannZeta s = 0)
    (hpos : 0 < s.re) (hlt : s.re < 1) :
    ∃ ψ : arithmeticDomain, ψ ≠ 0 ∧ ‖arithmeticForm.η ψ ψ‖ = 1 :=
  every_xi_zero_has_unit_absolute_mass (xi_zero_of_strip_zero hz hpos hlt)

/-- The remaining condition for this fixed model; no instance of it is asserted. -/
def ArithmeticUnitMassPairedBudget : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 →
    ∀ ε : ℝ, 0 < ε → ∃ ψ : arithmeticDomain,
      ‖arithmeticForm.η ψ ψ‖ = 1 ∧
      ‖arithmeticForm.toScalarHomogeneousForm.defect ψ (arithmeticSpectral ψ)‖ +
        ‖arithmeticForm.toScalarHomogeneousForm.defect ψ
          (arithmeticSpectral ψ - spectralParam s • ψ)‖ ≤ 2 * ε

theorem riemannHypothesis_of_arithmetic_unit_mass_paired_budget
    (hbudget : ArithmeticUnitMassPairedBudget) : RiemannHypothesis := by
  apply riemannHypothesis_of_localForm_approximation id
    (fun ψ => arithmeticSpectral ψ) arithmeticForm
  intro s hz hpos hlt ε hε
  obtain ⟨ψ, hm, hb⟩ := hbudget s hz hpos hlt ε hε
  refine ⟨ψ, arithmeticSpectral ψ - spectralParam s • ψ, ?_, ?_, ?_⟩
  · dsimp
    abel
  · have hn : ‖arithmeticForm.η ψ ψ‖ ≠ 0 := by rw [hm]; norm_num
    exact norm_ne_zero_iff.mp hn
  · simpa [hm] using hb

end Reinmann.XiAlgebraicMass
