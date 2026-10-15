/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.PseudoHermitianPacketMass

/-!
# Unit-mass approximate packets and the paired residual obstruction

The small ordinary residual theorem has no form continuity or symmetry premise.
The paired residual identity shows why, under symmetry, these states still
cannot supply an RH proof from ordinary residual smallness alone.
-/

noncomputable section
open Complex
open scoped ComplexConjugate

namespace Reinmann.PacketMass

theorem scalar_normalization_bound {h b q : ℝ} (hh : 0 < h) (hb : 0 < b)
    (hlower : h * b ^ 2 ≤ q) : h * b / Real.sqrt q ≤ Real.sqrt h := by
  have hq : 0 < q := (mul_pos hh (sq_pos_of_pos hb)).trans_le hlower
  have hprod := mul_le_mul_of_nonneg_left hlower hh.le
  have hp : (Real.sqrt h * Real.sqrt q) ^ 2 = h * q := by
    rw [mul_pow, Real.sq_sqrt hh.le, Real.sq_sqrt hq.le]
  have hs : (h * b) ^ 2 ≤ (Real.sqrt h * Real.sqrt q) ^ 2 := by
    rw [hp]
    nlinarith
  have hbase := (sq_le_sq₀ (by positivity : 0 ≤ h * b)
    (by positivity : 0 ≤ Real.sqrt h * Real.sqrt q)).mp hs
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hq)).mpr
  exact hbase

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem normalization_factor_bound (F : AdditiveScalarForm E) {v w : E}
    (hB : F.η v w ≠ 0) {h : ℝ} (hh : 0 < h)
    (hsmall : h ≤ 1 / (1 + |(F.η w w).re|)) :
    ‖(Real.sqrt (mass F v w h) : ℂ)⁻¹ * (h : ℂ) * F.η v w‖ ≤ Real.sqrt h := by
  have hs := scalar_normalization_bound hh (norm_pos_iff.mpr hB)
    (mass_bounds F v w hh hsmall).1
  calc
    _ = h * ‖F.η v w‖ / Real.sqrt (mass F v w h) := by
      rw [norm_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hh]
      ring
    _ ≤ _ := hs

theorem normalized_residual_norm_le (F : AdditiveScalarForm E)
    (T : E →ₗ[ℂ] E) {v w : E} {μ : ℂ} (heigen : T v = μ • v)
    (hB : F.η v w ≠ 0) {h : ℝ} (hh : 0 < h)
    (hsmall : h ≤ 1 / (1 + |(F.η w w).re|)) :
    ‖T (normalize (mass F v w h) (mixture F v w h)) -
      μ • normalize (mass F v w h) (mixture F v w h)‖ ≤
        Real.sqrt h * ‖T w - μ • w‖ := by
  rw [normalized_residual_identity F T heigen h, norm_smul]
  exact mul_le_mul_of_nonneg_right (normalization_factor_bound F hB hh hsmall) (norm_nonneg _)

theorem exists_unit_mass_small_residual (F : AdditiveScalarForm E)
    (hHerm : ∀ x y, conj (F.η y x) = F.η x y)
    (T : E →ₗ[ℂ] E) {v w : E} {μ : ℂ} (heigen : T v = μ • v)
    (hv : F.η v v = 0) (hB : F.η v w ≠ 0) {τ : ℝ} (hτ : 0 < τ) :
    ∃ x : E, x ≠ 0 ∧ F.η x x = 1 ∧ ‖T x - μ • x‖ < τ := by
  let M := ‖T w - μ • w‖
  have hM : 0 ≤ M := norm_nonneg _
  have hden : 0 < M + 1 := by positivity
  have hlimit : 0 < min (1 / (1 + |(F.η w w).re|)) ((τ / (M + 1)) ^ 2) := by
    apply lt_min <;> positivity
  obtain ⟨h, hh, hlt⟩ := exists_between hlimit
  have hsmall : h ≤ 1 / (1 + |(F.η w w).re|) :=
    hlt.le.trans (min_le_left _ _)
  have hstep : h < (τ / (M + 1)) ^ 2 := hlt.trans_le (min_le_right _ _)
  have hroot : Real.sqrt h < τ / (M + 1) := by
    apply (sq_lt_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt hh.le]
    exact hstep
  have hproduct : Real.sqrt h * (M + 1) < τ := (lt_div_iff₀ hden).mp hroot
  refine ⟨normalize (mass F v w h) (mixture F v w h),
    normalized_mixture_nonzero F hHerm hv hB hh hsmall,
    normalized_mixture_mass F hHerm hv hB hh hsmall, ?_⟩
  have hr := normalized_residual_norm_le F T heigen hB hh hsmall
  change ‖T _ - μ • _‖ ≤ Real.sqrt h * M at hr
  have hsqrt : 0 < Real.sqrt h := Real.sqrt_pos.mpr hh
  nlinarith

/-- Unit mass and global form symmetry force a fixed paired residual defect,
regardless of how small the ordinary residual norm is. -/
theorem paired_residual_norm_of_unit_mass (F : AdditiveScalarForm E)
    (T : E →ₗ[ℂ] E) (x : E) (s : ℂ) (hmass : ‖F.η x x‖ = 1)
    (hsym : F.η (T x) x = F.η x (T x)) :
    ‖F.toScalarHomogeneousForm.defect x (T x - spectralParam s • x)‖ =
      2 * |s.re - 1 / 2| := by
  have heig : T x = spectralParam s • x + (T x - spectralParam s • x) := by abel
  have hid := F.skew_mass_eq_defect_sub_residual heig
  have hd : F.toScalarHomogeneousForm.defect x (T x) = 0 := sub_eq_zero.mpr hsym
  rw [hd, zero_sub] at hid
  have hn := congrArg norm hid
  rw [norm_mul, norm_spectralParam_sub_conj, hmass, mul_one, norm_neg] at hn
  exact hn.symm

/-- A bounded form controls the paired residual by the product of state and
residual norms, rather than by the residual norm alone. -/
theorem paired_residual_norm_le_norm_product (F : AdditiveScalarForm E) {K : ℝ}
    (hbound : ∀ x y : E, ‖F.η x y‖ ≤ K * ‖x‖ * ‖y‖) (x r : E) :
    ‖F.toScalarHomogeneousForm.defect x r‖ ≤ 2 * K * ‖x‖ * ‖r‖ := by
  calc
    _ ≤ ‖F.η r x‖ + ‖F.η x r‖ := norm_sub_le _ _
    _ ≤ K * ‖r‖ * ‖x‖ + K * ‖x‖ * ‖r‖ := add_le_add (hbound r x) (hbound x r)
    _ = _ := by ring

theorem distance_le_norm_product (F : AdditiveScalarForm E) {K : ℝ}
    (hbound : ∀ x y : E, ‖F.η x y‖ ≤ K * ‖x‖ * ‖y‖)
    (T : E →ₗ[ℂ] E) (x : E) (s : ℂ) (hmass : ‖F.η x x‖ = 1)
    (hsym : F.η (T x) x = F.η x (T x)) :
    |s.re - 1 / 2| ≤ K * ‖x‖ * ‖T x - spectralParam s • x‖ := by
  have h := paired_residual_norm_le_norm_product F hbound x
    (T x - spectralParam s • x)
  rw [paired_residual_norm_of_unit_mass F T x s hmass hsym] at h
  linarith

/-- An analytic sufficient condition for the local reduction. The missing
arithmetic estimate is on this product at unit absolute form mass. -/
theorem critical_of_arbitrarily_small_norm_product (F : AdditiveScalarForm E) {K : ℝ}
    (hbound : ∀ x y : E, ‖F.η x y‖ ≤ K * ‖x‖ * ‖y‖)
    (T : E →ₗ[ℂ] E) (s : ℂ)
    (hpackets : ∀ ε : ℝ, 0 < ε → ∃ x : E, ‖F.η x x‖ = 1 ∧
      F.η (T x) x = F.η x (T x) ∧
      K * ‖x‖ * ‖T x - spectralParam s • x‖ ≤ ε) : s.re = 1 / 2 := by
  by_contra hoff
  have hd : 0 < |s.re - 1 / 2| := abs_pos.mpr (sub_ne_zero.mpr hoff)
  obtain ⟨x, hm, hs, he⟩ := hpackets (|s.re - 1 / 2| / 2) (by positivity)
  have hl := distance_le_norm_product F hbound T x s hm hs
  linarith

end Reinmann.PacketMass
