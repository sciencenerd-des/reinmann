/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.PseudoHermitianLocal
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Explicit packet mass lower bounds and normalization

For an isotropic state v with a nonzero cross pairing B=η(v,w), the
unnormalized mixture v+hBw has mass |B|²(2h+h²C), C=η(w,w) real.
The mass is bounded below by h|B|² for a positive, explicit range of h.
This lemma does not supply the arithmetic nonzero cross pairing or the
paired residual estimate. Those obligations must concern the same form.
-/

noncomputable section
open Complex
open scoped ComplexConjugate

namespace Reinmann.PacketMass

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

def mixture (F : AdditiveScalarForm E) (v w : E) (h : ℝ) : E :=
  v + ((h : ℂ) * F.η v w) • w

def mass (F : AdditiveScalarForm E) (v w : E) (h : ℝ) : ℝ :=
  ‖F.η v w‖ ^ 2 * (2 * h + h ^ 2 * (F.η w w).re)

def normalize (q : ℝ) (x : E) : E := (Real.sqrt q : ℂ)⁻¹ • x

theorem self_eq_real (F : AdditiveScalarForm E)
    (hHerm : ∀ x y, conj (F.η y x) = F.η x y) (w : E) :
    F.η w w = ((F.η w w).re : ℂ) := by
  have him := Complex.conj_eq_iff_im.mp (hHerm w w)
  apply Complex.ext
  · simp
  · simpa using him

theorem mixture_mass (F : AdditiveScalarForm E)
    (hHerm : ∀ x y, conj (F.η y x) = F.η x y)
    {v w : E} (hv : F.η v v = 0) (h : ℝ) :
    F.η (mixture F v w h) (mixture F v w h) = (mass F v w h : ℂ) := by
  have hwv : F.η w v = conj (F.η v w) := (hHerm w v).symm
  have hsq : F.η v w * conj (F.η v w) = (‖F.η v w‖ ^ 2 : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  unfold mixture mass
  simp only [F.add_left, F.add_right, F.smul_left, F.smul_right, hv, hwv,
    map_mul, Complex.conj_ofReal, zero_add]
  rw [self_eq_real F hHerm w]
  push_cast
  calc
    _ = (F.η v w * conj (F.η v w)) *
        (2 * (h : ℂ) + (h : ℂ) ^ 2 * ((F.η w w).re : ℂ)) := by ring
    _ = _ := by rw [hsq]; simp only [Complex.ofReal_re]

theorem scalar_mass_bounds {b C h : ℝ} (hh : 0 < h)
    (hsmall : h ≤ 1 / (1 + |C|)) :
    h * b ^ 2 ≤ b ^ 2 * (2 * h + h ^ 2 * C) ∧
      b ^ 2 * (2 * h + h ^ 2 * C) ≤ 3 * h * b ^ 2 := by
  have hden : 0 < 1 + |C| := by positivity
  have hbound := (le_div_iff₀ hden).mp hsmall
  have habs : h * |C| ≤ 1 := by nlinarith
  have hCupper : h * C ≤ 1 :=
    (mul_le_mul_of_nonneg_left (le_abs_self C) hh.le).trans habs
  have hClower : -1 ≤ h * C := by
    have hl := mul_le_mul_of_nonneg_left (neg_abs_le C) hh.le
    nlinarith
  have hbase : 0 ≤ h * b ^ 2 := mul_nonneg hh.le (sq_nonneg b)
  constructor
  · calc
      h * b ^ 2 = h * b ^ 2 * 1 := by ring
      _ ≤ h * b ^ 2 * (2 + h * C) :=
        mul_le_mul_of_nonneg_left (by linarith) hbase
      _ = _ := by ring
  · calc
      _ = h * b ^ 2 * (2 + h * C) := by ring
      _ ≤ h * b ^ 2 * 3 := mul_le_mul_of_nonneg_left (by linarith) hbase
      _ = _ := by ring

theorem mass_bounds (F : AdditiveScalarForm E) (v w : E) {h : ℝ}
    (hh : 0 < h) (hsmall : h ≤ 1 / (1 + |(F.η w w).re|)) :
    h * ‖F.η v w‖ ^ 2 ≤ mass F v w h ∧
      mass F v w h ≤ 3 * h * ‖F.η v w‖ ^ 2 :=
  scalar_mass_bounds hh hsmall

theorem mass_pos (F : AdditiveScalarForm E) {v w : E}
    (hB : F.η v w ≠ 0) {h : ℝ} (hh : 0 < h)
    (hsmall : h ≤ 1 / (1 + |(F.η w w).re|)) : 0 < mass F v w h := by
  have hl := (mass_bounds F v w hh hsmall).1
  have hp : 0 < h * ‖F.η v w‖ ^ 2 :=
    mul_pos hh (sq_pos_of_pos (norm_pos_iff.mpr hB))
  exact hp.trans_le hl

theorem normalized_mass (F : AdditiveScalarForm E) {x : E} {q : ℝ}
    (hq : 0 < q) (hmass : F.η x x = (q : ℂ)) :
    F.η (normalize q x) (normalize q x) = 1 := by
  have hs : Real.sqrt q ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hq)
  have hsc : (Real.sqrt q : ℂ) ≠ 0 := by exact_mod_cast hs
  rw [normalize, F.smul_left, F.smul_right, hmass]
  simp only [map_inv₀, Complex.conj_ofReal]
  have hsq : (Real.sqrt q : ℂ) ^ 2 = (q : ℂ) := by
    exact_mod_cast Real.sq_sqrt hq.le
  field_simp
  exact hsq.symm

theorem normalized_mixture_mass (F : AdditiveScalarForm E)
    (hHerm : ∀ x y, conj (F.η y x) = F.η x y)
    {v w : E} (hv : F.η v v = 0) (hB : F.η v w ≠ 0) {h : ℝ}
    (hh : 0 < h) (hsmall : h ≤ 1 / (1 + |(F.η w w).re|)) :
    F.η (normalize (mass F v w h) (mixture F v w h))
      (normalize (mass F v w h) (mixture F v w h)) = 1 :=
  normalized_mass F (mass_pos F hB hh hsmall) (mixture_mass F hHerm hv h)

theorem normalized_mixture_nonzero (F : AdditiveScalarForm E)
    (hHerm : ∀ x y, conj (F.η y x) = F.η x y)
    {v w : E} (hv : F.η v v = 0) (hB : F.η v w ≠ 0) {h : ℝ}
    (hh : 0 < h) (hsmall : h ≤ 1 / (1 + |(F.η w w).re|)) :
    normalize (mass F v w h) (mixture F v w h) ≠ 0 := by
  intro hz
  have hm := normalized_mixture_mass F hHerm hv hB hh hsmall
  rw [hz] at hm
  have hzero : F.η (0 : E) 0 = 0 := by
    simpa using F.smul_left 0 (0 : E) (0 : E)
  rw [hzero] at hm
  exact zero_ne_one hm

theorem normalized_residual_identity (F : AdditiveScalarForm E)
    (T : E →ₗ[ℂ] E) {v w : E} {μ : ℂ} (heigen : T v = μ • v) (h : ℝ) :
    T (normalize (mass F v w h) (mixture F v w h)) -
        μ • normalize (mass F v w h) (mixture F v w h) =
      ((Real.sqrt (mass F v w h) : ℂ)⁻¹ * (h : ℂ) * F.η v w) • (T w - μ • w) := by
  simp only [normalize, mixture, map_smul, map_add, heigen,
    smul_add, smul_smul, smul_sub]
  module

end Reinmann.PacketMass
