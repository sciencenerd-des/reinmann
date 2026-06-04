/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal, OpenAI Codex
-/
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Riemann Hypothesis proof spine

This file records a Lean-checked reduction toward mathlib's
`RiemannHypothesis` target. It verifies known supporting facts from mathlib and
isolates the remaining obligations without asserting that those obligations are
proved.
-/

noncomputable section

namespace Reinmann

/--
One of the standard negative even zeros of the Riemann zeta function.
-/
def IsTrivialZetaZero (s : Complex) : Prop :=
  ∃ n : Nat, s = (-2 : Complex) * ((n : Complex) + 1)

/--
The critical line in the complex plane.
-/
def OnCriticalLine (s : Complex) : Prop :=
  s.re = 1 / 2

/--
The central remaining obligation after using existing mathlib facts.
-/
structure CriticalStripObligations where
  strip_zero_on_line :
    ∀ s : Complex, 0 < s.re -> s.re < 1 -> riemannZeta s = 0 -> OnCriticalLine s

/--
A one-sided zero-free formulation for the open right half of the critical
strip. Because strip zeros reflect under `s ↦ 1 - s`, this is enough to imply
the full critical-strip obligation.
-/
def RightHalfStripZeroFree : Prop :=
  ∀ s : Complex, 1 / 2 < s.re -> s.re < 1 -> riemannZeta s ≠ 0

/--
Mathlib already proves that the Riemann zeta function has no zeros on
`re s >= 1`.
-/
theorem no_zeta_zeros_on_or_right_of_one {s : Complex}
    (hs : 1 ≤ s.re) : riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re hs

/--
Mathlib already proves the standard negative even zeros.
-/
theorem trivial_negative_even_zeta_zero (n : Nat) :
    riemannZeta ((-2 : Complex) * ((n : Complex) + 1)) = 0 :=
  riemannZeta_neg_two_mul_nat_add_one n

/--
A point strictly to the right of the critical line cannot be one of the
standard negative even zeros.
-/
theorem not_trivial_of_re_gt_half {s : Complex}
    (hs : (1 / 2 : Real) < s.re) : ¬ IsTrivialZetaZero s := by
  intro htrivial
  rcases htrivial with ⟨n, hs_eq⟩
  have hre := congrArg Complex.re hs_eq
  norm_num [IsTrivialZetaZero, Complex.mul_re, Complex.add_re, Complex.natCast_re] at hre
  have hn_nonneg : 0 ≤ (n : Real) := Nat.cast_nonneg n
  linarith

/--
The zeta value at zero is not a zero. Mathlib records `ζ(0) = -1 / 2`.
-/
theorem riemannZeta_zero_ne_zero : riemannZeta (0 : Complex) ≠ 0 := by
  rw [riemannZeta_zero]
  norm_num

/--
A point with positive real part is not a nonpositive integer.
-/
theorem ne_neg_nat_of_re_pos {s : Complex} (hs : 0 < s.re) :
    ∀ n : Nat, s ≠ -(n : Complex) := by
  intro n hs_eq
  have hre := congrArg Complex.re hs_eq
  simp only [Complex.neg_re, Complex.natCast_re] at hre
  have hn_nonneg : 0 ≤ (n : Real) := Nat.cast_nonneg n
  linarith

/--
A point with real part strictly less than one is not `1`.
-/
theorem ne_one_of_re_lt_one {s : Complex} (hs : s.re < 1) : s ≠ 1 := by
  intro hs_eq
  have hre := congrArg Complex.re hs_eq
  simp only [Complex.one_re] at hre
  linarith

/--
If `s` is on or left of the imaginary axis, then `1 - s` is not a
nonpositive integer. This is the side condition needed to apply
`riemannZeta_one_sub` to `1 - s`.
-/
theorem one_sub_ne_neg_nat_of_re_nonpos {s : Complex} (hs : s.re ≤ 0) :
    ∀ n : Nat, 1 - s ≠ -(n : Complex) := by
  intro n hn
  have hre := congrArg Complex.re hn
  simp only [Complex.sub_re, Complex.one_re, Complex.neg_re] at hre
  norm_num at hre
  have hn_nonneg : 0 ≤ (n : Real) := Nat.cast_nonneg n
  linarith

/--
Analytic reduction for the left half-plane: any zeta zero with `s.re <= 0`
forces the cosine factor in the functional equation to vanish.
-/
theorem cos_factor_zero_of_left_zero {s : Complex}
    (hs : s.re ≤ 0) (hz : riemannZeta s = 0) :
    Complex.cos (Real.pi * (1 - s) / 2) = 0 := by
  by_cases hs0 : s = 0
  · subst s
    exact False.elim (riemannZeta_zero_ne_zero hz)
  · have honeSub_re : 1 ≤ (1 - s).re := by
      rw [Complex.sub_re, Complex.one_re]
      linarith
    have hzeta_one_sub : riemannZeta (1 - s) ≠ 0 :=
      riemannZeta_ne_zero_of_one_le_re honeSub_re
    have hnot_neg_nat : ∀ n : Nat, 1 - s ≠ -(n : Complex) :=
      one_sub_ne_neg_nat_of_re_nonpos hs
    have honeSub_ne_one : 1 - s ≠ 1 := by
      intro h
      apply hs0
      linear_combination -h
    have hfe := riemannZeta_one_sub (s := 1 - s) hnot_neg_nat honeSub_ne_one
    have hfe_norm : riemannZeta s =
        2 * (2 * ↑Real.pi) ^ (-(1 - s)) * Complex.Gamma (1 - s) *
          Complex.cos (↑Real.pi * (1 - s) / 2) * riemannZeta (1 - s) := by
      simpa using hfe
    have hprod : 2 * (2 * ↑Real.pi) ^ (-(1 - s)) * Complex.Gamma (1 - s) *
        Complex.cos (↑Real.pi * (1 - s) / 2) * riemannZeta (1 - s) = 0 := by
      rw [hz] at hfe_norm
      simpa using hfe_norm.symm
    rcases mul_eq_zero.mp hprod with hprod_nozeta | hzeta
    · rcases mul_eq_zero.mp hprod_nozeta with hprod_nocos | hcos
      · rcases mul_eq_zero.mp hprod_nocos with hprod_nogamma | hgamma
        · rcases mul_eq_zero.mp hprod_nogamma with htwo | hpow
          · norm_num at htwo
          · have hbase : (2 * (↑Real.pi : Complex)) ≠ 0 := by
              norm_num [Real.pi_ne_zero]
            have hpow_ne : (2 * (↑Real.pi : Complex)) ^ (-(1 - s)) ≠ 0 := by
              rw [Ne, Complex.cpow_eq_zero_iff]
              exact not_and_of_not_left _ hbase
            exact False.elim (hpow_ne hpow)
        · have hgamma_ne : Complex.Gamma (1 - s) ≠ 0 :=
            Complex.Gamma_ne_zero hnot_neg_nat
          exact False.elim (hgamma_ne hgamma)
      · exact hcos
    · exact False.elim (hzeta_one_sub hzeta)

/--
Zeros of the Riemann zeta function on or left of the imaginary axis are exactly
the standard negative even zeros.
-/
theorem left_of_strip_zero_is_trivial {s : Complex}
    (hs : s.re ≤ 0) (hz : riemannZeta s = 0) : IsTrivialZetaZero s := by
  have hcos := cos_factor_zero_of_left_zero hs hz
  rcases Complex.cos_eq_zero_iff.mp hcos with ⟨k, hk⟩
  have hpi : (↑Real.pi : Complex) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hpi2 : (↑Real.pi : Complex) / 2 ≠ 0 :=
    div_ne_zero hpi two_ne_zero
  have hk_scaled : ((↑Real.pi : Complex) / 2) * (1 - s) =
      ((↑Real.pi : Complex) / 2) * (2 * (k : Complex) + 1) := by
    linear_combination hk
  have hraw : 1 - s = 2 * (k : Complex) + 1 :=
    mul_left_cancel₀ hpi2 hk_scaled
  have hsk : s = -2 * (k : Complex) := by
    linear_combination -hraw
  have hk_nonneg : 0 ≤ k := by
    have hlecast : (-2 * (k : Complex)).re ≤ 0 := by
      simpa [hsk] using hs
    norm_num [Complex.mul_re, Complex.neg_re, Complex.intCast_re] at hlecast ⊢
    linarith
  have hk_ne_zero : k ≠ 0 := by
    intro hk0
    have hs0 : s = 0 := by
      simp [hsk, hk0]
    have hz_at_zero : riemannZeta (0 : Complex) = 0 := by
      simpa [hs0] using hz
    exact riemannZeta_zero_ne_zero hz_at_zero
  have hk_pos : 0 < k := lt_of_le_of_ne hk_nonneg (Ne.symm hk_ne_zero)
  obtain ⟨n, hkn⟩ : ∃ n : Nat, (k : Complex) = (n : Complex) + 1 := by
    refine ⟨k.toNat - 1, ?_⟩
    have hknat : (k.toNat : Int) = k :=
      Int.toNat_of_nonneg (le_of_lt hk_pos)
    have hknat_ne_zero : k.toNat ≠ 0 := by
      intro hzero
      have hk_le_zero : k ≤ 0 := Int.toNat_eq_zero.mp hzero
      linarith
    have hsucc : k.toNat - 1 + 1 = k.toNat := by omega
    have hsucc_int : ((k.toNat - 1 + 1 : Nat) : Int) = k := by
      rw [hsucc, hknat]
    have hcast : ((k.toNat - 1 : Nat) : Int) + 1 = k := by
      norm_num at hsucc_int ⊢
      exact hsucc_int
    exact_mod_cast hcast.symm
  refine ⟨n, ?_⟩
  rw [hsk, hkn]

/--
Reflection across the critical line preserves the open critical strip.
-/
theorem reflected_point_in_strip {s : Complex}
    (hpos : 0 < s.re) (hlt : s.re < 1) :
    0 < (1 - s).re ∧ (1 - s).re < 1 := by
  constructor
  · rw [Complex.sub_re, Complex.one_re]
    linarith
  · rw [Complex.sub_re, Complex.one_re]
    linarith

/--
Inside the critical strip, a zeta zero reflects to another zeta zero under
`s ↦ 1 - s`.
-/
theorem strip_zero_reflects {s : Complex}
    (hpos : 0 < s.re) (hlt : s.re < 1) (hz : riemannZeta s = 0) :
    riemannZeta (1 - s) = 0 := by
  have hnot_neg_nat : ∀ n : Nat, s ≠ -(n : Complex) :=
    ne_neg_nat_of_re_pos hpos
  have hs_ne_one : s ≠ 1 :=
    ne_one_of_re_lt_one hlt
  have hfe := riemannZeta_one_sub (s := s) hnot_neg_nat hs_ne_one
  rw [hz] at hfe
  simpa using hfe

/--
The non-zeta prefactor in the functional equation is nonzero throughout the
open critical strip.
-/
theorem functionalEquation_prefactor_ne_zero_in_strip {s : Complex}
    (hpos : 0 < s.re) (hlt : s.re < 1) :
    2 * (2 * ↑Real.pi) ^ (-s) * Complex.Gamma s *
      Complex.cos (↑Real.pi * s / 2) ≠ 0 := by
  have hnot_neg_nat : ∀ n : Nat, s ≠ -(n : Complex) :=
    ne_neg_nat_of_re_pos hpos
  have hbase : (2 * (↑Real.pi : Complex)) ≠ 0 := by
    norm_num [Real.pi_ne_zero]
  have hpow_ne : (2 * (↑Real.pi : Complex)) ^ (-s) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact not_and_of_not_left _ hbase
  have hgamma_ne : Complex.Gamma s ≠ 0 :=
    Complex.Gamma_ne_zero hnot_neg_nat
  have hcos_ne : Complex.cos (↑Real.pi * s / 2) ≠ 0 := by
    intro hcos
    rcases Complex.cos_eq_zero_iff.mp hcos with ⟨k, hk⟩
    have hpi : (↑Real.pi : Complex) ≠ 0 := by
      exact_mod_cast Real.pi_ne_zero
    have hpi2 : (↑Real.pi : Complex) / 2 ≠ 0 :=
      div_ne_zero hpi two_ne_zero
    have hk_scaled : ((↑Real.pi : Complex) / 2) * s =
        ((↑Real.pi : Complex) / 2) * (2 * (k : Complex) + 1) := by
      linear_combination hk
    have hs_eq : s = 2 * (k : Complex) + 1 :=
      mul_left_cancel₀ hpi2 hk_scaled
    have hre : s.re = (2 * (k : Complex) + 1).re := by
      rw [hs_eq]
    norm_num [Complex.mul_re, Complex.add_re, Complex.intCast_re] at hre
    have hk_lt : (2 * k + 1 : Int) < 1 := by
      exact_mod_cast (by linarith : (2 * (k : Real) + 1) < 1)
    have hk_pos : 0 < (2 * k + 1 : Int) := by
      exact_mod_cast (by linarith : (0 : Real) < 2 * (k : Real) + 1)
    omega
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero two_ne_zero hpow_ne) hgamma_ne)
    hcos_ne

/--
Inside the critical strip, zerohood is equivalent for `s` and its reflection
`1 - s`.
-/
theorem strip_zero_reflection_iff {s : Complex}
    (hpos : 0 < s.re) (hlt : s.re < 1) :
    riemannZeta (1 - s) = 0 ↔ riemannZeta s = 0 := by
  constructor
  · intro hz_reflect
    have hstrip := reflected_point_in_strip hpos hlt
    have h := strip_zero_reflects hstrip.1 hstrip.2 hz_reflect
    simpa using h
  · intro hz
    exact strip_zero_reflects hpos hlt hz

/--
By reflection, it is enough to prove there are no zeros in the open right half
of the critical strip.
-/
theorem criticalStripObligations_of_rightHalfStripZeroFree
    (h : RightHalfStripZeroFree) : CriticalStripObligations where
  strip_zero_on_line := by
    intro s hpos hlt hz
    rcases lt_trichotomy s.re (1 / 2 : Real) with hleft | heq | hright
    · have hz_reflect := strip_zero_reflects hpos hlt hz
      have hstrip_reflect := reflected_point_in_strip hpos hlt
      have hright_reflect : 1 / 2 < (1 - s).re := by
        rw [Complex.sub_re, Complex.one_re]
        linarith
      exact False.elim ((h (1 - s) hright_reflect hstrip_reflect.2) hz_reflect)
    · exact heq
    · exact False.elim ((h s hright hlt) hz)

/--
A verified reduction: if the two remaining obligations are supplied, then
mathlib's formal statement of the Riemann Hypothesis follows.
-/
theorem riemannHypothesis_from_obligations
    (h : CriticalStripObligations) : RiemannHypothesis := by
  intro s hz hnotTrivial hsNotOne
  by_cases hle0 : s.re ≤ 0
  · exact False.elim (hnotTrivial (left_of_strip_zero_is_trivial hle0 hz))
  · have hpos : 0 < s.re := lt_of_not_ge hle0
    by_cases hge1 : 1 ≤ s.re
    · exact False.elim ((no_zeta_zeros_on_or_right_of_one hge1) hz)
    · have hlt1 : s.re < 1 := lt_of_not_ge hge1
      exact h.strip_zero_on_line s hpos hlt1 hz

/--
A one-sided zero-free theorem for the open right half of the critical strip
would prove mathlib's formal statement of the Riemann Hypothesis.
-/
theorem riemannHypothesis_of_rightHalfStripZeroFree
    (h : RightHalfStripZeroFree) : RiemannHypothesis :=
  riemannHypothesis_from_obligations
    (criticalStripObligations_of_rightHalfStripZeroFree h)

/--
Conversely, mathlib's formal Riemann Hypothesis statement rules out zeros in
the open right half of the critical strip.
-/
theorem rightHalfStripZeroFree_of_riemannHypothesis
    (h : RiemannHypothesis) : RightHalfStripZeroFree := by
  intro s hhalf hlt hz
  have hnotTrivial : ¬ IsTrivialZetaZero s :=
    not_trivial_of_re_gt_half hhalf
  have hs_ne_one : s ≠ 1 :=
    ne_one_of_re_lt_one hlt
  have hline : s.re = 1 / 2 :=
    h s hz hnotTrivial hs_ne_one
  linarith

/--
The one-sided zero-free target is equivalent to mathlib's formal Riemann
Hypothesis statement.
-/
theorem rightHalfStripZeroFree_iff_riemannHypothesis :
    RightHalfStripZeroFree ↔ RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_rightHalfStripZeroFree
  · exact rightHalfStripZeroFree_of_riemannHypothesis

/--
Failure of mathlib's formal Riemann Hypothesis is equivalent to the existence
of a zeta zero in the open right half of the critical strip.
-/
theorem not_riemannHypothesis_iff_exists_rightHalfStrip_zero :
    ¬ RiemannHypothesis ↔
      ∃ s : Complex, 1 / 2 < s.re ∧ s.re < 1 ∧ riemannZeta s = 0 := by
  classical
  rw [← rightHalfStripZeroFree_iff_riemannHypothesis]
  unfold RightHalfStripZeroFree
  push Not
  exact Iff.rfl

end Reinmann
