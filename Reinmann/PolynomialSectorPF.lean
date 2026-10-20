/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.QuadraticPF
import Reinmann.AnalyticPFLimit
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree

/-! Schoenberg's polynomial sector sufficiency theorem. The proof extracts
real linear and conjugate quadratic factors with multiplicities retained. -/
noncomputable section
namespace Reinmann.PolynomialSectorPF
open Polynomial

theorem finitePF_constant {c : ℝ} (hc : 0 ≤ c) (r : ℕ) :
    FinitePF (fun n => (C c : Polynomial ℝ).coeff n) r := by
  have h := finitePF_nonneg_scale (FinitePFConvolution.finitePF_one r) hc
  simpa only [Polynomial.coeff_C, PowerSeries.coeff_one, mul_ite, mul_one, mul_zero] using h

theorem finitePF_negative_real_factor {a : ℝ} (ha : a < 0) (r : ℕ) :
    FinitePF (fun n => (X - C a : Polynomial ℝ).coeff n) r := by
  have hp : 0 < -a := neg_pos.mpr ha
  have h := finitePF_nonneg_scale
    (FinitePFConvolution.finitePF_linear_polynomial (inv_nonneg.mpr hp.le) r) hp.le
  have he (n : ℕ) : (X - C a : Polynomial ℝ).coeff n =
      -a * (1 + C (-a)⁻¹ * X : Polynomial ℝ).coeff n := by
    rcases n with _ | _ | n
    all_goals simp only [Polynomial.coeff_sub, Polynomial.coeff_add,
      Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_C,
      Polynomial.coeff_one]
    all_goals simp <;> field_simp [ne_of_gt hp, ne_of_lt ha]
  simpa only [← he] using h

private theorem extract_factor {r : ℕ} (hr : 1 ≤ r) {p : Polynomial ℝ}
    (hp0 : 0 < p.coeff 0) (hpdeg : 0 < p.natDegree)
    (hsector : ∀ z : ℂ, aeval z p = 0 →
      Real.pi - Real.pi / ((r : ℝ) + 1) ≤ |Complex.arg z|) :
    ∃ f q : Polynomial ℝ, p = f * q ∧ 0 < f.coeff 0 ∧
      0 < f.natDegree ∧ FinitePF (fun n => f.coeff n) r := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero ℂ p
    (ne_of_gt (Polynomial.natDegree_pos_iff_degree_pos.mp hpdeg))
  have hzne : z ≠ 0 := by
    intro h
    subst z
    have hcoeff : (p.coeff 0 : ℂ) = 0 := by
      simpa only [← Polynomial.coeff_zero_eq_aeval_zero'] using hz
    exact hp0.ne' (Complex.ofReal_eq_zero.mp hcoeff)
  by_cases him : z.im = 0
  · have hzreal : (z.re : ℂ) = z := by apply Complex.ext <;> simp [him]
    have hneg : z.re < 0 := by
      by_contra hn
      have hre : 0 ≤ z.re := le_of_not_gt hn
      have harg : Complex.arg z = 0 := by
        rw [← hzreal]
        exact Complex.arg_ofReal_of_nonneg hre
      have h := hsector z hz
      rw [harg, abs_zero] at h
      have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
      have hden : 0 < (r : ℝ) + 1 := by positivity
      have hbound : Real.pi / ((r : ℝ) + 1) ≤ Real.pi / 2 :=
        div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) (by linarith)
      linarith [Real.pi_pos]
    have hroot : p.IsRoot z.re := by
      change p.eval z.re = 0
      have hh : aeval (z.re : ℂ) p = 0 := by rw [hzreal]; exact hz
      have heval : ((p.eval z.re : ℝ) : ℂ) = aeval (z.re : ℂ) p :=
        (Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval
          (R := ℝ) (A := ℂ) z.re p).symm
      exact Complex.ofReal_eq_zero.mp (heval.trans hh)
    obtain ⟨q, hq⟩ := Polynomial.dvd_iff_isRoot.mpr hroot
    refine ⟨X - C z.re, q, hq, ?_, ?_, finitePF_negative_real_factor hneg r⟩
    · simpa only [coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub] using neg_pos.mpr hneg
    · rw [Polynomial.natDegree_X_sub_C]
      norm_num
  · let f : Polynomial ℝ := X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2)
    obtain ⟨q, hq⟩ := p.quadratic_dvd_of_aeval_eq_zero_im_ne_zero hz him
    refine ⟨f, q, hq, ?_, ?_, QuadraticPF.finitePF_conjugate_pair hzne (hsector z hz)⟩
    · have hn := norm_pos_iff.mpr hzne
      have hf0 : f.coeff 0 = ‖z‖ ^ 2 := by
        simp only [f, Polynomial.coeff_add, Polynomial.coeff_sub,
          Polynomial.coeff_X_pow, Polynomial.coeff_C_mul, Polynomial.coeff_X,
          Polynomial.coeff_C]
        norm_num
      rw [hf0]
      exact sq_pos_of_pos hn
    · rw [Polynomial.isMonicOfDegree_sub_add_two (2 * z.re) (‖z‖ ^ 2) |>.natDegree_eq]
      norm_num

/-- Closed-sector polynomial sufficiency for all arbitrary ordered minors.
Repeated roots, modulus ties and boundary angles are allowed. -/
theorem finitePF_of_zero_sector {p : Polynomial ℝ} {r : ℕ}
    (hp0 : 0 < p.coeff 0)
    (hsector : ∀ z : ℂ, aeval z p = 0 →
      Real.pi - Real.pi / ((r : ℝ) + 1) ≤ |Complex.arg z|) :
    FinitePF (fun n => p.coeff n) r := by
  by_cases hr0 : r = 0
  · subst r
    intro k hk rows cols _ _
    have hk0 : k = 0 := by omega
    subst k
    simp [Matrix.det_fin_zero]
  have hr : 1 ≤ r := by omega
  have H : ∀ d, ∀ p : Polynomial ℝ, p.natDegree = d → 0 < p.coeff 0 →
      (∀ z : ℂ, aeval z p = 0 →
        Real.pi - Real.pi / ((r : ℝ) + 1) ≤ |Complex.arg z|) →
      FinitePF (fun n => p.coeff n) r := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro p hd hp0 hs
      by_cases hd0 : d = 0
      · have he := Polynomial.eq_C_of_natDegree_eq_zero (hd.trans hd0)
        rw [he]
        exact finitePF_constant hp0.le r
      obtain ⟨f, q, hpq, hf0, hfdeg, hf⟩ := extract_factor hr hp0 (by omega) hs
      have hpne : p ≠ 0 := by intro h; simp [h] at hp0
      have hfne : f ≠ 0 := by intro h; simp [h] at hf0
      have hqne : q ≠ 0 := by intro h; apply hpne; rw [hpq, h, mul_zero]
      have hdeg := Polynomial.natDegree_mul hfne hqne
      rw [← hpq, hd] at hdeg
      have hqdeg : q.natDegree < d := by omega
      have h0 : p.coeff 0 = f.coeff 0 * q.coeff 0 := by
        rw [hpq]
        exact Polynomial.mul_coeff_zero f q
      have hq0 : 0 < q.coeff 0 := by nlinarith
      have hsq (z : ℂ) (hz : aeval z q = 0) :
          Real.pi - Real.pi / ((r : ℝ) + 1) ≤ |Complex.arg z| := by
        apply hs z
        rw [hpq, map_mul, hz, mul_zero]
      rw [hpq]
      exact FinitePFConvolution.finitePF_polynomial_mul hf
        (ih q.natDegree hqdeg q rfl hq0 hsq)
  exact H p.natDegree p rfl hp0 hsector

/-- The usual zero-free open-sector formulation of polynomial sufficiency. -/
theorem finitePF_of_sector_zero_free {p : Polynomial ℝ} {r : ℕ}
    (hp0 : 0 < p.coeff 0)
    (hfree : ∀ z : ℂ, |Complex.arg z| < Real.pi * (r : ℝ) / ((r : ℝ) + 1) →
      aeval z p ≠ 0) : FinitePF (fun n => p.coeff n) r := by
  apply finitePF_of_zero_sector hp0
  intro z hz
  have hangle : Real.pi - Real.pi / ((r : ℝ) + 1) =
      Real.pi * (r : ℝ) / ((r : ℝ) + 1) := by
    have hd : (r : ℝ) + 1 ≠ 0 := ne_of_gt (by positivity)
    field_simp [hd]
    ring
  rw [hangle]
  exact le_of_not_gt (fun hlt => hfree z hlt hz)

/-- The polynomial sector theorem followed by the existing analytic limit
bridge. Degrees may grow unboundedly; no zero simplicity or modulus ordering
is imposed. Applications must supply actual polynomial approximants. -/
theorem finitePF_of_sector_polynomial_limit {ι : Type*} {l : Filter ι} [l.NeBot]
    {p : ι → Polynomial ℝ} {f : ℂ → ℂ} {a : ℕ → ℝ} {r : ℕ}
    (hlim : TendstoLocallyUniformlyOn
      (fun j z => ((p j).map (algebraMap ℝ ℂ)).eval z) f l Set.univ)
    (hpolys : ∀ᶠ j in l, 0 < (p j).coeff 0 ∧ ∀ z : ℂ, aeval z (p j) = 0 →
      Real.pi - Real.pi / ((r : ℝ) + 1) ≤ |Complex.arg z|)
    (hcoeff : ∀ n, iteratedDeriv n f 0 / (n.factorial : ℂ) = (a n : ℂ)) :
    FinitePF a r := by
  apply finitePF_of_real_polynomial_locallyUniformLimit hlim _ hcoeff
  exact hpolys.mono (fun j hj => finitePF_of_zero_sector hj.1 hj.2)

end Reinmann.PolynomialSectorPF
