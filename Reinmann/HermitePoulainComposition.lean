/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.JensenProgram
import Reinmann.JensenTuranBridge
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.QuadraticDiscriminant

/-!
# Hermite--Poulain / Schur--Szegő composition surface

This file fixes the ordinary-monomial coefficient convention used by the Jensen
route.  The raw Hadamard operation is recorded separately and its failure of
hyperbolicity preservation is proved explicitly.  The binomial-normalized
Schur--Szegő operation is the corrected target; its general
real-rootedness-preservation theorem is deliberately named as a `Prop` target.
-/

noncomputable section

open Polynomial

namespace Reinmann

/-- Raw Hadamard coefficientwise multiplication, truncated at degree `d`.
This is *not* the finite Schur--Szegő operation in the ordinary monomial
coefficient convention. -/
def coefficientwiseComposition (d : ℕ) (p q : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ Finset.range (d + 1),
    C (p.coeff k * q.coeff k) * X ^ k

/-- Finite Schur--Szegő composition in the ordinary monomial coefficient
convention.  The binomial normalization is essential: if
`p = ∑ choose d k aₖ X^k` and `q = ∑ choose d k bₖ X^k`, then this operation is
`∑ choose d k (aₖ bₖ) X^k`. -/
def schurSzegoComposition (d : ℕ) (p q : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ Finset.range (d + 1),
    C ((p.coeff k * q.coeff k) / (Nat.choose d k : ℝ)) * X ^ k

/- The real Schur--Szegő theorem requires one factor's real roots to have a
common sign.  Keeping this condition explicit prevents the false unrestricted
statement from re-entering the proof surface. -/
def PolynomialRootsSameSign (q : ℝ[X]) : Prop :=
  (∀ x : ℝ, q.IsRoot x → x ≤ 0) ∨
    (∀ x : ℝ, q.IsRoot x → 0 ≤ x)

/-- The general composition theorem needed by the Jensen/Laguerre--Pólya route.
The same-sign-root hypothesis is part of the classical real
Hermite--Poulain/Schur--Szegő statement.  It is a target, not an assumption:
the proof remains the full composition blocker. -/
def HermitePoulainSchurSzegoTheorem : Prop :=
  ∀ (d : ℕ) (p q : ℝ[X]),
    p.natDegree = d → q.natDegree = d →
      PolynomialHyperbolic p → PolynomialHyperbolic q →
        PolynomialRootsSameSign q →
        PolynomialHyperbolic (schurSzegoComposition d p q)

/-- Explicit degree-`1` composition law. -/
theorem schurSzegoComposition_one (p q : ℝ[X]) :
    schurSzegoComposition 1 p q =
      C (p.coeff 0 * q.coeff 0) + C (p.coeff 1 * q.coeff 1) * X := by
  unfold schurSzegoComposition
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero]

/- The explicit degree-`2` Schur--Szegő coefficient law.  This is the
ordinary-monomial form of the binomial normalization: only the middle
coefficient is divided by `choose 2 1 = 2`. -/
theorem schurSzegoComposition_two (p q : ℝ[X]) :
    schurSzegoComposition 2 p q =
      C (p.coeff 0 * q.coeff 0) +
        C ((p.coeff 1 * q.coeff 1) / 2) * X +
        C (p.coeff 2 * q.coeff 2) * X ^ 2 := by
  unfold schurSzegoComposition
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero]

/- The corresponding explicit degree-`3` coefficient law. -/
theorem schurSzegoComposition_three (p q : ℝ[X]) :
    schurSzegoComposition 3 p q =
      C (p.coeff 0 * q.coeff 0) +
        C ((p.coeff 1 * q.coeff 1) / 3) * X +
        C ((p.coeff 2 * q.coeff 2) / 3) * X ^ 2 +
        C (p.coeff 3 * q.coeff 3) * X ^ 3 := by
  unfold schurSzegoComposition
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero]

/- A coefficient-level degree-`2` discriminant certificate.  If both input
quadratics have nonnegative discriminant and their endpoint products are
nonnegative, then the normalized Schur--Szegő output has nonnegative
discriminant.  The statement is intentionally algebraic; connecting these
coefficient hypotheses to `PolynomialHyperbolic` is the remaining
same-sign-root theorem. -/
theorem schurSzegoComposition_two_discriminant_nonneg
    {a₀ a₁ a₂ b₀ b₁ b₂ : ℝ}
    (ha : 0 ≤ a₁ ^ 2 - 4 * a₀ * a₂)
    (hb : 0 ≤ b₁ ^ 2 - 4 * b₀ * b₂)
    (hb₀₂ : 0 ≤ b₀ * b₂) :
    0 ≤ (a₁ * b₁ / 2) ^ 2 - 4 * (a₀ * b₀) * (a₂ * b₂) := by
  have ha' : 4 * (a₀ * a₂) ≤ a₁ ^ 2 := by
    nlinarith
  have hb' : 4 * (b₀ * b₂) ≤ b₁ ^ 2 := by
    nlinarith
  have hleft : 0 ≤ 4 * (b₀ * b₂) := by positivity
  have hright : 0 ≤ a₁ ^ 2 := sq_nonneg _
  have hmul : (4 * (a₀ * a₂)) * (4 * (b₀ * b₂)) ≤
      (a₁ ^ 2) * (b₁ ^ 2) := by
    exact mul_le_mul ha' hb' hleft hright
  nlinarith [hmul]

/- Completing the square turns a nonnegative real discriminant into a direct
hyperbolicity proof for a genuine quadratic. -/
theorem polynomialHyperbolic_quadratic_of_discriminant
    {a₀ a₁ a₂ : ℝ} (ha₂ : a₂ ≠ 0)
    (hD : 0 ≤ a₁ ^ 2 - 4 * a₀ * a₂) :
    PolynomialHyperbolic (C a₀ + C a₁ * X + C a₂ * X ^ 2) := by
  intro z hz
  have hz' : (a₂ : ℂ) * z ^ 2 + (a₁ : ℂ) * z + (a₀ : ℂ) = 0 := by
    simpa [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_X, Polynomial.map_pow, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_pow, Complex.coe_algebraMap, add_comm, add_left_comm,
      add_assoc] using hz
  have hw : (2 * (a₂ : ℂ) * z + (a₁ : ℂ)) ^ 2 =
      ((a₁ ^ 2 - 4 * a₀ * a₂ : ℝ) : ℂ) := by
    calc
      (2 * (a₂ : ℂ) * z + (a₁ : ℂ)) ^ 2 =
          4 * (a₂ : ℂ) * ((a₂ : ℂ) * z ^ 2 + (a₁ : ℂ) * z + (a₀ : ℂ)) +
            ((a₁ ^ 2 - 4 * a₀ * a₂ : ℝ) : ℂ) := by
              push_cast
              ring
      _ = ((a₁ ^ 2 - 4 * a₀ * a₂ : ℝ) : ℂ) := by
        rw [hz']
        simp
  have him : (2 * (a₂ : ℂ) * z + (a₁ : ℂ)).im = 0 :=
    im_zero_of_sq_eq_nonneg_real hD hw
  have he : a₂ * z.im = 0 := by
    simpa [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im] using him
  rcases mul_eq_zero.mp he with h | h
  · exact absurd h ha₂
  · exact h

/- The preceding two algebraic lemmas compose into a genuine degree-`2`
Schur--Szegő preservation theorem under explicit coefficient hypotheses. -/
theorem schurSzegoComposition_two_hyperbolic_of_discriminant
    {a₀ a₁ a₂ b₀ b₁ b₂ : ℝ}
    (ha₂ : a₂ ≠ 0) (hb₂ : b₂ ≠ 0)
    (ha : 0 ≤ a₁ ^ 2 - 4 * a₀ * a₂)
    (hb : 0 ≤ b₁ ^ 2 - 4 * b₀ * b₂)
    (hb₀₂ : 0 ≤ b₀ * b₂) :
    PolynomialHyperbolic
      (C (a₀ * b₀) + C ((a₁ * b₁) / 2) * X + C (a₂ * b₂) * X ^ 2) := by
  apply polynomialHyperbolic_quadratic_of_discriminant (mul_ne_zero ha₂ hb₂)
  exact schurSzegoComposition_two_discriminant_nonneg ha hb hb₀₂

/- A polynomial-facing degree-`2` instance.  The hypotheses are stated in
coefficient form so that this theorem can be reused by later root-sign
bridges without hiding the exact discriminants being consumed. -/
theorem hermitePoulainSchurSzego_two_of_coeff_discriminants
    (p q : ℝ[X])
    (hpdeg : p.natDegree = 2) (hqdeg : q.natDegree = 2)
    (hpdisc : 0 ≤ p.coeff 1 ^ 2 - 4 * p.coeff 0 * p.coeff 2)
    (hqdisc : 0 ≤ q.coeff 1 ^ 2 - 4 * q.coeff 0 * q.coeff 2)
    (hqsign : 0 ≤ q.coeff 0 * q.coeff 2) :
    PolynomialHyperbolic (schurSzegoComposition 2 p q) := by
  rw [schurSzegoComposition_two]
  have hpne : p ≠ 0 := by
    intro hp0
    rw [hp0, Polynomial.natDegree_zero] at hpdeg
    omega
  have hqne : q ≠ 0 := by
    intro hq0
    rw [hq0, Polynomial.natDegree_zero] at hqdeg
    omega
  have hp₂ : p.coeff 2 ≠ 0 := by
    rw [← hpdeg, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hpne
  have hq₂ : q.coeff 2 ≠ 0 := by
    rw [← hqdeg, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hqne
  exact schurSzegoComposition_two_hyperbolic_of_discriminant
    hp₂ hq₂ hpdisc hqdisc hqsign

/-- The unnormalized coefficientwise operation is not a hyperbolicity
preserver.  This guards the convention correction: `X^2 - 1` composed with
itself gives `X^2 + 1`, which has the non-real root `I`. -/
theorem coefficientwiseComposition_not_hyperbolicity_preserver :
    ¬ (∀ (d : ℕ) (p q : ℝ[X]),
      p.natDegree = d → q.natDegree = d →
        PolynomialHyperbolic p → PolynomialHyperbolic q →
          PolynomialHyperbolic (coefficientwiseComposition d p q)) := by
  intro h
  have hp : PolynomialHyperbolic (X ^ 2 - 1 : ℝ[X]) := by
    intro z hz
    have hz' : z ^ 2 - 1 = 0 := by
      simpa [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
        Polynomial.map_one, Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_one] using hz
    have hz1 : z ^ 2 = 1 := sub_eq_zero.mp hz'
    rcases sq_eq_one_iff.mp hz1 with h | h
    · rw [h]
      simp
    · rw [h]
      simp
  have hdeg : (X ^ 2 - 1 : ℝ[X]).natDegree = 2 := by
    exact Polynomial.natDegree_X_pow_sub_C
  have hcomp := h 2 (X ^ 2 - 1) (X ^ 2 - 1) hdeg hdeg hp hp
  have hroot := hcomp Complex.I
  have hcoeff : coefficientwiseComposition 2 (X ^ 2 - 1) (X ^ 2 - 1) =
      X ^ 2 + 1 := by
    unfold coefficientwiseComposition
    norm_num [Finset.sum_range_succ, Finset.sum_range_zero,
      Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_one]
    ring_nf
  rw [hcoeff] at hroot
  have hzero : Polynomial.eval Complex.I
      ((X ^ 2 + 1 : ℝ[X]).map (algebraMap ℝ ℂ)) = 0 := by
    simp [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_one, Polynomial.eval_add, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_one, Complex.I_sq]
  have him := hroot hzero
  norm_num at him

/-- Even the binomial-normalized operation is not a hyperbolicity preserver
for two arbitrary real-rooted factors.  This is the same `X^2 - 1` witness;
the missing same-sign-root hypothesis is therefore mathematically necessary. -/
theorem unrestrictedSchurSzegoComposition_not_hyperbolicity_preserver :
    ¬ (∀ (d : ℕ) (p q : ℝ[X]),
      p.natDegree = d → q.natDegree = d →
        PolynomialHyperbolic p → PolynomialHyperbolic q →
          PolynomialHyperbolic (schurSzegoComposition d p q)) := by
  intro h
  have hp : PolynomialHyperbolic (X ^ 2 - 1 : ℝ[X]) := by
    intro z hz
    have hz' : z ^ 2 - 1 = 0 := by
      simpa [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
        Polynomial.map_one, Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_one] using hz
    have hz1 : z ^ 2 = 1 := sub_eq_zero.mp hz'
    rcases sq_eq_one_iff.mp hz1 with h | h
    · rw [h]
      simp
    · rw [h]
      simp
  have hdeg : (X ^ 2 - 1 : ℝ[X]).natDegree = 2 := by
    exact Polynomial.natDegree_X_pow_sub_C
  have hcomp := h 2 (X ^ 2 - 1) (X ^ 2 - 1) hdeg hdeg hp hp
  have hroot := hcomp Complex.I
  have hcoeff : schurSzegoComposition 2 (X ^ 2 - 1) (X ^ 2 - 1) =
      X ^ 2 + 1 := by
    unfold schurSzegoComposition
    norm_num [Finset.sum_range_succ, Finset.sum_range_zero,
      Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_one]
    ring_nf
  rw [hcoeff] at hroot
  have hzero : Polynomial.eval Complex.I
      ((X ^ 2 + 1 : ℝ[X]).map (algebraMap ℝ ℂ)) = 0 := by
    simp [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_one, Polynomial.eval_add, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_one, Complex.I_sq]
  have him := hroot hzero
  norm_num at him

/-- A nonzero real linear polynomial is hyperbolic in the repository's
root-set predicate. -/
theorem polynomialHyperbolic_C_add_C_mul_X {a b : ℝ} (hb : b ≠ 0) :
    PolynomialHyperbolic (C a + C b * X) := by
  intro z hz
  have hz' : (b : ℂ) * z + (a : ℂ) = 0 := by
    simpa only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_X, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, Complex.coe_algebraMap, add_comm] using hz
  have him := congrArg Complex.im hz'
  have hzero : b * z.im = 0 := by
    simpa [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im] using him
  rcases mul_eq_zero.mp hzero with h | h
  · exact absurd h hb
  · exact h

/-- The degree-`1` Schur--Szegő composition theorem.  This is a genuine
low-degree instance of the general target; higher degrees still require the
full Hermite--Poulain/Schur theorem. -/
theorem hermitePoulainSchurSzego_one
    (p q : ℝ[X]) (hpdeg : p.natDegree = 1) (hqdeg : q.natDegree = 1)
    (_hp : PolynomialHyperbolic p) (_hq : PolynomialHyperbolic q) :
    PolynomialHyperbolic (schurSzegoComposition 1 p q) := by
  rw [schurSzegoComposition_one]
  apply polynomialHyperbolic_C_add_C_mul_X
  have hpne : p ≠ 0 := by
    intro hp0
    rw [hp0, Polynomial.natDegree_zero] at hpdeg
    omega
  have hqne : q ≠ 0 := by
    intro hq0
    rw [hq0, Polynomial.natDegree_zero] at hqdeg
    omega
  have hp1 : p.coeff 1 ≠ 0 := by
    rw [← hpdeg, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hpne
  have hq1 : q.coeff 1 ≠ 0 := by
    rw [← hqdeg, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hqne
  rw [mul_ne_zero_iff]
  exact ⟨hp1, hq1⟩

/-- Composition with `(1 + X)^d` cancels the Schur--Szegő binomial normalization,
so it returns the ordinary coefficient polynomial. -/
theorem schurSzegoComposition_one_add_X_pow (d : ℕ) (p : ℝ[X]) :
    schurSzegoComposition d p ((1 + X) ^ d) =
      ∑ k ∈ Finset.range (d + 1), C (p.coeff k) * X ^ k := by
  unfold schurSzegoComposition
  apply Finset.sum_congr rfl
  intro k hk
  rw [Polynomial.coeff_one_add_X_pow]
  have hk_le : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hchoose : (Nat.choose d k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hk_le))
  have hterm : p.coeff k * (Nat.choose d k : ℝ) /
      (Nat.choose d k : ℝ) = p.coeff k := by
    field_simp
  rw [hterm]

/-- The Jensen factor `(1 + X)^d` has all real roots on the nonpositive
half-line, including the vacuous degree-zero case. -/
theorem polynomialRootsSameSign_one_add_X_pow (d : ℕ) :
    PolynomialRootsSameSign ((1 + X) ^ d : ℝ[X]) := by
  left
  intro x hx
  by_cases hd : d = 0
  · subst hd
    simp at hx
  · change Polynomial.eval x ((1 + X : ℝ[X]) ^ d) = 0 at hx
    have hpow : (Polynomial.eval x (1 + X : ℝ[X])) ^ d = 0 := by
      simpa [Polynomial.eval_pow] using hx
    have hbase : Polynomial.eval x (1 + X : ℝ[X]) = 0 :=
      (pow_eq_zero_iff hd).mp hpow
    have hlinear : (1 : ℝ) + x = 0 := by
      simpa [Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_X] using hbase
    linarith

/-- A coefficient-function form of the Jensen polynomial. -/
def jensenCoeffPoly (d n : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (d + 1),
    C ((Nat.choose d k : ℝ) * XiCoeff (n + k)) * X ^ k

theorem jensenCoeffPoly_coeff (d n k : ℕ) (hk : k ≤ d) :
    (jensenCoeffPoly d n).coeff k =
      (Nat.choose d k : ℝ) * XiCoeff (n + k) := by
  classical
  unfold jensenCoeffPoly
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range.mpr (Nat.lt_succ_of_le hk)]

/-- The repository's `JensenPoly` is exactly the Schur--Szegő binomial
composition of its coefficient-function polynomial with `(1+X)^d`. -/
theorem JensenPoly_eq_schurSzego_one_add_X_pow (d n : ℕ) :
    JensenPoly d n =
      schurSzegoComposition d (jensenCoeffPoly d n) ((1 + X) ^ d) := by
  unfold JensenPoly
  rw [schurSzegoComposition_one_add_X_pow]
  apply Finset.sum_congr rfl
  intro k hk
  have hk_le : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [jensenCoeffPoly_coeff d n k hk_le]

/- The existing Turán proof now transports through the corrected composition
identity for the concrete Jensen row. -/
theorem jensenPoly_two_hyperbolic_as_schurSzego
    (n : ℕ) (h2 : XiCoeff (n + 2) ≠ 0) (hT : XiTuran2 n) :
    PolynomialHyperbolic
      (schurSzegoComposition 2 (jensenCoeffPoly 2 n) ((1 + X) ^ 2)) := by
  rw [← JensenPoly_eq_schurSzego_one_add_X_pow]
  exact jensenPoly_two_hyperbolic_of_turan n h2 hT

end Reinmann
