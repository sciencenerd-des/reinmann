/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.ToeplitzComplement
import Reinmann.FiniteProductSplitPair

/-! The sign-free Jacobi identity for F(z) and 1/F(-z). -/
noncomputable section
namespace Reinmann.ToeplitzComplement
open Matrix Finset
variable {R : Type*} [CommRing R]

private theorem neg_pow_twice (n : ℕ) : (-1 : R)^n * (-1 : R)^n = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]
  simp

/-- Rescaling z to -z contributes exactly the rectangle-area sign. -/
theorem minor_rescale_neg (f : PowerSeries R) (size shift : ℕ) :
    minor (PowerSeries.rescale (-1) f) size shift =
      (-1 : R)^(shift*size) * minor f size shift := by
  classical
  have he : (fun i j : Fin size => entry (PowerSeries.rescale (-1) f) (shift+i.val) j.val) =
      fun i j : Fin size => (-1 : R)^(shift+i.val) *
        ((-1 : R)^j.val * entry f (shift+i.val) j.val) := by
    funext i j
    by_cases h : j.val ≤ shift+i.val
    · simp only [entry, if_pos h, PowerSeries.coeff_rescale]
      have hx : shift+i.val = (shift+i.val-j.val)+j.val := by omega
      conv_rhs => rw [hx, pow_add]
      rw [mul_assoc, ← mul_assoc ((-1 : R)^j.val), neg_pow_twice, one_mul]
      simp only [Nat.add_sub_cancel]
    · simp [entry, h]
  unfold minor
  rw [he]
  have hcol := det_mul_column (fun i : Fin size => (-1 : R)^(shift+i.val))
    (fun i j : Fin size => (-1 : R)^j.val * entry f (shift+i.val) j.val)
  have hrow := det_mul_row (fun j : Fin size => (-1 : R)^j.val)
    (fun i j : Fin size => entry f (shift+i.val) j.val)
  change (Matrix.det (fun i j : Fin size => (-1 : R)^(shift+i.val) *
    ((-1 : R)^j.val * entry f (shift+i.val) j.val))) =
    (∏ i : Fin size, (-1 : R)^(shift+i.val)) *
      Matrix.det (fun i j : Fin size => (-1 : R)^j.val * entry f (shift+i.val) j.val) at hcol
  change (Matrix.det (fun i j : Fin size => (-1 : R)^j.val * entry f (shift+i.val) j.val)) =
    (∏ i : Fin size, (-1 : R)^i.val) *
      Matrix.det (fun i j : Fin size => entry f (shift+i.val) j.val) at hrow
  rw [hcol, hrow, ← mul_assoc, ← prod_mul_distrib]
  have hp : (∏ i : Fin size, (-1 : R)^(shift+i.val) * (-1 : R)^i.val) =
      (-1 : R)^(shift*size) := by
    simp only [pow_add, mul_assoc, neg_pow_twice, mul_one, prod_const, card_univ,
      Fintype.card_fin, ← pow_mul]
  rw [hp]

/-- The s by s reciprocal minor equals the r by r original minor, with sizes
and shifts interchanged. This is an equality, not an equality up to sign. -/
theorem complementary_minor_signed {f g : PowerSeries R}
    (hfg : PowerSeries.rescale (-1) f * g = 1) (hf : PowerSeries.coeff 0 f = 1)
    (s r : ℕ) : minor g s r = minor f r s := by
  have h0 : PowerSeries.coeff 0 (PowerSeries.rescale (-1) f) = 1 := by simp [hf]
  have h := complementary_minor hfg h0 s r
  rw [minor_rescale_neg] at h
  have hc := congrArg (fun z => (-1 : R)^(s*r)*z) h
  simpa only [← mul_assoc, neg_pow_twice, one_mul] using hc.symm

/-- The finite-product theorem now concerns the original product coefficients
as well as the reciprocal complementary determinant. -/
theorem finite_product_original_minor_eq {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (s r : ℕ) :
    FiniteProductSplitPair.rankMinor a s r =
      minor (PowerSeries.rescale (-1) (SplitPairCoefficients.product a : PowerSeries ℂ)) r s := by
  have hf : PowerSeries.coeff 0 (SplitPairCoefficients.product a : PowerSeries ℂ) = 1 := by
    rw [Polynomial.coeff_coe]
    rw [Polynomial.coeff_zero_eq_eval_zero]
    simp [SplitPairCoefficients.product, SplitPairCoefficients.factor, Polynomial.eval_prod]
  have hres : PowerSeries.rescale (-1 : ℂ)
      (PowerSeries.rescale (-1) (SplitPairCoefficients.product a : PowerSeries ℂ)) =
      (SplitPairCoefficients.product a : PowerSeries ℂ) := by
    ext n
    simp only [PowerSeries.coeff_rescale, ← mul_assoc, neg_pow_twice, one_mul]
  have hfg : PowerSeries.rescale (-1 : ℂ)
      (PowerSeries.rescale (-1) (SplitPairCoefficients.product a : PowerSeries ℂ)) *
      (SplitPairCoefficients.product a : PowerSeries ℂ)⁻¹ = 1 := by
    rw [hres]
    exact PowerSeries.mul_inv_cancel _ (by
      simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using
        (show PowerSeries.coeff 0 (SplitPairCoefficients.product a : PowerSeries ℂ) ≠ 0 by
          rw [hf]; norm_num))
  exact complementary_minor_signed hfg (by simp [hf]) s r

/-- The geometric root-order hypotheses force both signs among the original
coefficient minors, not just the much smaller reciprocal determinants. -/
theorem finite_product_original_both_signs {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] {a : ι → ℂ} (ha : Function.Injective a) (hz : ∀ i, a i ≠ 0)
    (σ : ι ≃ ι) (hconj : ∀ i, a (σ i) = star (a i))
    (J : Finset ι) (p q : ι) (hp : p ∉ J) (hq : q ∉ J) (hpq : p ≠ q)
    (hσp : σ p = q) (hJ : J.image σ = J)
    (hphase : ((a p)⁻¹).im ≠ 0) {P : ℝ} (hP : 0 < P)
    (hproduct : (∏ i ∈ J, (a i)⁻¹) = (P : ℂ))
    (hinner : ∀ i ∈ J, ‖(a p)⁻¹‖ < ‖(a i)⁻¹‖)
    (houter : ∀ i ∉ insert p (insert q J), ‖(a i)⁻¹‖ < ‖(a p)⁻¹‖) :
    let F := PowerSeries.rescale (-1) (SplitPairCoefficients.product a : PowerSeries ℂ)
    (∀ M, ∃ r ≥ M, (minor F r (J.card+1)).re < 0) ∧
    (∀ M, ∃ r ≥ M, 0 < (minor F r (J.card+1)).re) := by
  simpa only [finite_product_original_minor_eq] using
    FiniteProductSplitPair.finite_product_split_pair_of_root_order
      ha hz σ hconj J p q hp hq hpq hσp hJ hphase hP hproduct hinner houter

end Reinmann.ToeplitzComplement
