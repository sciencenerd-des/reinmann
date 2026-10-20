/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.GenusZeroProductLimits
import Reinmann.PolynomialSectorPF

/-! Construct real polynomial approximants to a conjugation-stable genus-zero
product. Indexed repetitions and fixed points of conjugation are retained.
This does not identify folded Xi with such a product. -/
noncomputable section
namespace Reinmann.RealGenusZeroApproximants
open Finset Filter Polynomial
open scoped Topology

def closure {ι : Type*} (sigma : ι → ι) (s : Finset ι) : Finset ι := by
  classical
  exact s ∪ s.image sigma

theorem subset_closure {ι : Type*} (sigma : ι → ι) (s : Finset ι) :
    s ⊆ closure sigma s := by
  classical
  exact Finset.subset_union_left

open Classical in
theorem image_closure {ι : Type*} {sigma : ι → ι}
    (hsigma : Function.Involutive sigma)
    (s : Finset ι) : (closure sigma s).image sigma = closure sigma s := by
  classical
  simp [closure, Finset.image_union, Finset.image_image,
    hsigma, Finset.union_comm]

/-- Closing finite sets under the index involution is cofinal. -/
theorem closure_tendsto {ι : Type*} (sigma : ι → ι) :
    Tendsto (closure sigma) atTop atTop := by
  refine tendsto_atTop.2 (fun s => eventually_atTop.2 ⟨s, ?_⟩)
  intro t hst
  exact hst.trans (subset_closure sigma t)

def complexPartial {ι : Type*} (a : ι → ℂ) (s : Finset ι) : Polynomial ℂ :=
  ∏ i ∈ s, (1 - C (a i)⁻¹ * X)

/-- Coefficientwise real-part extraction is only a construction, not a ring
homomorphism. The map-back identity below requires conjugation invariance. -/
def realPart (p : Polynomial ℂ) : Polynomial ℝ :=
  Polynomial.ofFinsupp (p.toFinsupp.mapRange Complex.re (by rfl))

theorem realPart_coeff (p : Polynomial ℂ) (n : ℕ) :
    (realPart p).coeff n = (p.coeff n).re := rfl

theorem map_realPart {p : Polynomial ℂ}
    (hp : p.map (starRingEnd ℂ) = p) : (realPart p).map (algebraMap ℝ ℂ) = p := by
  ext n
  simp only [Polynomial.coeff_map, realPart_coeff]
  have hc := congrArg (fun q : Polynomial ℂ => q.coeff n) hp
  simp only [Polynomial.coeff_map] at hc
  have him : (p.coeff n).im = 0 := Complex.conj_eq_iff_im.mp hc
  apply Complex.ext <;> simp [him]

theorem complexPartial_conj {ι : Type*} {sigma : ι → ι}
    (hsigma : Function.Involutive sigma) {a : ι → ℂ}
    (hconj : ∀ i, a (sigma i) = star (a i)) (s : Finset ι) :
    (complexPartial a (closure sigma s)).map (starRingEnd ℂ) =
      complexPartial a (closure sigma s) := by
  classical
  have hf (i : ι) : (1 - C (a i)⁻¹ * X : Polynomial ℂ).map (starRingEnd ℂ) =
      1 - C (a (sigma i))⁻¹ * X := by
    simp [hconj]
  simp only [complexPartial, Polynomial.map_prod, hf]
  have hprod := Finset.prod_image (s := closure sigma s)
    (f := fun i => (1 - C (a i)⁻¹ * X : Polynomial ℂ))
    (g := sigma) hsigma.injective.injOn
  rw [image_closure hsigma s] at hprod
  exact hprod.symm

def realPartial {ι : Type*} (sigma : ι → ι) (a : ι → ℂ) (s : Finset ι) :
    Polynomial ℝ := realPart (complexPartial a (closure sigma s))

/-- These are actual real polynomials whose complexification is the closed
finite product, including each indexed multiplicity exactly once. -/
theorem map_realPartial {ι : Type*} {sigma : ι → ι}
    (hsigma : Function.Involutive sigma) {a : ι → ℂ}
    (hconj : ∀ i, a (sigma i) = star (a i)) (s : Finset ι) :
    (realPartial sigma a s).map (algebraMap ℝ ℂ) =
      complexPartial a (closure sigma s) :=
  map_realPart (complexPartial_conj hsigma hconj s)

theorem realPartial_zero {ι : Type*} (sigma : ι → ι) (a : ι → ℂ) (s : Finset ι) :
    (realPartial sigma a s).coeff 0 = 1 := by
  simp only [realPartial, realPart_coeff, complexPartial, Polynomial.coeff_zero_prod]
  simp [Polynomial.coeff_sub, Polynomial.coeff_one]

/-- Complex evaluation of the real approximant is exactly its finite linear
product; coefficientwise real-part extraction has introduced no new zeros. -/
theorem eval_realPartial {ι : Type*} {sigma : ι → ι}
    (hsigma : Function.Involutive sigma) {a : ι → ℂ}
    (hconj : ∀ i, a (sigma i) = star (a i)) (s : Finset ι) (z : ℂ) :
    ((realPartial sigma a s).map (algebraMap ℝ ℂ)).eval z =
      ∏ i ∈ closure sigma s, (1 - (a i)⁻¹ * z) := by
  rw [map_realPartial hsigma hconj s]
  simp only [complexPartial, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]

/-- Each approximant inherits the sector bound from its actual indexed zeros.
This is not an extra positivity hypothesis on the approximants. -/
theorem realPartial_finitePF {ι : Type*} {sigma : ι → ι}
    (hsigma : Function.Involutive sigma) {a : ι → ℂ}
    (hconj : ∀ i, a (sigma i) = star (a i)) (ha : ∀ i, a i ≠ 0)
    {r : ℕ} (hsector : ∀ i, Real.pi - Real.pi / ((r : ℝ) + 1) ≤ |Complex.arg (a i)|)
    (s : Finset ι) : FinitePF (fun n => (realPartial sigma a s).coeff n) r := by
  classical
  apply PolynomialSectorPF.finitePF_of_zero_sector (by rw [realPartial_zero]; norm_num)
  intro z hz
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
    eval_realPartial hsigma hconj s z] at hz
  obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hz
  have he : a i = z := by
    have h := congrArg (fun w : ℂ => a i * w) hi
    have hsub : a i - z = 0 := by
      simpa only [mul_sub, mul_one, ← mul_assoc, mul_inv_cancel₀ (ha i),
        one_mul, mul_zero] using h
    exact sub_eq_zero.mp hsub
  rw [← he]
  exact hsector i

/-- The constructed real polynomial net converges locally uniformly to the
whole genus-zero product. Involution closure is cofinal, not a subsequence
assumed to converge. -/
theorem realPartial_locallyUniformly {ι : Type*} {sigma : ι → ι}
    (hsigma : Function.Involutive sigma) {a : ι → ℂ}
    (hconj : ∀ i, a (sigma i) = star (a i))
    (hsum : Summable (fun i => ‖(a i)⁻¹‖)) :
    TendstoLocallyUniformlyOn
      (fun s z => ((realPartial sigma a s).map (algebraMap ℝ ℂ)).eval z)
      (fun z => ∏' i, (1 - (a i)⁻¹ * z)) atTop Set.univ := by
  have hp : TendstoLocallyUniformlyOn
      (fun s z => ∏ i ∈ s, (1 - (a i)⁻¹ * z))
      (fun z => ∏' i, (1 - (a i)⁻¹ * z)) atTop Set.univ := by
    have hsum' : Summable (fun i => ‖-(a i)⁻¹‖) := by simpa only [norm_neg] using hsum
    simpa only [neg_mul, sub_eq_add_neg] using
      GenusZeroProductLimits.linearProduct_locallyUniformly hsum'
  intro v hv z hz
  obtain ⟨t, ht, h⟩ := hp v hv z hz
  refine ⟨t, ht, ?_⟩
  have he := (closure_tendsto sigma).eventually h
  filter_upwards [he] with s hs y hy
  simpa only [eval_realPartial hsigma hconj s y] using hs y hy

/-- Sector sufficiency for an actual conjugation-stable genus-zero product.
All finite approximants, their real coefficients and their positivity are
constructed internally. Repetitions, fixed points and modulus ties are allowed. -/
theorem finitePF_genusZero_product {ι : Type*} {sigma : ι → ι}
    (hsigma : Function.Involutive sigma) {a : ι → ℂ}
    (hconj : ∀ i, a (sigma i) = star (a i)) (ha : ∀ i, a i ≠ 0)
    (hsum : Summable (fun i => ‖(a i)⁻¹‖)) {r : ℕ}
    (hsector : ∀ i, Real.pi - Real.pi / ((r : ℝ) + 1) ≤ |Complex.arg (a i)|) :
    FinitePF (fun n => (iteratedDeriv n (fun z => ∏' i, (1 - (a i)⁻¹ * z)) 0 /
      (n.factorial : ℂ)).re) r := by
  apply FinitePFAnalyticLimits.finitePF_of_polynomial_locallyUniformly
    (realPartial_locallyUniformly hsigma hconj hsum) isOpen_univ (Set.mem_univ 0)
  exact Filter.Eventually.of_forall (realPartial_finitePF hsigma hconj ha hsector)

/-- The product's ordinary Taylor coefficients really are real. The real-part
projection in the PF statement is therefore an identification, not a change
of the complex coefficient sequence. -/
theorem product_ordinaryCoeff_im_zero {ι : Type*} {sigma : ι → ι}
    (hsigma : Function.Involutive sigma) {a : ι → ℂ}
    (hconj : ∀ i, a (sigma i) = star (a i))
    (hsum : Summable (fun i => ‖(a i)⁻¹‖)) (n : ℕ) :
    (iteratedDeriv n (fun z => ∏' i, (1 - (a i)⁻¹ * z)) 0 /
      (n.factorial : ℂ)).im = 0 := by
  have hc := polynomial_coeff_tendsto_of_locallyUniformLimit
    (realPartial_locallyUniformly hsigma hconj hsum) n
  have hi := (Complex.continuous_im.tendsto _).comp hc
  have hzero : Tendsto (fun _ : Finset ι => (0 : ℝ)) atTop
      (𝓝 ((iteratedDeriv n (fun z => ∏' i, (1 - (a i)⁻¹ * z)) 0 /
        (n.factorial : ℂ)).im)) := by
    simpa only [Polynomial.coeff_map, RCLike.algebraMap_eq_ofReal,
      Complex.ofReal_im, Function.comp_apply] using hi
  exact tendsto_nhds_unique hzero tendsto_const_nhds

/-- End-to-end transfer from an explicit genus-zero product identity to a
given ordinary real coefficient sequence. The identity, inverse-zero
summability and conjugation indexing remain actual mathematical inputs. -/
theorem finitePF_of_product_identity {ι : Type*} {sigma : ι → ι}
    (hsigma : Function.Involutive sigma) {a : ι → ℂ}
    (hconj : ∀ i, a (sigma i) = star (a i)) (ha : ∀ i, a i ≠ 0)
    (hsum : Summable (fun i => ‖(a i)⁻¹‖)) {r : ℕ}
    (hsector : ∀ i, Real.pi - Real.pi / ((r : ℝ) + 1) ≤ |Complex.arg (a i)|)
    {C : ℝ} (hC : 0 ≤ C) {f : ℂ → ℂ} {b : ℕ → ℝ}
    (hidentity : ∀ z, f z = (C : ℂ) * ∏' i, (1 - (a i)⁻¹ * z))
    (hcoeff : ∀ n, iteratedDeriv n f 0 / (n.factorial : ℂ) = (b n : ℂ)) :
    FinitePF b r := by
  have h := finitePF_nonneg_scale
    (finitePF_genusZero_product hsigma hconj ha hsum hsector) hC
  have hb (n : ℕ) : b n = C *
      (iteratedDeriv n (fun z => ∏' i, (1 - (a i)⁻¹ * z)) 0 /
        (n.factorial : ℂ)).re := by
    have hc := hcoeff n
    rw [funext hidentity, iteratedDeriv_const_mul_field, mul_div_assoc] at hc
    have hre := congrArg Complex.re hc
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] using hre.symm
  simpa only [← hb] using h

end Reinmann.RealGenusZeroApproximants
