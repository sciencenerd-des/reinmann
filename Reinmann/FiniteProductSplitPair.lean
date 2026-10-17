/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.SplitPairCoefficients
import Reinmann.SplitPairDeterminant
import Reinmann.SplitPairOscillation
import Reinmann.SplitPairModulusOrder

/-!
# Finite-product split-pair oscillation

The hypotheses describe actual roots, their conjugation permutation, and strict
finite subset-product modulus gaps. The reciprocal coefficients, determinant
expansion, nonzero leading constant and decaying tail are all proved here.
No two-term asymptotic or sign-change conclusion is a hypothesis.
-/
noncomputable section
namespace Reinmann.FiniteProductSplitPair
open Finset Matrix
open SplitPairCoefficients SplitPairDeterminant SplitPairOscillation
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The complementary Toeplitz minor at paper rank r=n+s−1. -/
def minor (a : ι → ℂ) (s n : ℕ) : ℂ :=
  Matrix.det (fun i j : Fin s => PowerSeries.coeff (n+i.val+(s-1-j.val))
    ((SplitPairCoefficients.product a : PowerSeries ℂ))⁻¹)

/-- The original rank convention, including zero for negative coefficient indices. -/
def rankMinor (a : ι → ℂ) (s r : ℕ) : ℂ :=
  Matrix.det (fun i j : Fin s => if j.val ≤ r+i.val then
    PowerSeries.coeff (r+i.val-j.val) ((SplitPairCoefficients.product a : PowerSeries ℂ))⁻¹
    else 0)

omit [DecidableEq ι] [Nonempty ι] in
theorem minor_eq_rankMinor (a : ι → ℂ) (s n : ℕ) :
    minor a s n = rankMinor a s (n+(s-1)) := by
  unfold minor rankMinor
  congr 1
  funext i j
  have hidx : n+i.val+(s-1-j.val) = n+(s-1)+i.val-j.val := by
    have hj := j.isLt
    omega
  rw [if_pos (show j.val ≤ n+(s-1)+i.val by have hj := j.isLt; omega), hidx]

/-- Actual inverse coefficients supply the complementary-moment matrix. -/
theorem minor_eq_moment {a : ι → ℂ} (ha : Function.Injective a)
    (hz : ∀ i, a i ≠ 0) (s n : ℕ) :
    minor a s n = (momentMatrix (residue a) (fun i => (a i)⁻¹) s n).det := by
  unfold minor
  congr 1
  funext i j
  rw [reciprocal_coefficient ha hz]
  rfl

/-- The computed leading coefficient, not an asymptotic input. -/
def leading (a : ι → ℂ) (s : ℕ) (S : Finset ι) : ℂ :=
  coefficient (residue a) (fun i => (a i)⁻¹) s S

def base (a : ι → ℂ) (S : Finset ι) : ℂ := ∏ i ∈ S, (a i)⁻¹

omit [Nonempty ι] in
theorem leading_ne_zero {a : ι → ℂ} (ha : Function.Injective a)
    (hz : ∀ i, a i ≠ 0) (s : ℕ) {S : Finset ι} (hS : S.card = s) :
    leading a s S ≠ 0 :=
  coefficient_ne_zero (inv_injective.comp ha) (residue_ne_zero ha hz) s hS

omit [Fintype ι] [Nonempty ι] in
theorem base_conjugate {a : ι → ℂ} (σ : ι ≃ ι)
    (ha : ∀ i, a (σ i) = star (a i)) (S : Finset ι) :
    base a (S.image σ) = star (base a S) := by
  unfold base
  rw [prod_image σ.injective.injOn]
  change _ = (starRingEnd ℂ) (∏ i ∈ S, (a i)⁻¹)
  simp [ha, map_prod, map_inv₀]

omit [Nonempty ι] in
theorem leading_conjugate {a : ι → ℂ} (σ : ι ≃ ι)
    (ha : ∀ i, a (σ i) = star (a i)) (s : ℕ) (S : Finset ι) :
    leading a s (S.image σ) = star (leading a s S) := by
  apply coefficient_conjugate σ (residue_conjugate σ ha)
  intro i
  simp [ha i]

/-- Exact finite-product expansion into subset bases. -/
theorem minor_subset_expansion {a : ι → ℂ} (ha : Function.Injective a)
    (hz : ∀ i, a i ≠ 0) (s n : ℕ) :
    minor a s n = ∑ T ∈ (univ : Finset ι).powersetCard s,
      leading a s T * base a T ^ n := by
  rw [minor_eq_moment ha hz, subset_expansion]
  rfl

/-- A finite product with one conjugate dominant subset pair has both signs at
unbounded actual Toeplitz ranks. All other normalized bases have norm below1.
The subset-product inequalities are finite root-modulus conditions, not an
assumed determinant asymptotic. -/
theorem finite_product_split_pair {a : ι → ℂ} (ha : Function.Injective a)
    (hz : ∀ i, a i ≠ 0) (σ : ι ≃ ι) (hconj : ∀ i, a (σ i) = star (a i))
    (s : ℕ) (S : Finset ι) (hS : S.card = s)
    (hpair : S ≠ S.image σ) (hangle : (base a S).im ≠ 0)
    (hgap : ∀ T ∈ (univ : Finset ι).powersetCard s,
      T ≠ S → T ≠ S.image σ → ‖base a T‖ < ‖base a S‖) :
    (∀ M, ∃ r ≥ M, (rankMinor a s r).re < 0) ∧
    (∀ M, ∃ r ≥ M, 0 < (rankMinor a s r).re) := by
  classical
  let P := (univ : Finset ι).powersetCard s
  let T := S.image σ
  let R : ℝ := ‖base a S‖
  let u : ℂ := base a S / (R : ℂ)
  let K : ℂ := leading a s S
  let rest : Finset (Finset ι) := (P.erase S).erase T
  let c : rest → ℂ := fun U => leading a s U.val
  let v : rest → ℂ := fun U => base a U.val / (R : ℂ)
  have hR : 0 < R := norm_pos_iff.mpr (fun h => hangle (by rw [h]; rfl))
  have hRcomplex : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  have hu : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, div_self hR.ne']
  have huim : u.im ≠ 0 := by
    dsimp [u]
    rw [Complex.div_ofReal_im]
    exact div_ne_zero hangle hR.ne'
  have hne : u ≠ 1 := fun h => huim (by simp [h])
  have hne2 : u ^ 2 ≠ 1 := by
    intro h
    rcases (sq_eq_one_iff).mp h with h | h
    · exact hne h
    · exact huim (by simp [h])
  have hK : K ≠ 0 := leading_ne_zero ha hz s hS
  have hSmem : S ∈ P := mem_powersetCard.mpr ⟨subset_univ _, hS⟩
  have hTmem : T ∈ P := by
    apply mem_powersetCard.mpr
    exact ⟨subset_univ _, by simpa [T, card_image_of_injective _ σ.injective] using hS⟩
  have hTne : T ≠ S := Ne.symm hpair
  have hv (U : rest) : ‖v U‖ < 1 := by
    dsimp [v]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    apply (div_lt_one hR).mpr
    have hr := mem_erase.mp U.property
    have hs := mem_erase.mp hr.2
    exact hgap U.val hs.2 hs.1 hr.1
  have hbaseT : base a T / (R : ℂ) = star u := by
    rw [base_conjugate σ hconj]
    change star (base a S) / (R : ℂ) = star (base a S / (R : ℂ))
    simp [star_div₀]
  have hleadT : leading a s T = star K := leading_conjugate σ hconj s S
  have hnorm (n : ℕ) : minor a s n / (R : ℂ) ^ n =
      K * u ^ n + star K * (star u) ^ n + ∑ U : rest, c U * v U ^ n := by
    rw [minor_subset_expansion ha hz]
    have hdiv : (∑ U ∈ P, leading a s U * base a U ^ n) / (R : ℂ) ^ n =
        ∑ U ∈ P, leading a s U * base a U ^ n / (R : ℂ) ^ n := by
      simp only [div_eq_mul_inv, Finset.sum_mul]
    rw [hdiv]
    have hterm (U : Finset ι) : leading a s U * base a U ^ n / (R : ℂ) ^ n =
        leading a s U * (base a U / (R : ℂ)) ^ n := by
      rw [div_pow, mul_div_assoc]
    simp_rw [hterm]
    rw [← add_sum_erase _ _ hSmem,
      ← add_sum_erase _ _ (mem_erase.mpr ⟨hTne, hTmem⟩)]
    rw [hleadT, hbaseT]
    change K * u ^ n + (star K * star u ^ n + ∑ U ∈ rest, leading a s U * (base a U / ↑R) ^ n) = _
    rw [← Finset.sum_coe_sort rest (fun U => leading a s U * (base a U / ↑R) ^ n)]
    exact (add_assoc _ _ _).symm
  have hosc := finite_split_sum_both_signs hK hu hne hne2 c v hv
  have hnegative (M : ℕ) : ∃ n ≥ M, (minor a s n).re < 0 := by
    obtain ⟨n, hn, hsign⟩ := hosc.1 M
    refine ⟨n, hn, ?_⟩
    rw [← hnorm n] at hsign
    have hs : (minor a s n).re / R ^ n < 0 := by
      simpa only [← Complex.ofReal_pow, Complex.div_ofReal_re] using hsign
    simpa using (div_lt_iff₀ (pow_pos hR n)).mp hs
  have hpositive (M : ℕ) : ∃ n ≥ M, 0 < (minor a s n).re := by
    obtain ⟨n, hn, hsign⟩ := hosc.2 M
    refine ⟨n, hn, ?_⟩
    rw [← hnorm n] at hsign
    have hs : 0 < (minor a s n).re / R ^ n := by
      simpa only [← Complex.ofReal_pow, Complex.div_ofReal_re] using hsign
    simpa using (lt_div_iff₀ (pow_pos hR n)).mp hs
  constructor
  · intro M
    obtain ⟨n, hn, hs⟩ := hnegative M
    exact ⟨n+(s-1), by omega, by rwa [← minor_eq_rankMinor]⟩
  · intro M
    obtain ⟨n, hn, hs⟩ := hpositive M
    exact ⟨n+(s-1), by omega, by rwa [← minor_eq_rankMinor]⟩

/-- A proved exponentially small remainder for the actual finite-product
minor, with computed nonzero leading coefficient. -/
theorem exponential_remainder_bound {a : ι → ℂ} (ha : Function.Injective a)
    (hz : ∀ i, a i ≠ 0) (σ : ι ≃ ι) (hconj : ∀ i, a (σ i) = star (a i))
    (s : ℕ) (S : Finset ι) (hS : S.card = s)
    (hpair : S ≠ S.image σ) (hangle : (base a S).im ≠ 0)
    (hgap : ∀ T ∈ (univ : Finset ι).powersetCard s,
      T ≠ S → T ≠ S.image σ → ‖base a T‖ < ‖base a S‖) :
    leading a s S ≠ 0 ∧ ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ∃ A : ℝ, 0 ≤ A ∧ ∀ n : ℕ,
      ‖minor a s n / (‖base a S‖ : ℂ) ^ n -
        (leading a s S * (base a S / (‖base a S‖ : ℂ)) ^ n +
          star (leading a s S) * (star (base a S / (‖base a S‖ : ℂ))) ^ n)‖ ≤ A * ρ ^ n := by
  classical
  let P := (univ : Finset ι).powersetCard s
  let T := S.image σ
  let R : ℝ := ‖base a S‖
  let u : ℂ := base a S / (R : ℂ)
  let K : ℂ := leading a s S
  let rest : Finset (Finset ι) := (P.erase S).erase T
  let c : rest → ℂ := fun U => leading a s U.val
  let v : rest → ℂ := fun U => base a U.val / (R : ℂ)
  have hR : 0 < R := norm_pos_iff.mpr (fun h => hangle (by rw [h]; rfl))
  have hK : K ≠ 0 := leading_ne_zero ha hz s hS
  have hSmem : S ∈ P := mem_powersetCard.mpr ⟨subset_univ _, hS⟩
  have hTmem : T ∈ P := by
    apply mem_powersetCard.mpr
    exact ⟨subset_univ _, by simpa [T, card_image_of_injective _ σ.injective] using hS⟩
  have hTne : T ≠ S := Ne.symm hpair
  have hv (U : rest) : ‖v U‖ < 1 := by
    dsimp [v]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    apply (div_lt_one hR).mpr
    have hr := mem_erase.mp U.property
    have hs := mem_erase.mp hr.2
    exact hgap U.val hs.2 hs.1 hr.1
  have hbaseT : base a T / (R : ℂ) = star u := by
    rw [base_conjugate σ hconj]
    change star (base a S) / (R : ℂ) = star (base a S / (R : ℂ))
    simp [star_div₀]
  have hleadT : leading a s T = star K := leading_conjugate σ hconj s S
  have hnorm (n : ℕ) : minor a s n / (R : ℂ) ^ n =
      K * u ^ n + star K * (star u) ^ n + ∑ U : rest, c U * v U ^ n := by
    rw [minor_subset_expansion ha hz]
    have hdiv : (∑ U ∈ P, leading a s U * base a U ^ n) / (R : ℂ) ^ n =
        ∑ U ∈ P, leading a s U * base a U ^ n / (R : ℂ) ^ n := by
      simp only [div_eq_mul_inv, Finset.sum_mul]
    rw [hdiv]
    have hterm (U : Finset ι) : leading a s U * base a U ^ n / (R : ℂ) ^ n =
        leading a s U * (base a U / (R : ℂ)) ^ n := by
      rw [div_pow, mul_div_assoc]
    simp_rw [hterm]
    rw [← add_sum_erase _ _ hSmem,
      ← add_sum_erase _ _ (mem_erase.mpr ⟨hTne, hTmem⟩)]
    rw [hleadT, hbaseT]
    change K * u ^ n + (star K * star u ^ n + ∑ U ∈ rest, leading a s U * (base a U / ↑R) ^ n) = _
    rw [← Finset.sum_coe_sort rest (fun U => leading a s U * (base a U / ↑R) ^ n)]
    exact (add_assoc _ _ _).symm
  obtain ⟨ρ, hρpos, hρlt, hrate⟩ := exists_geometric_rate v hv
  let A : ℝ := ∑ U : rest, ‖c U‖
  refine ⟨hK, ρ, hρpos, hρlt, A, Finset.sum_nonneg (fun U _ => norm_nonneg _), ?_⟩
  intro n
  change ‖minor a s n / (R : ℂ) ^ n - (K * u ^ n + star K * star u ^ n)‖ ≤ A * ρ ^ n
  rw [hnorm n, add_sub_cancel_left]
  exact norm_finite_geometric_tail_le c v hρpos.le hrate n

omit [DecidableEq ι] in
/-- Reality is proved from the root conjugation permutation. Thus the real-part
sign conclusions above are signs of real determinants, not a projection test. -/
theorem minor_im_eq_zero {a : ι → ℂ} (ha : Function.Injective a)
    (hz : ∀ i, a i ≠ 0) (σ : ι ≃ ι) (hconj : ∀ i, a (σ i) = star (a i))
    (s n : ℕ) : (minor a s n).im = 0 := by
  classical
  rw [minor_eq_moment ha hz]
  apply moment_im_eq_zero σ (residue_conjugate σ hconj)
  intro i
  simp [hconj i]

/-- Root-by-root boundary ordering implies the finite subset-product gaps. -/
theorem finite_product_split_pair_of_boundary {a : ι → ℂ} (ha : Function.Injective a)
    (hz : ∀ i, a i ≠ 0) (σ : ι ≃ ι) (hconj : ∀ i, a (σ i) = star (a i))
    (s : ℕ) (S : Finset ι) (hS : S.card = s) (p q : ι) (hp : p ∈ S) (hq : q ∉ S)
    (hswap : S.image σ = insert q (S.erase p)) (hangle : (base a S).im ≠ 0)
    (hmax : ∀ x ∈ S, ∀ y ∉ S, ‖(a y)⁻¹‖ ≤ ‖(a x)⁻¹‖)
    (hequal : ∀ x ∈ S, ∀ y ∉ S, ‖(a y)⁻¹‖ = ‖(a x)⁻¹‖ → x = p ∧ y = q) :
    (∀ M, ∃ r ≥ M, (rankMinor a s r).re < 0) ∧
    (∀ M, ∃ r ≥ M, 0 < (rankMinor a s r).re) := by
  have hpair : S ≠ S.image σ := by
    intro h
    have hq' : q ∈ S := by rw [h, hswap]; exact mem_insert_self _ _
    exact hq hq'
  apply finite_product_split_pair ha hz σ hconj s S hS hpair hangle
  intro T hT hne hne'
  have hgap := SplitPairModulusOrder.boundary_product_gap
    (fun i => ‖(a i)⁻¹‖) (fun i => norm_pos_iff.mpr (inv_ne_zero (hz i)))
    S p q hp hq hmax hequal T ((mem_powersetCard.mp hT).2.trans hS.symm) hne
    (by simpa only [← hswap] using hne')
  simpa only [base, norm_prod] using hgap

/-- The paper's geometric finite-product formulation: conjugation-invariant
inner roots, one nonreal pair, strict inner/outer inverse-modulus gaps, and a
positive real inner product. No subset comparison or asymptotic is assumed. -/
theorem finite_product_split_pair_of_root_order {a : ι → ℂ} (ha : Function.Injective a)
    (hz : ∀ i, a i ≠ 0) (σ : ι ≃ ι) (hconj : ∀ i, a (σ i) = star (a i))
    (J : Finset ι) (p q : ι) (hp : p ∉ J) (hq : q ∉ J) (hpq : p ≠ q)
    (hσp : σ p = q) (hJ : J.image σ = J)
    (hphase : ((a p)⁻¹).im ≠ 0) {P : ℝ} (hP : 0 < P)
    (hproduct : (∏ i ∈ J, (a i)⁻¹) = (P : ℂ))
    (hinner : ∀ i ∈ J, ‖(a p)⁻¹‖ < ‖(a i)⁻¹‖)
    (houter : ∀ i ∉ insert p (insert q J), ‖(a i)⁻¹‖ < ‖(a p)⁻¹‖) :
    (∀ M, ∃ r ≥ M, (rankMinor a (J.card+1) r).re < 0) ∧
    (∀ M, ∃ r ≥ M, 0 < (rankMinor a (J.card+1) r).re) := by
  classical
  let S := insert p J
  have hcard : S.card = J.card+1 := card_insert_of_notMem hp
  have hpS : p ∈ S := mem_insert_self _ _
  have hqS : q ∉ S := by simp [S, hq, Ne.symm hpq]
  have hswap : S.image σ = insert q (S.erase p) := by
    simp [S, image_insert, hσp, hJ, hp]
  have hangle : (base a S).im ≠ 0 := by
    unfold base
    rw [prod_insert hp, hproduct]
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add] using
      mul_ne_zero hphase hP.ne'
  have hnormpair : ‖(a q)⁻¹‖ = ‖(a p)⁻¹‖ := by
    rw [← hσp, hconj p]
    simp
  have hybound (y : ι) (hy : y ∉ S) : ‖(a y)⁻¹‖ ≤ ‖(a p)⁻¹‖ := by
    by_cases hyq : y = q
    · simpa only [hyq] using hnormpair.le
    · exact (houter y (by simpa [S, mem_insert, hyq] using hy)).le
  have hystrict (y : ι) (hy : y ∉ S) (hyq : y ≠ q) :
      ‖(a y)⁻¹‖ < ‖(a p)⁻¹‖ := houter y (by simpa [S, mem_insert, hyq] using hy)
  apply finite_product_split_pair_of_boundary ha hz σ hconj (J.card+1) S hcard p q
    hpS hqS hswap hangle
  · intro x hx y hy
    rcases mem_insert.mp hx with rfl | hx
    · exact hybound y hy
    · exact (hybound y hy).trans (hinner x hx).le
  · intro x hx y hy heq
    have hxp : x = p := by
      by_contra h
      have hxJ : x ∈ J := (mem_insert.mp hx).resolve_left h
      have := hinner x hxJ
      have := hybound y hy
      linarith
    refine ⟨hxp, ?_⟩
    by_contra hyq
    have := hystrict y hy hyq
    rw [hxp] at heq
    linarith

end Reinmann.FiniteProductSplitPair
