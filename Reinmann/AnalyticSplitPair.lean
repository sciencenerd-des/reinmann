/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.SplitPairCoefficientIdentity
import Reinmann.SplitPairMixedRows
import Reinmann.ToeplitzComplementSigned
import Mathlib.Analysis.Calculus.Deriv.Star

/-! Standalone analytic split-pair oscillation. No PF implies RH bridge is modified. -/
noncomputable section
namespace Reinmann.AnalyticSplitPair
open Finset Filter Matrix
open scoped Topology
open SplitPairDeterminant SplitPairOscillation

theorem finite_split_sum_with_error_both_signs {ι : Type*} [Fintype ι]
    {K u : ℂ} (hK : K ≠ 0) (hu : ‖u‖ = 1)
    (hne : u ≠ 1) (hne2 : u ^ 2 ≠ 1) (c v : ι → ℂ) (hv : ∀ i, ‖v i‖ < 1)
    (error : ℕ → ℂ) (herror : Tendsto error atTop (nhds 0)) :
    (∀ M, ∃ n ≥ M,
      (K * u ^ n + star K * (star u) ^ n + ∑ i, c i * v i ^ n + error n).re < 0) ∧
    (∀ M, ∃ n ≥ M,
      0 < (K * u ^ n + star K * (star u) ^ n + ∑ i, c i * v i ^ n + error n).re) := by
  let w : ℂ := K / (‖K‖ : ℂ)
  have hk : 0 < ‖K‖ := norm_pos_iff.mpr hK
  have hw : ‖w‖ = 1 := by
    dsimp [w]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk, div_self hk.ne']
  have he0 : Tendsto (fun n => (∑ i, c i*v i^n)+error n) atTop (nhds 0) := by
    simpa using (SplitPairOscillation.finite_geometric_tail_tendsto c v hv).add herror
  have he := (Complex.continuous_re.tendsto (0 : ℂ)).comp he0
  have h := SplitPairOscillation.perturbed_phase_both_signs hu hw hne hne2 (show 0 < 2 * ‖K‖ by positivity) he
  have hphase (n : ℕ) :
      (K * u ^ n + star K * (star u) ^ n + ∑ i, c i * v i ^ n + error n).re =
      (2 * ‖K‖) * (w * u ^ n).re + (∑ i, c i * v i ^ n + error n).re := by
    have hscale : K = (‖K‖ : ℂ) * w := by
      dsimp [w]
      field_simp [Complex.ofReal_ne_zero.mpr hk.ne']
    have hlead : (star K * (star u) ^ n).re = (K * u ^ n).re := by
      rw [← star_pow, ← star_mul]
      simpa only [mul_comm] using Complex.conj_re (u ^ n * K)
    have hreal : (K * u ^ n).re = ‖K‖ * (w * u ^ n).re := by
      calc
        _ = ((‖K‖ : ℂ) * (w * u ^ n)).re := congrArg Complex.re (by
          calc
            K * u ^ n = ((‖K‖ : ℂ) * w) * u ^ n := congrArg (fun t : ℂ => t * u ^ n) hscale
            _ = _ := mul_assoc _ _ _)
        _ = _ := by simp [Complex.mul_re]
    simp only [Complex.add_re, hlead, hreal]
    ring
  simp_rw [hphase]
  simpa only [Function.comp_apply] using h



def poleBase {ι : Type*} (z : ι → ℂ) (S : Finset ι) := ∏ i ∈ S, z i
def poleLeading {ι : Type*} [Fintype ι] (c z : ι → ℂ) (s : ℕ) (S : Finset ι) :=
  SplitPairDeterminant.coefficient c z s S

private theorem poleBase_conjugate {ι : Type*} [DecidableEq ι] (σ : ι ≃ ι)
    {z : ι → ℂ} (hz : ∀ i, z (σ i) = star (z i)) (S : Finset ι) :
    poleBase z (S.image σ) = star (poleBase z S) := by
  unfold poleBase
  rw [prod_image σ.injective.injOn]
  change _ = (starRingEnd ℂ) (∏ i ∈ S, z i)
  simp [hz, map_prod]

/-- A computed finite pole determinant plus a vanishing normalized analytic
error oscillates. The final analytic theorem below proves this error condition. -/
theorem moment_split_pair_perturbed {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c0 z : ι → ℂ) (hc0 : ∀ i, c0 i ≠ 0) (hz : Function.Injective z)
    (σ : ι ≃ ι) (hcconj : ∀ i, c0 (σ i) = star (c0 i))
    (hzconj : ∀ i, z (σ i) = star (z i))
    (s : ℕ) (S : Finset ι) (hS : S.card = s)
    (hpair : S ≠ S.image σ) (hangle : (poleBase z S).im ≠ 0)
    (hgap : ∀ T ∈ (univ : Finset ι).powersetCard s,
      T ≠ S → T ≠ S.image σ → ‖poleBase z T‖ < ‖poleBase z S‖)
    (A : ℕ → ℂ)
    (herror : Tendsto (fun n => (A n-(momentMatrix c0 z s n).det) /
      (‖poleBase z S‖ : ℂ)^n) atTop (nhds 0)) :
    (∀ M, ∃ n ≥ M, (A n).re < 0) ∧ (∀ M, ∃ n ≥ M, 0 < (A n).re) := by
  classical
  let P := (univ : Finset ι).powersetCard s
  let T := S.image σ
  let R : ℝ := ‖poleBase z S‖
  let u : ℂ := poleBase z S / (R : ℂ)
  let K : ℂ := poleLeading c0 z s S
  let rest : Finset (Finset ι) := (P.erase S).erase T
  let c : rest → ℂ := fun U => poleLeading c0 z s U.val
  let v : rest → ℂ := fun U => poleBase z U.val / (R : ℂ)
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
  have hK : K ≠ 0 := coefficient_ne_zero hz hc0 s hS
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
  have hbaseT : poleBase z T / (R : ℂ) = star u := by
    rw [poleBase_conjugate σ hzconj]
    change star (poleBase z S) / (R : ℂ) = star (poleBase z S / (R : ℂ))
    simp [star_div₀]
  have hleadT : poleLeading c0 z s T = star K := coefficient_conjugate σ hcconj hzconj s S
  have hnorm (n : ℕ) : (momentMatrix c0 z s n).det / (R : ℂ) ^ n =
      K * u ^ n + star K * (star u) ^ n + ∑ U : rest, c U * v U ^ n := by
    rw [subset_expansion]
    change (∑ U ∈ P, poleLeading c0 z s U*poleBase z U^n)/(R : ℂ)^n = _
    have hdiv : (∑ U ∈ P, poleLeading c0 z s U * poleBase z U ^ n) / (R : ℂ) ^ n =
        ∑ U ∈ P, poleLeading c0 z s U * poleBase z U ^ n / (R : ℂ) ^ n := by
      simp only [div_eq_mul_inv, Finset.sum_mul]
    rw [hdiv]
    have hterm (U : Finset ι) : poleLeading c0 z s U * poleBase z U ^ n / (R : ℂ) ^ n =
        poleLeading c0 z s U * (poleBase z U / (R : ℂ)) ^ n := by
      rw [div_pow, mul_div_assoc]
    simp_rw [hterm]
    rw [← add_sum_erase _ _ hSmem,
      ← add_sum_erase _ _ (mem_erase.mpr ⟨hTne, hTmem⟩)]
    rw [hleadT, hbaseT]
    change K * u ^ n + (star K * star u ^ n + ∑ U ∈ rest, poleLeading c0 z s U * (poleBase z U / ↑R) ^ n) = _
    rw [← Finset.sum_coe_sort rest (fun U => poleLeading c0 z s U * (poleBase z U / ↑R) ^ n)]
    exact (add_assoc _ _ _).symm
  let error (n : ℕ) := (A n-(momentMatrix c0 z s n).det)/(R : ℂ)^n
  have hnormA (n : ℕ) : A n/(R : ℂ)^n =
      K*u^n + star K*(star u)^n + ∑ U : rest, c U*v U^n + error n := by
    rw [← hnorm n]
    dsimp [error]
    ring
  have hosc := finite_split_sum_with_error_both_signs hK hu hne hne2 c v hv error herror
  have hnegative (M : ℕ) : ∃ n ≥ M, (A n).re < 0 := by
    obtain ⟨n, hn, hsign⟩ := hosc.1 M
    refine ⟨n, hn, ?_⟩
    rw [← hnormA n] at hsign
    have hs : (A n).re / R ^ n < 0 := by
      simpa only [← Complex.ofReal_pow, Complex.div_ofReal_re] using hsign
    simpa using (div_lt_iff₀ (pow_pos hR n)).mp hs
  have hpositive (M : ℕ) : ∃ n ≥ M, 0 < (A n).re := by
    obtain ⟨n, hn, hsign⟩ := hosc.2 M
    refine ⟨n, hn, ?_⟩
    rw [← hnormA n] at hsign
    have hs : 0 < (A n).re / R ^ n := by
      simpa only [← Complex.ofReal_pow, Complex.div_ofReal_re] using hsign
    simpa using (lt_div_iff₀ (pow_pos hR n)).mp hs
  exact ⟨hnegative,hpositive⟩

/-- Actual coefficient errors give a vanishing normalized determinant error.
Uniform constants are chosen from finite sums; no determinant asymptotic is input. -/
theorem normalized_determinant_error_tendsto {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c z : ι → ℂ) (h : ℕ → ℂ) {s : ℕ} (hs : 0 < s)
    (S : Finset ι) (hS : S.card = s) {d ρ C0 : ℝ}
    (hd : 0 < d) (hρ : 0 ≤ ρ) (hρd : ρ < d) (hC0 : 0 ≤ C0)
    (htop : ∀ i ∈ S, d ≤ ‖z i‖) (hout : ∀ i ∉ S, ‖z i‖ ≤ d)
    (he : ∀ k, ‖h k-∑ i, c i*z i^k‖ ≤ C0*ρ^k) :
    Tendsto (fun n =>
      (Matrix.det (fun i j : Fin s => h (n+i.val+(s-1-j.val))) -
        (momentMatrix c z s n).det)/(‖poleBase z S‖ : ℂ)^n) atTop (nhds 0) := by
  classical
  let C := C0+∑ i, ‖c i‖
  let B := 1+ρ+∑ i, ‖z i‖
  let D := ‖poleBase z S‖
  let e (k : ℕ) := h k-∑ i, c i*z i^k
  have hc0 : 0 ≤ ∑ i, ‖c i‖ := sum_nonneg (fun i _ => norm_nonneg _)
  have hz0 : 0 ≤ ∑ i, ‖z i‖ := sum_nonneg (fun i _ => norm_nonneg _)
  have hC : 0 ≤ C := by dsimp [C]; linarith
  have hB : 1 ≤ B := by dsimp [B]; linarith
  have hρB : ρ ≤ B := by dsimp [B]; linarith
  have hc (i : ι) : ‖c i‖ ≤ C := by
    have hsum := single_le_sum (fun j _ => norm_nonneg (c j)) (mem_univ i)
    dsimp [C]; linarith
  have hz (i : ι) : ‖z i‖ ≤ B := by
    have hsum := single_le_sum (fun j _ => norm_nonneg (z j)) (mem_univ i)
    dsimp [B]; linarith
  have he' (k : ℕ) : ‖e k‖ ≤ C*ρ^k := (he k).trans
    (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (pow_nonneg hρ k))
  have hD : 0 < D := by
    dsimp [D,poleBase]
    rw [norm_prod]
    exact prod_pos (fun i hi => hd.trans_le (htop i hi))
  let A := (Fintype.card ι+1 : ℝ)^s*(s.factorial*(C*B^(2*s-2))^s)
  have hb (n : ℕ) :
      ‖(Matrix.det (fun i j : Fin s => h (n+i.val+(s-1-j.val))) -
        (momentMatrix c z s n).det)/(D : ℂ)^n‖ ≤ A*(ρ/d)^n := by
    have H := SplitPairMixedRows.coefficient_determinant_bound hs c z e S hC hB
      hd hρ hρd.le hρB hc hz htop hout hS he' (n := n)
    have hm : (fun i j : Fin s => (∑ l, c l*z l^(n+i.val+(s-1-j.val)))+
          e (n+i.val+(s-1-j.val))) = (fun i j => h (n+i.val+(s-1-j.val))) := by
      ext i j
      dsimp [e]
      ring
    rw [hm] at H
    simpa only [A,D,poleBase,momentMatrix,norm_div,norm_pow,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos hD,norm_prod,abs_norm,mul_assoc] using H
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (div_nonneg hρ hd.le) ((div_lt_one hd).mpr hρd)).const_mul A
  apply squeeze_zero_norm hb
  simpa using ht

/-- Reciprocal complementary determinant of actual ordinary Taylor coefficients. -/
def reciprocalMinor (F : ℂ → ℂ) (s n : ℕ) : ℂ :=
  Matrix.det (fun i j : Fin s =>
    SplitPairCauchyTail.coefficient (fun w => (F w)⁻¹) (n+i.val+(s-1-j.val)))

/-- Conjugation symmetry of an entire function also holds for its derivative. -/
theorem derivative_conjugate {F : ℂ → ℂ} (hF : ∀ z, F (star z) = star (F z)) (z : ℂ) :
    deriv F (star z) = star (deriv F z) := by
  have heq : (star : ℂ → ℂ) ∘ F ∘ star = F := by
    funext w
    simp only [Function.comp_apply, hF, star_star]
  have hd := congrFun (deriv_conj_conj (f := F)) (star z)
  change deriv ((star : ℂ → ℂ) ∘ F ∘ star) (star z) = star (deriv F (star (star z))) at hd
  rw [heq] at hd
  simpa only [Function.comp_apply, star_star] using hd

/-- Entire-function split-pair oscillation from simple zeros in one disk and
strict finite subset-product gaps. The Cauchy and determinant errors are proved,
not hypotheses. A genus-zero entire function is a special case. -/
theorem entire_split_pair {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : ℂ → ℂ} (hF : Differentiable ℂ F) (hF0 : F 0 ≠ 0)
    (hFconj : ∀ z, F (star z) = star (F z)) (a : ι → ℂ)
    (ha : Function.Injective a) (hzero : ∀ i, F (a i) = 0)
    (hsimple : ∀ i, deriv F (a i) ≠ 0) (σ : ι ≃ ι)
    (hconj : ∀ i, a (σ i) = star (a i)) {R d : ℝ} (hR : 0 < R) (hd : 0 < d)
    (hall : ∀ z ∈ Metric.closedBall 0 R, F z = 0 → ∃ i, z = a i)
    (hsep : R⁻¹ < d) (s : ℕ) (hs : 0 < s) (S : Finset ι) (hS : S.card = s)
    (htop : ∀ i ∈ S, d ≤ ‖(a i)⁻¹‖) (hout : ∀ i ∉ S, ‖(a i)⁻¹‖ ≤ d)
    (hpair : S ≠ S.image σ) (hangle : (∏ i ∈ S, (a i)⁻¹).im ≠ 0)
    (hgap : ∀ T ∈ (univ : Finset ι).powersetCard s,
      T ≠ S → T ≠ S.image σ → ‖∏ i ∈ T, (a i)⁻¹‖ < ‖∏ i ∈ S, (a i)⁻¹‖) :
    (∀ M, ∃ n ≥ M, (reciprocalMinor F s n).re < 0) ∧
    (∀ M, ∃ n ≥ M, 0 < (reciprocalMinor F s n).re) := by
  classical
  let c : ι → ℂ := fun i => -(deriv F (a i))⁻¹/a i
  let z : ι → ℂ := fun i => (a i)⁻¹
  have hz0 (i : ι) : a i ≠ 0 := by
    intro h
    exact hF0 (h ▸ hzero i)
  have hc0 (i : ι) : c i ≠ 0 := div_ne_zero (neg_ne_zero.mpr (inv_ne_zero (hsimple i))) (hz0 i)
  have hz : Function.Injective z := inv_injective.comp ha
  have hcconj (i : ι) : c (σ i) = star (c i) := by
    dsimp [c]
    rw [hconj i, derivative_conjugate hFconj]
    simp only [map_div₀,map_neg,map_inv₀,starRingEnd_apply]
  have hzconj (i : ι) : z (σ i) = star (z i) := by simp [z,hconj]
  obtain ⟨C0,hC0,he⟩ := SplitPairCoefficientIdentity.actual_reciprocal_coefficient_error
    hF hF0 a ha hzero hsimple hR hall
  have he' (k : ℕ) :
      ‖SplitPairCauchyTail.coefficient (fun w => (F w)⁻¹) k-∑ i, c i*z i^k‖ ≤ C0*(R⁻¹)^k := by
    simpa only [c,z,one_div,div_eq_mul_inv,inv_pow,mul_one,one_mul] using he k
  have hlim := normalized_determinant_error_tendsto c z
    (SplitPairCauchyTail.coefficient (fun w => (F w)⁻¹)) hs S hS hd (inv_nonneg.mpr hR.le)
    hsep hC0 htop hout he'
  exact moment_split_pair_perturbed c z hc0 hz σ hcconj hzconj s S hS hpair hangle hgap
    (reciprocalMinor F s) hlim

/-- An isolated pair straddling the boundary of a top-modulus subset supplies
all subset gaps. Only the pair needs to lie strictly inside the Cauchy radius. -/
theorem entire_split_pair_of_boundary {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : ℂ → ℂ} (hF : Differentiable ℂ F) (hF0 : F 0 ≠ 0)
    (hFconj : ∀ z, F (star z) = star (F z)) (a : ι → ℂ)
    (ha : Function.Injective a) (hzero : ∀ i, F (a i) = 0)
    (hsimple : ∀ i, deriv F (a i) ≠ 0) (σ : ι ≃ ι)
    (hconj : ∀ i, a (σ i) = star (a i)) {R : ℝ} (hR : 0 < R)
    (hall : ∀ z ∈ Metric.closedBall 0 R, F z = 0 → ∃ i, z = a i)
    (s : ℕ) (S : Finset ι) (hS : S.card = s) (p q : ι) (hp : p ∈ S) (hq : q ∉ S)
    (hσp : σ p = q) (hswap : S.image σ = insert q (S.erase p))
    (hangle : (∏ i ∈ S, (a i)⁻¹).im ≠ 0) (hpR : ‖a p‖ < R)
    (hmax : ∀ x ∈ S, ∀ y ∉ S, ‖(a y)⁻¹‖ ≤ ‖(a x)⁻¹‖)
    (hequal : ∀ x ∈ S, ∀ y ∉ S, ‖(a y)⁻¹‖ = ‖(a x)⁻¹‖ → x = p ∧ y = q) :
    (∀ M, ∃ n ≥ M, (reciprocalMinor F s n).re < 0) ∧
    (∀ M, ∃ n ≥ M, 0 < (reciprocalMinor F s n).re) := by
  have hz0 (i : ι) : a i ≠ 0 := by intro h; exact hF0 (h ▸ hzero i)
  have hd : 0 < ‖(a p)⁻¹‖ := norm_pos_iff.mpr (inv_ne_zero (hz0 p))
  have hsep : R⁻¹ < ‖(a p)⁻¹‖ := by
    rw [norm_inv]
    exact (inv_lt_inv₀ hR (norm_pos_iff.mpr (hz0 p))).mpr hpR
  have hnormpair : ‖(a q)⁻¹‖ = ‖(a p)⁻¹‖ := by rw [← hσp,hconj]; simp
  have hs : 0 < s := hS ▸ card_pos.mpr ⟨p,hp⟩
  have hpair : S ≠ S.image σ := by
    intro h
    exact hq (by rw [h,hswap]; exact mem_insert_self _ _)
  apply entire_split_pair hF hF0 hFconj a ha hzero hsimple σ hconj hR hd hall hsep
    s hs S hS (fun x hx => by simpa [hnormpair] using hmax x hx q hq)
    (fun y hy => hmax p hp y hy) hpair hangle
  intro T hT hne hne'
  have h := SplitPairModulusOrder.boundary_product_gap
    (fun i => ‖(a i)⁻¹‖) (fun i => norm_pos_iff.mpr (inv_ne_zero (hz0 i)))
    S p q hp hq hmax hequal T ((mem_powersetCard.mp hT).2.trans hS.symm) hne
    (by simpa only [← hswap] using hne')
  simpa only [norm_prod] using h

end Reinmann.AnalyticSplitPair
