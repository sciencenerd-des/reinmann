/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.ToeplitzKernel
import Mathlib.FieldTheory.Separable
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Simple roots of corank-one positive Toeplitz kernel polynomials

Shared finite linear algebra. No arithmetic positivity or atomic moment
representation is assumed. The original kernel-root module is unchanged.
-/

noncomputable section

namespace Reinmann.ToeplitzSimpleRoots

open Matrix Polynomial Reinmann.ToeplitzKernel
open scoped ComplexOrder

/-- The Toeplitz sesquilinear pairing of ordinary polynomial coefficients. -/
def pairing {n : ℕ} (T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (p q : ℂ[X]) : ℂ := star (coeffVec n p) ⬝ᵥ (T *ᵥ coeffVec n q)

lemma pairing_shift {n : ℕ} {T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hT : IsToeplitz T) (p q : ℂ[X]) (hp : p.natDegree < n) (hq : q.natDegree < n) :
    pairing T (X * p) (X * q) = pairing T p q := by
  have hplast : p.coeff n = 0 := coeff_eq_zero_of_natDegree_lt hp
  have hqlast : q.coeff n = 0 := coeff_eq_zero_of_natDegree_lt hq
  unfold pairing
  simp only [dotProduct, mulVec, Pi.star_apply, coeffVec, Finset.mul_sum]
  conv_lhs => rw [Fin.sum_univ_succ]
  conv_rhs => rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_zero, coeff_X_mul_zero, star_zero, zero_mul, Finset.sum_const_zero,
    Fin.val_last, hplast, star_zero, zero_mul, add_zero, zero_add,
    Fin.val_succ, coeff_X_mul, Fin.val_castSucc]
  conv_lhs => simp only [Fin.sum_univ_succ]
  conv_rhs => simp only [Fin.sum_univ_castSucc]
  simp only [Fin.val_zero, coeff_X_mul_zero, mul_zero, zero_add,
    Fin.val_succ, coeff_X_mul, Fin.val_last, hqlast, mul_zero, add_zero, Fin.val_castSucc]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hT i j]

/-- Corank one excludes every nonzero short polynomial from the energy kernel. -/
theorem energy_ne_zero_of_natDegree_lt {n : ℕ}
    {T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hpsd : T.PosSemidef) (htoe : IsToeplitz T) (hrank : T.rank = n)
    {q : ℂ[X]} (hq : q.natDegree < n) (hq0 : q ≠ 0) :
    energy T (coeffVec n q) ≠ 0 := by
  intro h
  have hk := (hpsd.dotProduct_mulVec_zero_iff (coeffVec n q)).mp h
  have hd := natDegree_eq_of_kernel hpsd htoe hrank hq.le hq0 hk
  omega

/-- Strict positive energy on polynomials of degree below the matrix rank. -/
theorem energy_pos_of_natDegree_lt {n : ℕ}
    {T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hpsd : T.PosSemidef) (htoe : IsToeplitz T) (hrank : T.rank = n)
    {q : ℂ[X]} (hq : q.natDegree < n) (hq0 : q ≠ 0) :
    0 < energy T (coeffVec n q) := by
  exact lt_of_le_of_ne (hpsd.dotProduct_mulVec_nonneg _)
    (Ne.symm (energy_ne_zero_of_natDegree_lt hpsd htoe hrank hq hq0))

lemma quotient_not_root {n : ℕ}
    {T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hpsd : T.PosSemidef) (htoe : IsToeplitz T) (hrank : T.rank = n)
    {p q : ℂ[X]} (hp : p.natDegree ≤ n) (hp0 : p ≠ 0)
    (hpk : T *ᵥ coeffVec n p = 0) {z : ℂ} (hfactor : p = (X - C z) * q) :
    ¬ q.IsRoot z := by
  intro hqroot
  have hq0 : q ≠ 0 := by
    intro h
    apply hp0
    simp [hfactor, h]
  have hdeg : p.natDegree = 1 + q.natDegree := by
    rw [hfactor, natDegree_mul (X_sub_C_ne_zero z) hq0, natDegree_X_sub_C]
  have hqn : q.natDegree < n := by omega
  obtain ⟨r, hr⟩ := dvd_iff_isRoot.mpr hqroot
  have hr0 : r ≠ 0 := by
    intro h
    apply hq0
    simp [hr, h]
  have hdegr : q.natDegree = 1 + r.natDegree := by
    rw [hr, natDegree_mul (X_sub_C_ne_zero z) hr0, natDegree_X_sub_C]
  have hrn : r.natDegree < n := by omega
  have hzroot : p.IsRoot z := by simp [IsRoot, hfactor]
  have hznorm := root_norm_eq_one hpsd htoe hrank hp hp0 hpk hzroot
  have hz0 : z ≠ 0 := by
    intro h
    exact zero_ne_one (by simpa only [h, norm_zero] using hznorm)
  have hunit : star z * z = 1 := by
    change starRingEnd ℂ z * z = 1
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hznorm]
    norm_num
  have hrel : coeffVec n p = coeffVec n (X * q) - z • coeffVec n q := by
    ext i
    simp [coeffVec, hfactor, sub_mul]
  have hright : T *ᵥ coeffVec n (X * q) = z • (T *ᵥ coeffVec n q) := by
    have h := hpk
    rw [hrel, mulVec_sub, mulVec_smul, sub_eq_zero] at h
    exact h
  have hleft : coeffVec n (X * r) = coeffVec n q + z • coeffVec n r := by
    ext i
    simp [coeffVec, hr, sub_mul]
  have hs := pairing_shift htoe r q hrn hqn
  unfold pairing at hs
  rw [hright, hleft, star_add, star_smul, dotProduct_smul, add_dotProduct,
    smul_dotProduct] at hs
  simp only [smul_eq_mul] at hs
  have hsum : z * energy T (coeffVec n q) +
      (star z * z) * pairing T r q = pairing T r q := by
    unfold energy pairing
    linear_combination hs
  rw [hunit, one_mul] at hsum
  have he : z * energy T (coeffVec n q) = 0 := by linear_combination hsum
  exact mul_ne_zero hz0 (energy_ne_zero_of_natDegree_lt hpsd htoe hrank hqn hq0) he

/-- Every root of a nonzero corank-one Toeplitz kernel polynomial is simple. -/
theorem derivative_ne_zero_at_root {n : ℕ}
    {T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hpsd : T.PosSemidef) (htoe : IsToeplitz T) (hrank : T.rank = n)
    {p : ℂ[X]} (hp : p.natDegree ≤ n) (hp0 : p ≠ 0)
    (hpk : T *ᵥ coeffVec n p = 0) {z : ℂ} (hz : p.IsRoot z) :
    p.derivative.eval z ≠ 0 := by
  obtain ⟨q, hfactor⟩ := dvd_iff_isRoot.mpr hz
  have hq := quotient_not_root hpsd htoe hrank hp hp0 hpk hfactor
  simpa only [hfactor, derivative_mul, derivative_sub, derivative_X, derivative_C,
    sub_zero, one_mul, eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self,
    zero_mul, add_zero, IsRoot] using hq

/-- A corank-one positive Toeplitz kernel polynomial is separable. -/
theorem separable_of_kernel {n : ℕ}
    {T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hpsd : T.PosSemidef) (htoe : IsToeplitz T) (hrank : T.rank = n)
    {p : ℂ[X]} (hp : p.natDegree ≤ n) (hp0 : p ≠ 0)
    (hpk : T *ᵥ coeffVec n p = 0) : p.Separable := by
  apply (nodup_roots_iff_of_splits hp0 (IsAlgClosed.splits p)).mp
  apply Multiset.nodup_iff_count_le_one.mpr
  intro z
  rw [count_roots]
  by_contra h
  have hs := (one_lt_rootMultiplicity_iff_isRoot hp0).mp (by omega : 1 < p.rootMultiplicity z)
  exact derivative_ne_zero_at_root hpsd htoe hrank hp hp0 hpk hs.1 hs.2

/-- There are exactly n distinct roots in the unit circle. -/
theorem distinct_unit_circle_roots {n : ℕ}
    {T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hpsd : T.PosSemidef) (htoe : IsToeplitz T) (hrank : T.rank = n)
    {p : ℂ[X]} (hp : p.natDegree ≤ n) (hp0 : p ≠ 0)
    (hpk : T *ᵥ coeffVec n p = 0) :
    p.roots.toFinset.card = n ∧ ∀ z ∈ p.roots.toFinset, ‖z‖ = 1 := by
  have hsep := separable_of_kernel hpsd htoe hrank hp hp0 hpk
  constructor
  · rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep),
      IsAlgClosed.card_roots_eq_natDegree, natDegree_eq_of_kernel hpsd htoe hrank hp hp0 hpk]
  · intro z hz
    exact root_norm_eq_one hpsd htoe hrank hp hp0 hpk
      ((mem_roots hp0).mp (Multiset.mem_toFinset.mp hz))

end Reinmann.ToeplitzSimpleRoots
