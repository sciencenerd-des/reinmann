/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Tactic

/-!
# Unit-circle roots of a corank-one positive Toeplitz kernel

Formalizes the finite kernel-root corollary of Caratheodory--Fejer, as stated
in Connes--van Suijlekom, arXiv:2511.23257, Corollary 1.1, with the necessary
nonzero-vector hypothesis explicit. The proof uses shift isometry and
one-dimensionality of the kernel directly, without assuming an atomic moment
representation. It also proves that every nonzero kernel polynomial has full degree.

These are Hermitian two-sided Toeplitz matrices, not Taylor-coefficient PF matrices.
Shared finite linear algebra: no arithmetic positivity or RH input is supplied.
-/

noncomputable section

namespace Reinmann.ToeplitzKernel

open Matrix Polynomial
open scoped ComplexOrder

/-- Ordinary ascending polynomial coefficients, truncated at degree `n`. -/
def coeffVec (n : ℕ) (p : ℂ[X]) : Fin (n + 1) → ℂ := fun i => p.coeff i

/-- The Hermitian quadratic form, with conjugation in the first slot. -/
def energy {m : Type*} [Fintype m] (T : Matrix m m ℂ) (v : m → ℂ) : ℂ :=
  star v ⬝ᵥ (T *ᵥ v)

lemma energy_of_kernel_relation {m : Type*} [Fintype m]
    {T : Matrix m m ℂ} (hT : T.IsHermitian) (u w : m → ℂ) (z : ℂ)
    (hk : T *ᵥ (w - z • u) = 0) :
    energy T w = star z * z * energy T u := by
  have hr : T *ᵥ w = z • (T *ᵥ u) := by
    simpa only [mulVec_sub, mulVec_smul, sub_eq_zero] using hk
  have hl : star w ᵥ* T = star z • (star u ᵥ* T) := by
    have hh := congrArg star hr
    simpa only [star_mulVec, hT.eq, star_smul] using hh
  unfold energy
  calc
    star w ⬝ᵥ (T *ᵥ w) = (star w ᵥ* T) ⬝ᵥ w := dotProduct_mulVec _ _ _
    _ = star z * ((star u ᵥ* T) ⬝ᵥ w) := by rw [hl, smul_dotProduct]; rfl
    _ = star z * (star u ⬝ᵥ (T *ᵥ w)) := by rw [dotProduct_mulVec]
    _ = star z * z * (star u ⬝ᵥ (T *ᵥ u)) := by
      rw [hr, dotProduct_smul]
      simp only [smul_eq_mul]
      ring

/-- Toeplitz means invariance of entries under simultaneous one-step shift. -/
def IsToeplitz {n : ℕ} (T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : Prop :=
  ∀ i j : Fin n, T i.succ j.succ = T i.castSucc j.castSucc

lemma energy_shift {n : ℕ} {T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hT : IsToeplitz T) (q : ℂ[X]) (hq : q.natDegree < n) :
    energy T (coeffVec n (X * q)) = energy T (coeffVec n q) := by
  have hlast : q.coeff n = 0 := coeff_eq_zero_of_natDegree_lt hq
  unfold energy
  simp only [dotProduct, mulVec, Pi.star_apply, coeffVec, Finset.mul_sum]
  conv_lhs => rw [Fin.sum_univ_succ]
  conv_rhs => rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_zero, coeff_X_mul_zero, star_zero, zero_mul, Finset.sum_const_zero,
    Fin.val_last, hlast, star_zero, zero_mul, add_zero, zero_add,
    Fin.val_succ, coeff_X_mul, Fin.val_castSucc]
  conv_lhs => simp only [Fin.sum_univ_succ]
  conv_rhs => simp only [Fin.sum_univ_castSucc]
  simp only [Fin.val_zero, coeff_X_mul_zero, mul_zero, zero_add,
    Fin.val_succ, coeff_X_mul, Fin.val_last, hlast, mul_zero, add_zero, Fin.val_castSucc]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hT i j]

lemma polynomial_eq_of_coeffVec_eq {n : ℕ} {p q : ℂ[X]}
    (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n)
    (h : coeffVec n p = coeffVec n q) : p = q := by
  ext k
  by_cases hk : k ≤ n
  · exact congrFun h ⟨k, by omega⟩
  · rw [coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < k),
      coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < k)]

lemma coeffVec_ne_zero {n : ℕ} {p : ℂ[X]} (hp : p.natDegree ≤ n) (hp0 : p ≠ 0) :
    coeffVec n p ≠ 0 := by
  intro h
  apply hp0
  exact polynomial_eq_of_coeffVec_eq hp (by simp) (by simpa [coeffVec] using h)

lemma kernel_finrank {n : ℕ} {T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hrank : T.rank = n) : Module.finrank ℂ (LinearMap.ker T.mulVecLin) = 1 := by
  have h := T.mulVecLin.finrank_range_add_finrank_ker
  rw [← Matrix.rank, hrank] at h
  simp only [Module.finrank_pi, Fintype.card_fin] at h
  omega

lemma polynomial_eq_C_mul_of_kernel {n : ℕ}
    {T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hrank : T.rank = n)
    {p q : ℂ[X]} (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n) (hp0 : p ≠ 0)
    (hpk : T *ᵥ coeffVec n p = 0) (hqk : T *ᵥ coeffVec n q = 0) :
    ∃ c : ℂ, q = C c * p := by
  let vp : LinearMap.ker T.mulVecLin := ⟨coeffVec n p, hpk⟩
  let vq : LinearMap.ker T.mulVecLin := ⟨coeffVec n q, hqk⟩
  have hvp : vp ≠ 0 := by
    intro h
    apply coeffVec_ne_zero hp hp0
    exact congrArg Subtype.val h
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one (kernel_finrank hrank) hvp vq
  refine ⟨c, polynomial_eq_of_coeffVec_eq hq ?_ ?_⟩
  · exact (natDegree_C_mul_le c p).trans hp
  · funext i
    have hi := congrFun (congrArg Subtype.val hc) i
    simpa [vp, vq, coeffVec, coeff_C_mul] using hi.symm

/-- Corank-one positive Toeplitz kernel polynomials have only unit-circle roots.
The proof uses Toeplitz shift isometry and corank one, without a moment representation. -/
theorem root_norm_eq_one {n : ℕ}
    {T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hpsd : T.PosSemidef) (htoe : IsToeplitz T) (hrank : T.rank = n)
    {p : ℂ[X]} (hp : p.natDegree ≤ n) (hp0 : p ≠ 0)
    (hpk : T *ᵥ coeffVec n p = 0) {z : ℂ} (hz : p.IsRoot z) : ‖z‖ = 1 := by
  obtain ⟨q, hfactor⟩ := dvd_iff_isRoot.mpr hz
  have hq0 : q ≠ 0 := by
    intro h
    apply hp0
    simp [hfactor, h]
  have hdeg : p.natDegree = 1 + q.natDegree := by
    rw [hfactor, natDegree_mul (X_sub_C_ne_zero z) hq0, natDegree_X_sub_C]
  have hqn : q.natDegree < n := by omega
  have hrel : coeffVec n p = coeffVec n (X * q) - z • coeffVec n q := by
    ext i
    simp [coeffVec, hfactor, sub_mul]
  have he := energy_of_kernel_relation hpsd.isHermitian
    (coeffVec n q) (coeffVec n (X * q)) z (by rw [← hrel]; exact hpk)
  rw [energy_shift htoe q hqn] at he
  have he0 : energy T (coeffVec n q) ≠ 0 := by
    intro h
    have hqk := (hpsd.dotProduct_mulVec_zero_iff (coeffVec n q)).mp h
    obtain ⟨c, hc⟩ := polynomial_eq_C_mul_of_kernel hrank hp hqn.le hp0 hpk hqk
    have hc0 : c ≠ 0 := by
      intro hh
      exact hq0 (by simpa only [hh, map_zero, zero_mul] using hc)
    have hdeg' : q.natDegree = p.natDegree := by
      rw [hc, natDegree_C_mul hc0]
    omega
  have hzz : star z * z = 1 := by
    apply mul_right_cancel₀ he0
    simpa using he.symm
  have hn := congrArg norm hzz
  simp only [norm_mul, norm_star, norm_one] at hn
  nlinarith [norm_nonneg z]

/-- Every nonzero kernel polynomial has full degree; corank one rules out
simultaneous kernel membership of a polynomial and its one-step shift. -/
theorem natDegree_eq_of_kernel {n : ℕ}
    {T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hpsd : T.PosSemidef) (htoe : IsToeplitz T) (hrank : T.rank = n)
    {p : ℂ[X]} (hp : p.natDegree ≤ n) (hp0 : p ≠ 0)
    (hpk : T *ᵥ coeffVec n p = 0) : p.natDegree = n := by
  by_contra hne
  have hlt : p.natDegree < n := lt_of_le_of_ne hp hne
  have hshift : T *ᵥ coeffVec n (X * p) = 0 := by
    apply (hpsd.dotProduct_mulVec_zero_iff _).mp
    change energy T (coeffVec n (X * p)) = 0
    rw [energy_shift htoe p hlt]
    simp [energy, hpk]
  have hd : (X * p).natDegree = 1 + p.natDegree := by
    rw [natDegree_mul X_ne_zero hp0, natDegree_X]
  obtain ⟨c, hc⟩ := polynomial_eq_C_mul_of_kernel hrank hp (by omega) hp0 hpk hshift
  have hle : (X * p).natDegree ≤ p.natDegree := by
    rw [hc]
    exact natDegree_C_mul_le c p
  omega

/-- The full ordinary kernel-vector form of the finite Caratheodory--Fejer corollary.
`ofFn (n+1) v` is exactly the polynomial with ascending coefficients `v`. -/
theorem kernel_polynomial_roots_unit_circle {n : ℕ}
    {T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hpsd : T.PosSemidef) (htoe : IsToeplitz T) (hrank : T.rank = n)
    {v : Fin (n + 1) → ℂ} (hv : v ≠ 0) (hvk : T *ᵥ v = 0)
    {z : ℂ} (hz : (ofFn (n + 1) v).IsRoot z) : ‖z‖ = 1 := by
  have hcoeff : coeffVec n (ofFn (n + 1) v) = v := by
    ext i
    exact ofFn_coeff_eq_val_of_lt v i.isLt
  apply root_norm_eq_one hpsd htoe hrank (Nat.le_of_lt_succ (ofFn_natDegree_lt (by omega) v))
  · intro h
    apply hv
    have hh := congrArg (coeffVec n) h
    simpa [hcoeff, coeffVec] using hh
  · simpa [hcoeff] using hvk
  · exact hz

/-- The entry-difference convention is a Toeplitz matrix in the shift convention. -/
lemma isToeplitz_of_difference (n : ℕ) (c : ℤ → ℂ) :
    IsToeplitz (fun i j : Fin (n + 1) => c ((j : ℤ) - (i : ℤ))) := by
  intro i j
  change c (((j.val + 1 : ℕ) : ℤ) - ((i.val + 1 : ℕ) : ℤ)) =
    c ((j.val : ℤ) - (i.val : ℤ))
  congr 1
  push_cast
  ring

end Reinmann.ToeplitzKernel
