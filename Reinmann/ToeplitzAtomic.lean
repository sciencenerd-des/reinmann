/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.ToeplitzSimpleRoots
import Mathlib.LinearAlgebra.Lagrange

/-! # Corank-one finite Toeplitz atomic representation

Shared finite linear algebra. No arithmetic positivity is supplied.
-/

noncomputable section

namespace Reinmann.ToeplitzAtomic

open Matrix Polynomial Reinmann.ToeplitzKernel Reinmann.ToeplitzSimpleRoots
open scoped ComplexOrder

lemma coeffVec_sub {n : ℕ} (p q : ℂ[X]) :
    coeffVec n (p - q) = coeffVec n p - coeffVec n q := by
  ext i
  simp [coeffVec]

lemma coeffVec_C_mul {n : ℕ} (a : ℂ) (p : ℂ[X]) :
    coeffVec n (C a * p) = a • coeffVec n p := by
  ext i
  simp [coeffVec]

lemma coeffVec_sum {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → ℂ[X]) :
    coeffVec n (∑ i ∈ s, f i) = ∑ i ∈ s, coeffVec n (f i) := by
  ext i
  simp [coeffVec]

lemma pairing_sum_left {n : ℕ} {ι : Type*} (T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (s : Finset ι) (f : ι → ℂ[X]) (q : ℂ[X]) :
    pairing T (∑ i ∈ s, f i) q = ∑ i ∈ s, pairing T (f i) q := by
  simp [pairing, coeffVec_sum, star_sum, sum_dotProduct]

lemma pairing_sum_right {n : ℕ} {ι : Type*} (T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (s : Finset ι) (p : ℂ[X]) (f : ι → ℂ[X]) :
    pairing T p (∑ i ∈ s, f i) = ∑ i ∈ s, pairing T p (f i) := by
  simp [pairing, coeffVec_sum, mulVec_sum, dotProduct_sum]

lemma pairing_C_mul_left {n : ℕ} (T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (a : ℂ) (p q : ℂ[X]) : pairing T (C a * p) q = star a * pairing T p q := by
  simp [pairing, coeffVec_C_mul, star_smul, smul_dotProduct]

lemma pairing_C_mul_right {n : ℕ} (T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (a : ℂ) (p q : ℂ[X]) : pairing T p (C a * q) = a * pairing T p q := by
  simp [pairing, coeffVec_C_mul, mulVec_smul, dotProduct_smul]

/-- Positive weights on exactly `r` distinct unit-circle nodes reproduce every entry. -/
def HasAtomicRepresentation {n : ℕ}
    (T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (r : ℕ) : Prop :=
  ∃ s : Finset ℂ, ∃ w : ℂ → ℝ,
    s.card = r ∧ (∀ z ∈ s, ‖z‖ = 1 ∧ 0 < w z) ∧
      ∀ i j : Fin (n + 1),
        T i j = ∑ z ∈ s, (w z : ℂ) * star (z ^ (i : ℕ)) * z ^ (j : ℕ)

lemma coeffVec_X_pow {n : ℕ} (i : Fin (n + 1)) :
    coeffVec n (X ^ (i : ℕ)) = Pi.single i (1 : ℂ) := by
  ext j
  simp [coeffVec, coeff_X_pow, Pi.single_apply, Fin.ext_iff, eq_comm]

lemma pairing_X_pow {n : ℕ} (T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (i j : Fin (n + 1)) : pairing T (X ^ (i : ℕ)) (X ^ (j : ℕ)) = T i j := by
  unfold pairing
  rw [coeffVec_X_pow, coeffVec_X_pow, mulVec_single_one]
  have hs : star (Pi.single i (1 : ℂ) : Fin (n + 1) → ℂ) =
      (Pi.single i 1 : Fin (n + 1) → ℂ) := by
    ext k
    by_cases h : i = k
    · subst k
      simp
    · simp [h]
  rw [hs, single_dotProduct, one_mul]
  rfl

section Kernel

variable {n : ℕ} {T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
variable (hpsd : T.PosSemidef) (htoe : IsToeplitz T) (hrank : T.rank = n)
variable {p : ℂ[X]} (hp : p.natDegree ≤ n) (hp0 : p ≠ 0)
variable (hpk : T *ᵥ coeffVec n p = 0)

include hpsd htoe hrank hp hp0 hpk

lemma kernel_of_vanishing {q : ℂ[X]} (hq : q.natDegree ≤ n)
    (hz : ∀ z ∈ p.roots.toFinset, q.eval z = 0) : T *ᵥ coeffVec n q = 0 := by
  by_cases hq0 : q = 0
  · subst q
    have hzv : coeffVec n (0 : ℂ[X]) = 0 := by ext i; simp [coeffVec]
    rw [hzv, mulVec_zero]
  have hsep := separable_of_kernel hpsd htoe hrank hp hp0 hpk
  have hdvd : p ∣ q := (IsAlgClosed.splits p).dvd_of_roots_le_roots hp0 <|
    (Multiset.le_iff_subset (Polynomial.nodup_roots hsep)).mpr (by
      intro z hz'
      exact (mem_roots hq0).mpr (hz z (Multiset.mem_toFinset.mpr hz')))
  obtain ⟨r, hr⟩ := hdvd
  have hr0 : r ≠ 0 := by
    intro h
    exact hq0 (by simp [hr, h])
  have hdegp := natDegree_eq_of_kernel hpsd htoe hrank hp hp0 hpk
  have hdegr : r.natDegree = 0 := by
    have hd := natDegree_mul hp0 hr0
    rw [← hr, hdegp] at hd
    omega
  have heq : q = C (r.coeff 0) * p := by
    calc
      q = p * r := hr
      _ = p * C (r.coeff 0) :=
        congrArg (fun f : ℂ[X] => p * f) (eq_C_of_natDegree_eq_zero hdegr)
      _ = C (r.coeff 0) * p := mul_comm _ _
  rw [heq, coeffVec_C_mul, mulVec_smul, hpk, smul_zero]

lemma basis_degree {z : ℂ} (hz : z ∈ p.roots.toFinset) :
    (Lagrange.basis p.roots.toFinset id z).natDegree < n := by
  have hc := (distinct_unit_circle_roots hpsd htoe hrank hp hp0 hpk).1
  rw [Lagrange.natDegree_basis (v := id) (fun _ _ _ _ h => h) hz, hc]
  have hn : 0 < n := by
    rw [← hc]
    exact Finset.card_pos.mpr ⟨z, hz⟩
  omega

lemma basis_shift_kernel {z : ℂ} (hz : z ∈ p.roots.toFinset) :
    T *ᵥ coeffVec n ((X - C z) * Lagrange.basis p.roots.toFinset id z) = 0 := by
  apply kernel_of_vanishing hpsd htoe hrank hp hp0 hpk
  · apply (natDegree_mul_le).trans
    have hd := basis_degree hpsd htoe hrank hp hp0 hpk hz
    simp only [natDegree_X_sub_C]
    omega
  · intro w hw
    by_cases h : z = w
    · simp [h]
    · simp only [eval_mul, eval_sub, eval_X, eval_C]
      have he : eval w (Lagrange.basis p.roots.toFinset id z) = 0 := by
        simpa only [id_eq] using (Lagrange.eval_basis_of_ne (v := id) h hw)
      rw [he, mul_zero]

omit htoe hrank hp hp0 hpk in
lemma pairing_eq_of_images {a a' b b' : ℂ[X]}
    (ha : T *ᵥ coeffVec n a = T *ᵥ coeffVec n a')
    (hb : T *ᵥ coeffVec n b = T *ᵥ coeffVec n b') :
    pairing T a b = pairing T a' b' := by
  have hl : star (coeffVec n a) ᵥ* T = star (coeffVec n a') ᵥ* T := by
    simpa only [star_mulVec, hpsd.isHermitian.eq] using congrArg star ha
  unfold pairing
  rw [hb, dotProduct_mulVec, hl, ← dotProduct_mulVec]

lemma basis_pairing_zero {z w : ℂ} (hz : z ∈ p.roots.toFinset)
    (hw : w ∈ p.roots.toFinset) (hzw : z ≠ w) :
    pairing T (Lagrange.basis p.roots.toFinset id z)
      (Lagrange.basis p.roots.toFinset id w) = 0 := by
  let a := Lagrange.basis p.roots.toFinset id z
  let b := Lagrange.basis p.roots.toFinset id w
  have ha := basis_shift_kernel hpsd htoe hrank hp hp0 hpk hz
  have hb := basis_shift_kernel hpsd htoe hrank hp hp0 hpk hw
  have hc (c : ℂ) (f : ℂ[X]) :
      coeffVec n ((X - C c) * f) = coeffVec n (X * f) - c • coeffVec n f := by
    ext i
    simp [coeffVec, sub_mul]
  rw [hc, mulVec_sub, mulVec_smul, sub_eq_zero] at ha hb
  have hl : star (coeffVec n (X * a)) ᵥ* T =
      star z • (star (coeffVec n a) ᵥ* T) := by
    simpa only [star_mulVec, hpsd.isHermitian.eq, star_smul] using congrArg star ha
  have he : pairing T (X * a) (X * b) = (star z * w) * pairing T a b := by
    unfold pairing
    calc
      star (coeffVec n (X * a)) ⬝ᵥ (T *ᵥ coeffVec n (X * b)) =
          w * (star (coeffVec n (X * a)) ⬝ᵥ (T *ᵥ coeffVec n b)) := by
        rw [hb, dotProduct_smul]
        rfl
      _ = w * ((star (coeffVec n (X * a)) ᵥ* T) ⬝ᵥ coeffVec n b) := by
        rw [dotProduct_mulVec]
      _ = w * (star z * ((star (coeffVec n a) ᵥ* T) ⬝ᵥ coeffVec n b)) := by
        rw [hl, smul_dotProduct]
        rfl
      _ = star z * w * (star (coeffVec n a) ⬝ᵥ (T *ᵥ coeffVec n b)) := by
        rw [← dotProduct_mulVec]
        ring
  rw [pairing_shift htoe a b
    (basis_degree hpsd htoe hrank hp hp0 hpk hz)
    (basis_degree hpsd htoe hrank hp hp0 hpk hw)] at he
  have hzn := (distinct_unit_circle_roots hpsd htoe hrank hp hp0 hpk).2 z hz
  have hz0 : z ≠ 0 := by
    intro h
    exact zero_ne_one (by simpa only [h, norm_zero] using hzn)
  have hunit : star z * z = 1 := by
    change starRingEnd ℂ z * z = 1
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hzn]
    norm_num
  have hne : star z * w - 1 ≠ 0 := by
    intro h
    have heq : star z * w = star z * z := (sub_eq_zero.mp h).trans hunit.symm
    exact hzw (mul_left_cancel₀ (star_ne_zero.mpr hz0) heq).symm
  apply (mul_eq_zero.mp (show (star z * w - 1) * pairing T a b = 0 by
    linear_combination -he)).resolve_left hne

lemma interpolant_degree (a : ℂ[X]) :
    (Lagrange.interpolate p.roots.toFinset id (fun z => a.eval z)).natDegree ≤ n := by
  rw [Lagrange.interpolate_apply]
  apply natDegree_sum_le_of_forall_le
  intro z hz
  exact (natDegree_C_mul_le _ _).trans
    (basis_degree hpsd htoe hrank hp hp0 hpk hz).le

lemma interpolant_image {a : ℂ[X]} (ha : a.natDegree ≤ n) :
    T *ᵥ coeffVec n a =
      T *ᵥ coeffVec n (Lagrange.interpolate p.roots.toFinset id (fun z => a.eval z)) := by
  have hd := interpolant_degree hpsd htoe hrank hp hp0 hpk a
  have hk := kernel_of_vanishing hpsd htoe hrank hp hp0 hpk
    ((natDegree_sub_le _ _).trans (max_le ha hd)) (by
      intro z hz
      have he : eval z (Lagrange.interpolate p.roots.toFinset id (fun z => a.eval z)) =
          a.eval z := by
        simpa only [id_eq] using (Lagrange.eval_interpolate_at_node (v := id)
          (fun z => a.eval z) (fun _ _ _ _ h => h) hz)
      rw [eval_sub, he, sub_self])
  rw [coeffVec_sub, mulVec_sub, sub_eq_zero] at hk
  exact hk

lemma pairing_expansion {a b : ℂ[X]} (ha : a.natDegree ≤ n) (hb : b.natDegree ≤ n) :
    pairing T a b = ∑ z ∈ p.roots.toFinset,
      star (a.eval z) * b.eval z *
        pairing T (Lagrange.basis p.roots.toFinset id z)
          (Lagrange.basis p.roots.toFinset id z) := by
  rw [pairing_eq_of_images hpsd
    (interpolant_image hpsd htoe hrank hp hp0 hpk ha)
    (interpolant_image hpsd htoe hrank hp hp0 hpk hb)]
  rw [Lagrange.interpolate_apply, pairing_sum_left]
  apply Finset.sum_congr rfl
  intro z hz
  rw [pairing_C_mul_left, Lagrange.interpolate_apply, pairing_sum_right,
    Finset.sum_eq_single z]
  · rw [pairing_C_mul_right]
    ring
  · intro w hw hwz
    rw [pairing_C_mul_right, basis_pairing_zero hpsd htoe hrank hp hp0 hpk hz hw
      (Ne.symm hwz), mul_zero]
  · intro h
    exact (h hz).elim

/-- The atomic weights are strictly positive, not merely nonnegative. -/
theorem basis_weight_pos {z : ℂ} (hz : z ∈ p.roots.toFinset) :
    0 < (pairing T (Lagrange.basis p.roots.toFinset id z)
      (Lagrange.basis p.roots.toFinset id z)).re := by
  have h := energy_pos_of_natDegree_lt hpsd htoe hrank
    (basis_degree hpsd htoe hrank hp hp0 hpk hz)
    (Lagrange.basis_ne_zero (v := id) (fun _ _ _ _ h => h) hz)
  exact (RCLike.pos_iff.mp h).1

omit htoe hrank hp hp0 hpk in
lemma pairing_self_real (q : ℂ[X]) :
    ((pairing T q q).re : ℂ) = pairing T q q := by
  have h := hpsd.dotProduct_mulVec_nonneg (coeffVec n q)
  have hi := (RCLike.nonneg_iff.mp h).2
  apply Complex.ext
  · rfl
  · exact hi.symm

/-- Corank-one atomic representation constructed from the kernel polynomial. -/
theorem atomic_representation_of_kernel : HasAtomicRepresentation T n := by
  let s := p.roots.toFinset
  let w : ℂ → ℝ := fun z =>
    (pairing T (Lagrange.basis s id z) (Lagrange.basis s id z)).re
  refine ⟨s, w, ?_, ?_, ?_⟩
  · exact (distinct_unit_circle_roots hpsd htoe hrank hp hp0 hpk).1
  · intro z hz
    exact ⟨(distinct_unit_circle_roots hpsd htoe hrank hp hp0 hpk).2 z hz,
      basis_weight_pos hpsd htoe hrank hp hp0 hpk hz⟩
  · intro i j
    rw [← pairing_X_pow T i j,
      pairing_expansion hpsd htoe hrank hp hp0 hpk
        ((natDegree_X_pow_le _).trans (Nat.le_of_lt_succ i.isLt))
        ((natDegree_X_pow_le _).trans (Nat.le_of_lt_succ j.isLt))]
    apply Finset.sum_congr rfl
    intro z hz
    dsimp only [w, s]
    rw [pairing_self_real hpsd, eval_pow, eval_X, eval_pow, eval_X]
    ring

end Kernel

/-- Every positive Toeplitz matrix of size n+1 and rank n has a positive
n-atom unit-circle representation. No kernel vector is supplied as an input. -/
theorem exists_atomic_representation {n : ℕ}
    {T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hpsd : T.PosSemidef) (htoe : IsToeplitz T) (hrank : T.rank = n) :
    HasAtomicRepresentation T n := by
  have hdim := kernel_finrank hrank
  have hk : LinearMap.ker T.mulVecLin ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hdim
    exact zero_ne_one hdim
  obtain ⟨v, hvk, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  let p := ofFn (n + 1) v
  have hcv : coeffVec n p = v := by
    ext i
    exact ofFn_coeff_eq_val_of_lt v i.isLt
  have hp0 : p ≠ 0 := by
    intro h
    apply hv0
    have hh := congrArg (coeffVec n) h
    simpa only [hcv, coeffVec, coeff_zero, Pi.zero_def] using hh
  apply atomic_representation_of_kernel hpsd htoe hrank
    (Nat.le_of_lt_succ (ofFn_natDegree_lt (by omega) v)) hp0
  change T *ᵥ coeffVec n p = 0
  rw [hcv]
  exact hvk


end Reinmann.ToeplitzAtomic
