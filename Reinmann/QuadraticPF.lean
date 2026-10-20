/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.FinitePFConvolution
import Reinmann.ToeplitzQuadraticChebyshev
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! Arbitrary minors for the quadratic sector building block. -/
noncomputable section
namespace Reinmann.QuadraticPF
open Finset Matrix

def entry (c : ℝ) (i j : ℤ) : ℝ :=
  if i = j then 2 * c else if i + 1 = j ∨ j + 1 = i then 1 else 0

def minor {k : ℕ} (c : ℝ) (rows cols : Fin k → ℤ) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => entry c (rows i) (cols j)

private def leftIndex (k t : ℕ) (ht : t ≤ k) (i : Fin t) : Fin k :=
  ⟨i.val, lt_of_lt_of_le i.isLt ht⟩

private def rightIndex (k t : ℕ) (ht : t ≤ k) (i : Fin (k - t)) : Fin k :=
  ⟨t + i.val, by have := i.isLt; omega⟩

private theorem det_cut {k t : ℕ} (ht : t ≤ k) (M : Matrix (Fin k) (Fin k) ℝ)
    (hcut : (∀ i j, M (leftIndex k t ht i) (rightIndex k t ht j) = 0) ∨
      (∀ i j, M (rightIndex k t ht i) (leftIndex k t ht j) = 0)) :
    M.det = (M.submatrix (leftIndex k t ht) (leftIndex k t ht)).det *
      (M.submatrix (rightIndex k t ht) (rightIndex k t ht)).det := by
  let e : Fin t ⊕ Fin (k - t) ≃ Fin k :=
    finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le ht))
  have hel (i : Fin t) : e (Sum.inl i) = leftIndex k t ht i := by
    apply Fin.ext
    rfl
  have her (i : Fin (k - t)) : e (Sum.inr i) = rightIndex k t ht i := by
    apply Fin.ext
    rfl
  have hm : M.submatrix e e = Matrix.fromBlocks
      (M.submatrix (leftIndex k t ht) (leftIndex k t ht))
      (M.submatrix (leftIndex k t ht) (rightIndex k t ht))
      (M.submatrix (rightIndex k t ht) (leftIndex k t ht))
      (M.submatrix (rightIndex k t ht) (rightIndex k t ht)) := by
    ext i j
    cases i <;> cases j <;> simp [hel, her]
  rw [← Matrix.det_submatrix_equiv_self e M, hm]
  rcases hcut with hu | hl
  · have hz : M.submatrix (leftIndex k t ht) (rightIndex k t ht) = 0 := by
      ext i j
      exact hu i j
    rw [hz, Matrix.det_fromBlocks_zero₁₂]
  · have hz : M.submatrix (rightIndex k t ht) (leftIndex k t ht) = 0 := by
      ext i j
      exact hl i j
    rw [hz, Matrix.det_fromBlocks_zero₂₁]

private theorem lower_from_zero {n : ℕ} {rows : Fin (n + 1) → ℤ}
    (hr : StrictMono rows) (i : Fin (n + 1)) : rows 0 + (i.val : ℤ) ≤ rows i := by
  induction i using Fin.induction with
  | zero => simp
  | succ i ih =>
    have h := hr (show i.castSucc < i.succ from Fin.castSucc_lt_succ)
    simp only [Fin.val_castSucc] at ih
    simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]
    omega

private theorem entry_lattice {k : ℕ} (c : ℝ) (a : ℤ) (i j : Fin k) :
    entry c (a + (i.val : ℤ)) (a + (j.val : ℤ)) =
      ToeplitzQuadraticChebyshev.tri k c i j := by
  have hd : a + (i.val : ℤ) = a + (j.val : ℤ) ↔ i.val = j.val := by omega
  have ho : ((a + (i.val : ℤ)) + 1 = a + (j.val : ℤ) ∨
      (a + (j.val : ℤ)) + 1 = a + (i.val : ℤ)) ↔
      i.val + 1 = j.val ∨ j.val + 1 = i.val := by omega
  simp only [entry, ToeplitzQuadraticChebyshev.tri, hd, ho]

private theorem entry_nonneg {c : ℝ} (hc : 0 ≤ 2 * c) (i j : ℤ) :
    0 ≤ entry c i j := by
  unfold entry
  split_ifs <;> positivity

private theorem entry_zero_gap (c : ℝ) {i j : ℤ} (h : i + 1 < j ∨ j + 1 < i) :
    entry c i j = 0 := by
  have hd : i ≠ j := by omega
  have ho : ¬ (i + 1 = j ∨ j + 1 = i) := by omega
  simp only [entry, if_neg hd, if_neg ho]

/-- Every ordered minor of a symmetric Jacobi matrix is nonnegative if all
contiguous principal blocks up to its size are nonnegative. This theorem is
about arbitrary row and column selections, not only contiguous minors. -/
theorem arbitrary_minor_nonneg_of_tridiagonal (c : ℝ) (k : ℕ)
    (htri : ∀ m ≤ k, 0 ≤ (ToeplitzQuadraticChebyshev.tri m c).det)
    (rows cols : Fin k → ℤ) (hr : StrictMono rows) (hc : StrictMono cols) :
    0 ≤ (minor c rows cols).det := by
  classical
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => simp [Matrix.det_fin_zero]
    | succ n =>
      have hdiag : 0 ≤ 2 * c := by
        simpa [Matrix.det_fin_one] using htri 1 (by omega)
      have htail : 0 ≤ ((minor c rows cols).submatrix Fin.succ Fin.succ).det :=
        ih n (by omega) (fun m hm => htri m (by omega))
          (rows ∘ Fin.succ) (cols ∘ Fin.succ)
          (hr.comp (Fin.strictMono_succ)) (hc.comp (Fin.strictMono_succ))
      by_cases he : rows 0 = cols 0
      · by_cases hall : ∀ i, rows i = rows 0 + (i.val : ℤ) ∧
            cols i = cols 0 + (i.val : ℤ)
        · have hm : minor c rows cols = ToeplitzQuadraticChebyshev.tri (n + 1) c := by
            ext i j
            change entry c (rows i) (cols j) = _
            rw [(hall i).1, (hall j).2, ← he]
            exact entry_lattice c (rows 0) i j
          rw [hm]
          exact htri _ le_rfl
        · let s := Finset.univ.filter (fun i : Fin (n + 1) =>
            ¬ (rows i = rows 0 + (i.val : ℤ) ∧ cols i = cols 0 + (i.val : ℤ)))
          have hs : s.Nonempty := by
            obtain ⟨i, hi⟩ := not_forall.mp hall
            exact ⟨i, mem_filter.mpr ⟨mem_univ i, hi⟩⟩
          let b := s.min' hs
          have hb : ¬ (rows b = rows 0 + (b.val : ℤ) ∧
              cols b = cols 0 + (b.val : ℤ)) := (mem_filter.mp (s.min'_mem hs)).2
          have hbefore (i : Fin (n + 1)) (hi : i < b) :
              rows i = rows 0 + (i.val : ℤ) ∧ cols i = cols 0 + (i.val : ℤ) := by
            by_contra hn
            have hle : b ≤ i := s.min'_le i (mem_filter.mpr ⟨mem_univ i, hn⟩)
            exact (not_le_of_gt hi) hle
          have hbpos : 0 < b.val := by
            by_contra hn
            have hbzero : b = 0 := Fin.ext (by
              simpa only [Fin.val_zero] using Nat.eq_zero_of_not_pos hn)
            simp [hbzero] at hb
          have hble : b.val ≤ n + 1 := Nat.le_of_lt b.isLt
          let L := leftIndex (n + 1) b.val hble
          let R := rightIndex (n + 1) b.val hble
          have hL (i : Fin b.val) :
              rows (L i) = rows 0 + (i.val : ℤ) ∧
              cols (L i) = cols 0 + (i.val : ℤ) :=
            hbefore (L i) (show (L i).val < b.val from i.isLt)
          have hleft : (minor c rows cols).submatrix L L =
              ToeplitzQuadraticChebyshev.tri b.val c := by
            ext i j
            change entry c (rows (L i)) (cols (L j)) = _
            rw [(hL i).1, (hL j).2, ← he]
            exact entry_lattice c (rows 0) i j
          have hright : 0 ≤ ((minor c rows cols).submatrix R R).det := by
            apply ih (n + 1 - b.val) (by omega)
              (fun m hm => htri m (by omega)) (rows ∘ R) (cols ∘ R)
            · intro i j hij
              apply hr
              change b.val + i.val < b.val + j.val
              omega
            · intro i j hij
              apply hc
              change b.val + i.val < b.val + j.val
              omega
          have hrlo := lower_from_zero hr b
          have hclo := lower_from_zero hc b
          have hgap : rows 0 + (b.val : ℤ) < rows b ∨
              cols 0 + (b.val : ℤ) < cols b := by omega
          have hcut : (∀ i j, (minor c rows cols) (L i) (R j) = 0) ∨
              (∀ i j, (minor c rows cols) (R i) (L j) = 0) := by
            rcases hgap with hrg | hcg
            · right
              intro i j
              have hbr : b ≤ R i := by change b.val ≤ b.val + i.val; omega
              have hrr := hr.monotone hbr
              have hl := (hL j).2
              apply entry_zero_gap c
              right
              have hj := j.isLt
              change cols (L j) + 1 < rows (R i)
              omega
            · left
              intro i j
              have hbr : b ≤ R j := by change b.val ≤ b.val + j.val; omega
              have hcc := hc.monotone hbr
              have hl := (hL i).1
              apply entry_zero_gap c
              left
              have hi := i.isLt
              change rows (L i) + 1 < cols (R j)
              omega
          rw [det_cut hble _ hcut, hleft]
          exact mul_nonneg (htri _ hble) hright
      · rcases lt_or_gt_of_ne he with hlt | hgt
        · have hz (j : Fin n) : (minor c rows cols) 0 j.succ = 0 := by
            have h := hc (show (0 : Fin (n + 1)) < j.succ from Nat.succ_pos j.val)
            apply entry_zero_gap c
            left
            omega
          rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
          simp only [Fin.val_zero, pow_zero, one_mul, hz, mul_zero, zero_mul,
            Finset.sum_const_zero, add_zero, Fin.succAbove_zero]
          exact mul_nonneg (entry_nonneg hdiag _ _) htail
        · have hz (i : Fin n) : (minor c rows cols) i.succ 0 = 0 := by
            have h := hr (show (0 : Fin (n + 1)) < i.succ from Nat.succ_pos i.val)
            apply entry_zero_gap c
            right
            omega
          rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
          simp only [Fin.val_zero, pow_zero, one_mul, hz, mul_zero, zero_mul,
            Finset.sum_const_zero, add_zero, Fin.succAbove_zero]
          exact mul_nonneg (entry_nonneg hdiag _ _) htail

/-- The closed angular range includes the sharp boundary, where the last
allowed Chebyshev block may have determinant zero. -/
theorem tridiagonal_nonneg {r : ℕ} {phi : ℝ} (h0 : 0 ≤ phi)
    (hphi : phi ≤ Real.pi / ((r : ℝ) + 1)) (m : ℕ) (hm : m ≤ r) :
    0 ≤ (ToeplitzQuadraticChebyshev.tri m (Real.cos phi)).det := by
  by_cases hm0 : m = 0
  · subst m
    simp [Matrix.det_fin_zero]
  by_cases hp0 : phi = 0
  · rw [hp0, Real.cos_zero, ToeplitzQuadraticChebyshev.determinant_eq_U,
      Polynomial.Chebyshev.U_eval_one]
    positivity
  have hp : 0 < phi := lt_of_le_of_ne h0 (Ne.symm hp0)
  have hr : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
  have hden : 0 < (r : ℝ) + 1 := by positivity
  have hb := (le_div_iff₀ hden).mp hphi
  have hplt : phi < Real.pi := by nlinarith [Real.pi_pos]
  have hs := Real.sin_pos_of_pos_of_lt_pi hp hplt
  rw [ToeplitzQuadraticChebyshev.determinant_cos m phi (ne_of_gt hs)]
  apply div_nonneg _ hs.le
  apply Real.sin_nonneg_of_nonneg_of_le_pi
  · positivity
  · have hmr : (m : ℝ) ≤ r := by exact_mod_cast hm
    nlinarith

def polynomial (c : ℝ) : Polynomial ℝ :=
  1 + Polynomial.C (2 * c) * Polynomial.X + Polynomial.X ^ 2

theorem polynomial_coeff (c : ℝ) (n : ℕ) :
    (polynomial c).coeff n = if n = 0 then 1 else if n = 1 then 2 * c
      else if n = 2 then 1 else 0 := by
  rcases n with _ | _ | _ | n
  all_goals simp [polynomial, Polynomial.coeff_one, Polynomial.coeff_X_pow]

/-- The integer Jacobi convention is exactly the ordinary quadratic Toeplitz
convention after shifting the row indices by one. -/
theorem toeplitz_entry (c : ℝ) (i j : ℕ) :
    sequenceToeplitz (fun n => (polynomial c).coeff n) i j =
      entry c ((i : ℤ) - 1) (j : ℤ) := by
  simp only [sequenceToeplitz, polynomial_coeff, entry]
  split_ifs <;> first | rfl | omega

/-- Schoenberg's quadratic sector building block, for all arbitrary ordered
minors through rank r, with its boundary angle included. -/
theorem finitePF_quadratic {r : ℕ} {phi : ℝ} (h0 : 0 ≤ phi)
    (hphi : phi ≤ Real.pi / ((r : ℝ) + 1)) :
    FinitePF (fun n => (polynomial (Real.cos phi)).coeff n) r := by
  intro k hk rows cols hr hc
  simp only [toeplitz_entry]
  apply arbitrary_minor_nonneg_of_tridiagonal (Real.cos phi) k
    (fun m hm => tridiagonal_nonneg h0 hphi m (hm.trans hk))
    (fun i => (rows i : ℤ) - 1) (fun i => (cols i : ℤ))
  · intro i j hij
    change (rows i : ℤ) - 1 < (rows j : ℤ) - 1
    have h : (rows i : ℤ) < (rows j : ℤ) := by exact_mod_cast hr hij
    omega
  · intro i j hij
    change (cols i : ℤ) < (cols j : ℤ)
    exact_mod_cast hc hij

/-- Positive dilation of the variable preserves finite PF of ordinary
coefficients. Row and column powers account for every arbitrary minor. -/
theorem finitePF_pos_rescale {a : ℕ → ℝ} {r : ℕ} (ha : FinitePF a r)
    {t : ℝ} (ht : 0 < t) : FinitePF (fun n => t ^ n * a n) r := by
  have he (i j : ℕ) : sequenceToeplitz (fun n => t ^ n * a n) i j =
      t ^ i * ((t ^ j)⁻¹ * sequenceToeplitz a i j) := by
    by_cases hji : j ≤ i
    · simp only [sequenceToeplitz, if_pos hji]
      rw [pow_sub₀ t ht.ne' hji]
      ring
    · unfold sequenceToeplitz
      rw [if_neg hji, if_neg hji]
      simp only [mul_zero]
  intro k hk rows cols hr hc
  simp only [he]
  rw [Matrix.det_mul_column]
  change 0 ≤ (∏ i, t ^ rows i) *
    (Matrix.of fun i j => (t ^ cols j)⁻¹ * sequenceToeplitz a (rows i) (cols j)).det
  rw [Matrix.det_mul_row]
  apply mul_nonneg (Finset.prod_nonneg (fun i _ => pow_nonneg ht.le _))
  exact mul_nonneg (Finset.prod_nonneg (fun i _ => inv_nonneg.mpr
    (pow_nonneg ht.le _))) (ha k hk rows cols hr hc)

def scaledPolynomial (c t : ℝ) : Polynomial ℝ :=
  1 + Polynomial.C (2 * c * t) * Polynomial.X + Polynomial.C (t ^ 2) * Polynomial.X ^ 2

theorem scaledPolynomial_coeff (c t : ℝ) (n : ℕ) :
    (scaledPolynomial c t).coeff n = t ^ n * (polynomial c).coeff n := by
  rcases n with _ | _ | _ | n
  all_goals simp only [scaledPolynomial, polynomial, Polynomial.coeff_add,
    Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_one,
    Polynomial.coeff_X_pow]
  all_goals simp <;> ring

/-- The quadratic criterion permits arbitrary positive root moduli. -/
theorem finitePF_scaled_quadratic {r : ℕ} {phi t : ℝ} (h0 : 0 ≤ phi)
    (hphi : phi ≤ Real.pi / ((r : ℝ) + 1)) (ht : 0 < t) :
    FinitePF (fun n => (scaledPolynomial (Real.cos phi) t).coeff n) r := by
  simpa only [scaledPolynomial_coeff] using
    finitePF_pos_rescale (finitePF_quadratic h0 hphi) ht

/-- A conjugate root pair in the closed Schoenberg sector gives a real PF-r
quadratic, with arbitrary modulus. No simplicity or strict-angle assumption
is used. The polynomial is the actual monic conjugate-pair factor. -/
theorem finitePF_conjugate_pair {r : ℕ} {z : ℂ} (hz : z ≠ 0)
    (hsector : Real.pi - Real.pi / ((r : ℝ) + 1) ≤ |Complex.arg z|) :
    FinitePF (fun n => (Polynomial.X ^ 2 - Polynomial.C (2 * z.re) * Polynomial.X +
      Polynomial.C (‖z‖ ^ 2) : Polynomial ℝ).coeff n) r := by
  let phi := Real.pi - |Complex.arg z|
  have h0 : 0 ≤ phi := sub_nonneg.mpr (Complex.abs_arg_le_pi z)
  have hphi : phi ≤ Real.pi / ((r : ℝ) + 1) := by dsimp [phi]; linarith
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hn0 : ‖z‖ ≠ 0 := ne_of_gt hn
  have hcos : Real.cos phi = -z.re / ‖z‖ := by
    rw [show phi = Real.pi - |Complex.arg z| from rfl,
      Real.cos_pi_sub, Real.cos_abs, Complex.cos_arg hz]
    ring
  have h := finitePF_nonneg_scale
    (finitePF_scaled_quadratic h0 hphi (inv_pos.mpr hn)) (sq_nonneg ‖z‖)
  have he (n : ℕ) :
      (Polynomial.X ^ 2 - Polynomial.C (2 * z.re) * Polynomial.X +
        Polynomial.C (‖z‖ ^ 2) : Polynomial ℝ).coeff n =
        ‖z‖ ^ 2 * (scaledPolynomial (Real.cos phi) ‖z‖⁻¹).coeff n := by
    rcases n with _ | _ | _ | n
    all_goals simp only [scaledPolynomial, hcos, Polynomial.coeff_add,
      Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X,
      Polynomial.coeff_one, Polynomial.coeff_X_pow, Polynomial.coeff_C]
    all_goals simp <;> field_simp [hn0]
  simpa only [← he] using h

end Reinmann.QuadraticPF
