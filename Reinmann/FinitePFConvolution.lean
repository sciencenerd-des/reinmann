/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.FinitePFBaseline
import Reinmann.FinitePFStrict
import Reinmann.MatrixMinorProduct
import Reinmann.ToeplitzComplement
import Mathlib.Data.Finset.Sort

/-! Product closure for all ordered Toeplitz minors through a fixed rank.
This is the algebraic product step, not the polynomial sector theorem. -/
noncomputable section
namespace Reinmann.FinitePFConvolution
open Finset Matrix

/-- An injective finite list in a linear order can be put in increasing order
by permuting its positions. -/
theorem exists_sort_perm {α : Type*} [LinearOrder α] {k : ℕ}
    {p : Fin k → α} (hp : Function.Injective p) :
    ∃ σ : Equiv.Perm (Fin k), StrictMono (p ∘ σ) := by
  classical
  let s := Finset.univ.image p
  have hs : s.card = k := by
    rw [Finset.card_image_of_injective _ hp]
    exact Fintype.card_fin k
  let f (i : Fin k) : s := ⟨p i, Finset.mem_image.mpr ⟨i, mem_univ i, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j h
      exact hp (congrArg Subtype.val h)
    · rintro ⟨y, hy⟩
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hy
      exact ⟨i, Subtype.ext hi⟩
  let e : Fin k ≃ s := Equiv.ofBijective f hf
  let σ : Equiv.Perm (Fin k) := (s.orderIsoOfFin hs).toEquiv.trans e.symm
  have hσ (i : Fin k) : p (σ i) = s.orderEmbOfFin hs i := by
    change ((e (e.symm (s.orderIsoOfFin hs i))) : α) = _
    rw [e.apply_symm_apply]
    rfl
  refine ⟨σ, ?_⟩
  intro i j hij
  change p (σ i) < p (σ j)
  rw [hσ, hσ]
  exact (s.orderEmbOfFin hs).strictMono hij

/-- Ordered-minor nonnegativity makes every term of Cauchy–Binet nonnegative.
Repeated indices vanish; sorting injective indices cancels both signs. -/
theorem det_mul_nonneg {k N : ℕ}
    (A : Matrix (Fin k) (Fin N) ℝ) (B : Matrix (Fin N) (Fin k) ℝ)
    (hA : ∀ p : Fin k → Fin N, StrictMono p → 0 ≤ (A.submatrix id p).det)
    (hB : ∀ p : Fin k → Fin N, StrictMono p → 0 ≤ (B.submatrix p id).det) :
    0 ≤ (A * B).det := by
  have hterm (p : Fin k → Fin N) :
      0 ≤ (A.submatrix id p).det * (B.submatrix p id).det := by
    classical
    by_cases hp : Function.Injective p
    · obtain ⟨σ, hσ⟩ := exists_sort_perm hp
      rw [← MatrixMinorProduct.minor_pair_permute A B p σ]
      exact mul_nonneg (hA _ hσ) (hB _ hσ)
    · obtain ⟨i, j, heq, hne⟩ := Function.not_injective_iff.mp hp
      have hz : (B.submatrix p id).det = 0 :=
        Matrix.det_zero_of_row_eq hne (by ext l; simp [heq])
      rw [hz, mul_zero]
  have h := Finset.sum_nonneg (fun p (_ : p ∈ Finset.univ) => hterm p)
  rw [← MatrixMinorProduct.factorial_mul_det_mul A B] at h
  have hfac : (0 : ℝ) < ((Fintype.card (Fin k)).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (Fintype.card (Fin k))
  exact (mul_nonneg_iff_of_pos_left hfac).mp h

/-- Multiplication of ordinary formal power series preserves every arbitrary
Toeplitz minor through the given rank. No rank is lost. -/
theorem finitePF_mul {f g : PowerSeries ℝ} {r : ℕ}
    (hf : FinitePF (fun n => PowerSeries.coeff n f) r)
    (hg : FinitePF (fun n => PowerSeries.coeff n g) r) :
    FinitePF (fun n => PowerSeries.coeff n (f * g)) r := by
  classical
  intro k hk rows cols hr hc
  let N := (∑ i, rows i) + (∑ i, cols i) + 1
  have hrow (i : Fin k) : rows i < N := by
    have h : rows i ≤ ∑ j, rows j :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)
    dsimp [N]
    omega
  have hcol (i : Fin k) : cols i < N := by
    have h : cols i ≤ ∑ j, cols j :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)
    dsimp [N]
    omega
  let rr (i : Fin k) : Fin N := ⟨rows i, hrow i⟩
  let cc (i : Fin k) : Fin N := ⟨cols i, hcol i⟩
  let A := (ToeplitzComplement.toeplitz f N).submatrix rr id
  let B := (ToeplitzComplement.toeplitz g N).submatrix id cc
  have hm : (Matrix.of fun i j => sequenceToeplitz
      (fun n => PowerSeries.coeff n (f * g)) (rows i) (cols j)) = A * B := by
    change (ToeplitzComplement.toeplitz (f * g) N).submatrix rr cc = _
    rw [ToeplitzComplement.toeplitz_mul]
    ext i j
    simp [A, B, Matrix.mul_apply]
  rw [hm]
  apply det_mul_nonneg
  · intro p hp
    exact hf k hk rows (fun i => (p i).val) hr
      (fun _ _ hij => hp hij)
  · intro p hp
    exact hg k hk (fun i => (p i).val) cols
      (fun _ _ hij => hp hij) hc

/-- Sequence version: the ordinary Cauchy convolution of two PF-r sequences
is PF-r. This is not a statement about factorial-weighted Jensen coefficients. -/
theorem finitePF_convolution {a b : ℕ → ℝ} {r : ℕ}
    (ha : FinitePF a r) (hb : FinitePF b r) :
    FinitePF (fun n => ∑ p ∈ Finset.antidiagonal n, a p.1 * b p.2) r := by
  have h := finitePF_mul (f := PowerSeries.mk a) (g := PowerSeries.mk b)
    (by simpa only [PowerSeries.coeff_mk] using ha)
    (by simpa only [PowerSeries.coeff_mk] using hb)
  simpa only [PowerSeries.coeff_mul, PowerSeries.coeff_mk] using h

/-- In particular the ordinary coefficient sequences of real polynomials are
closed under multiplication at each fixed PF rank. -/
theorem finitePF_polynomial_mul {f g : Polynomial ℝ} {r : ℕ}
    (hf : FinitePF (fun n => f.coeff n) r)
    (hg : FinitePF (fun n => g.coeff n) r) :
    FinitePF (fun n => (f * g).coeff n) r := by
  have h := finitePF_mul (f := (f : PowerSeries ℝ)) (g := (g : PowerSeries ℝ))
    (by simpa only [Polynomial.coeff_coe] using hf)
    (by simpa only [Polynomial.coeff_coe] using hg)
  simpa only [← Polynomial.coe_mul, Polynomial.coeff_coe] using h

/-- Ordered minors of the infinite identity are either zero or one. -/
theorem ordered_delta_det {k : ℕ} {rows cols : Fin k → ℕ}
    (hr : StrictMono rows) (hc : StrictMono cols) :
    (Matrix.of fun i j => if rows i = cols j then (1 : ℝ) else 0).det =
      if rows = cols then 1 else 0 := by
  classical
  by_cases he : rows = cols
  · subst cols
    rw [if_pos rfl]
    have hm : (Matrix.of fun i j => if rows i = rows j then (1 : ℝ) else 0) = 1 := by
      ext i j
      simp only [Matrix.of_apply, Matrix.one_apply, hr.injective.eq_iff]
    rw [hm, Matrix.det_one]
  · rw [if_neg he, Matrix.det_apply']
    apply Finset.sum_eq_zero
    intro σ _
    have hn : ¬ ∀ i, rows (σ i) = cols i := by
      intro hall
      have hrange : Set.range rows = Set.range cols := by
        calc
          Set.range rows = Set.range (rows ∘ σ) :=
            (σ.surjective.range_comp rows).symm
          _ = Set.range cols := congrArg Set.range (funext hall)
      exact he ((hr.range_inj hc).mp hrange)
    obtain ⟨i, hi⟩ := not_forall.mp hn
    have hz : (∏ j, (Matrix.of fun i j =>
        if rows i = cols j then (1 : ℝ) else 0) (σ j) j) = 0 :=
      Finset.prod_eq_zero (mem_univ i) (by simp only [Matrix.of_apply, if_neg hi])
    rw [hz, mul_zero]

/-- The unit ordinary power series is PF at every finite rank. -/
theorem finitePF_one (r : ℕ) :
    FinitePF (fun n => PowerSeries.coeff n (1 : PowerSeries ℝ)) r := by
  intro k _ rows cols hr hc
  have he (i j : ℕ) : sequenceToeplitz
      (fun n => PowerSeries.coeff n (1 : PowerSeries ℝ)) i j =
      if i = j then 1 else 0 := by
    simp only [sequenceToeplitz, PowerSeries.coeff_one]
    split_ifs <;> simp_all
    omega
  simp only [he, ordered_delta_det hr hc]
  split_ifs <;> norm_num

/-- Every finite product of ordinary PF-r power series remains PF-r. -/
theorem finitePF_prod {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℝ) {r : ℕ}
    (hf : ∀ i ∈ s, FinitePF (fun n => PowerSeries.coeff n (f i)) r) :
    FinitePF (fun n => PowerSeries.coeff n (∏ i ∈ s, f i)) r := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using finitePF_one r
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact finitePF_mul (hf i (mem_insert_self i s))
      (ih (fun j hj => hf j (mem_insert_of_mem hj)))

/-- Real polynomial factors can be assembled without a rank loss. -/
theorem finitePF_polynomial_prod {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℝ)
    {r : ℕ} (hf : ∀ i ∈ s, FinitePF (fun n => (f i).coeff n) r) :
    FinitePF (fun n => (∏ i ∈ s, f i).coeff n) r := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.prod_empty, Polynomial.coeff_one, PowerSeries.coeff_one] using
      finitePF_one r
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact finitePF_polynomial_mul (hf i (mem_insert_self i s))
      (ih (fun j hj => hf j (mem_insert_of_mem hj)))

/-- The earlier bidiagonal row-step theorem gives linear-factor preservation
in the natural-index `FinitePF` interface. -/
theorem finitePF_linearFactor {a : ℕ → ℝ} {r : ℕ} (ha : FinitePF a r)
    {t : ℝ} (ht : 0 ≤ t) : FinitePF (FinitePFStrict.linearFactor t a) r := by
  intro k hk rows cols hr hc
  have h := FinitePFStrict.orderedNonneg_rowStep
    (FinitePFStrict.orderedNonneg_intToeplitz ha) ht
  have hrows : StrictMono (fun i => (rows i : ℤ)) := by
    intro i j hij
    change (rows i : ℤ) < (rows j : ℤ)
    exact_mod_cast hr hij
  have hh := h k hk (fun i => (rows i : ℤ)) cols hrows hc
  rw [← FinitePFStrict.intToeplitz_linearFactor] at hh
  simpa only [FinitePFStrict.intToeplitz, Int.natCast_nonneg, if_true,
    Int.toNat_natCast] using hh

/-- Every nonnegative linear factor is PF at every rank. This finishes the
linear building block of the polynomial sector route. -/
theorem finitePF_linear_polynomial {t : ℝ} (ht : 0 ≤ t) (r : ℕ) :
    FinitePF (fun n => (1 + Polynomial.C t * Polynomial.X : Polynomial ℝ).coeff n) r := by
  have h := finitePF_linearFactor (finitePF_one r) ht
  convert h using 1
  funext n
  cases n with
  | zero => simp [FinitePFStrict.linearFactor, Polynomial.coeff_one]
  | succ n =>
    cases n with
    | zero => simp [FinitePFStrict.linearFactor, Polynomial.coeff_one]
    | succ n => simp [FinitePFStrict.linearFactor, Polynomial.coeff_one]

end Reinmann.FinitePFConvolution
