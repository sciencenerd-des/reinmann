/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.SplitPairDeterminant
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-! Finite algebra for analytic-error rows in a pole-dominance determinant.
Repeated poles must cancel before estimating the determinant. -/
noncomputable section
namespace Reinmann.SplitPairMixedRows
open Finset Matrix

/-- A normalized selected product is largest on the prescribed top set.
No strict ordering among the top moduli is required. -/
theorem normalized_subset_product_bound {ι : Type*} [DecidableEq ι]
    (β : ι → ℝ) (top I : Finset ι) (h0 : ∀ i, 0 ≤ β i)
    (htop : ∀ i ∈ top, 1 ≤ β i) (hout : ∀ i ∉ top, β i ≤ 1) :
    (∏ i ∈ I, β i) ≤ ∏ i ∈ top, β i := by
  have hsub := prod_le_prod_of_subset_of_one_le (inter_subset_right (s₁ := I) (s₂ := top))
    (fun i _ => h0 i) (fun i hi _ => htop i hi)
  have htail : (∏ i ∈ I \ (I ∩ top), β i) ≤ 1 := by
    apply prod_le_one (fun i _ => h0 i)
    intro i hi
    apply hout i
    intro hit
    exact (mem_sdiff.mp hi).2 (mem_inter.mpr ⟨(mem_sdiff.mp hi).1, hit⟩)
  rw [← prod_sdiff (inter_subset_left (s₁ := I) (s₂ := top))]
  exact (mul_le_mul_of_nonneg_right htail (prod_nonneg (fun i _ => h0 i))).trans
    (by simpa using hsub)

/-- The ordered subset-product estimate with exactly k missing pole factors. -/
theorem ordered_subset_product_bound {ι : Type*} [DecidableEq ι]
    (α : ι → ℝ) (top I : Finset ι) {d : ℝ} (hd : 0 < d)
    (h0 : ∀ i, 0 ≤ α i) (htop : ∀ i ∈ top, d ≤ α i)
    (hout : ∀ i ∉ top, α i ≤ d) {k : ℕ} (hcard : I.card + k = top.card) :
    (∏ i ∈ I, α i) * d ^ k ≤ ∏ i ∈ top, α i := by
  have hn := normalized_subset_product_bound (fun i => α i / d) top I
    (fun i => div_nonneg (h0 i) hd.le)
    (fun i hi => (one_le_div hd).mpr (htop i hi))
    (fun i hi => (div_le_one hd).mpr (hout i hi))
  simp only [prod_div_distrib, prod_const] at hn
  have h := (div_le_div_iff₀ (pow_pos hd _) (pow_pos hd _)).mp hn
  rw [← hcard, pow_add] at h
  apply (mul_le_mul_iff_left₀ (pow_pos hd I.card)).mp
  nlinarith only [h]

/-- Multiplying the missing factors by the analytic row rate gives q^k. -/
theorem mixed_product_rate {ι : Type*} [DecidableEq ι]
    (α : ι → ℝ) (top I : Finset ι) {d ρ : ℝ} (hd : 0 < d) (hρ : 0 ≤ ρ)
    (h0 : ∀ i, 0 ≤ α i) (htop : ∀ i ∈ top, d ≤ α i)
    (hout : ∀ i ∉ top, α i ≤ d) {k : ℕ} (hcard : I.card + k = top.card) :
    (∏ i ∈ I, α i) * ρ ^ k ≤ (∏ i ∈ top, α i) * (ρ / d) ^ k := by
  have h := ordered_subset_product_bound α top I hd h0 htop hout hcard
  have h' := mul_le_mul_of_nonneg_right h (pow_nonneg hρ k)
  rw [div_pow, ← mul_div_assoc]
  apply (le_div_iff₀ (pow_pos hd k)).mpr
  nlinarith only [h']

/-- Multilinearity allows each error row to depend on its row index. -/
theorem row_expansion {ι : Type*} [Fintype ι] [DecidableEq ι] {s : ℕ}
    (rows : Fin s → ι → Fin s → ℂ) :
    Matrix.det (fun i j => ∑ l, rows i l j) =
      ∑ e : Fin s → ι, Matrix.det (fun i j => rows i (e i) j) := by
  rw [show (fun i j => ∑ l, rows i l j) = (fun i => ∑ l, rows i l) by
    ext i j
    simp only [Finset.sum_apply]]
  change Matrix.detRowAlternating.toMultilinearMap (fun i => ∑ l, rows i l) = _
  exact Matrix.detRowAlternating.toMultilinearMap.map_sum rows

/-- Proportional repeated pole rows vanish even when other rows are errors. -/
theorem repeated_pole_zero {s : ℕ} (a : Fin s → ℂ)
    (V : Matrix (Fin s) (Fin s) ℂ) {i j : Fin s} (hij : i ≠ j)
    (hrow : V i = V j) : Matrix.det (fun u v => a u * V u v) = 0 := by
  have hscale : Matrix.det (fun u v => a u * V u v) = (∏ u, a u) * V.det := by
    exact Matrix.detRowAlternating.toMultilinearMap.map_smul_univ a V
  rw [hscale, Matrix.det_zero_of_row_eq hij hrow, mul_zero]

/-- Leibniz bound which retains a distinct weight for every row. -/
theorem det_norm_le_row_weights {s : ℕ} (M : Matrix (Fin s) (Fin s) ℂ)
    (w : Fin s → ℝ) (hw : ∀ i, 0 ≤ w i) (hM : ∀ i j, ‖M i j‖ ≤ w i) :
    ‖M.det‖ ≤ s.factorial * ∏ i, w i := by
  rw [Matrix.det_apply]
  apply (norm_sum_le _ _).trans
  have hterm (σ : Equiv.Perm (Fin s)) :
      ‖Equiv.Perm.sign σ • ∏ i, M (σ i) i‖ ≤ ∏ i, w i := by
    rw [norm_units_zsmul, norm_prod]
    apply (prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hM (σ i) i)).trans_eq
    exact Equiv.prod_comp σ w
  calc
    _ ≤ ∑ _σ : Equiv.Perm (Fin s), ∏ i, w i := sum_le_sum (fun σ _ => hterm σ)
    _ = _ := by simp [Fintype.card_perm]

/-- A mixed term, after repeated-pole cancellation and the ordered product bound,
has the required q^n rate. It does not repeat the largest modulus s-1 times. -/
theorem det_geometric_rate {s n : ℕ} (M : Matrix (Fin s) (Fin s) ℂ)
    (w : Fin s → ℝ) {K D q : ℝ} (hK : 0 ≤ K) (hw : ∀ i, 0 ≤ w i)
    (hD : 0 < D) (hq : 0 ≤ q) (hprod : (∏ i, w i) ≤ D * q)
    (hM : ∀ i j, ‖M i j‖ ≤ K * (w i) ^ n) :
    ‖M.det‖ / D ^ n ≤ s.factorial * K ^ s * q ^ n := by
  have h := det_norm_le_row_weights M (fun i => K * (w i) ^ n)
    (fun i => mul_nonneg hK (pow_nonneg (hw i) n)) hM
  simp only [prod_mul_distrib, prod_const, prod_pow, card_univ, Fintype.card_fin] at h
  have hp := pow_le_pow_left₀ (prod_nonneg (fun i _ => hw i)) hprod n
  rw [mul_pow] at hp
  apply (div_le_iff₀ (pow_pos hD n)).mpr
  have hh := mul_le_mul_of_nonneg_left hp
    (mul_nonneg (Nat.cast_nonneg s.factorial) (pow_nonneg hK s))
  nlinarith only [h, hh]

/-- A row choice with an error and distinct poles loses at least one factor d.
Repeated error labels are harmless: their normalized auxiliary factor is one. -/
theorem choice_weight_bound {ι : Type*} [DecidableEq ι] {s : ℕ}
    (α : ι → ℝ) (top : Finset ι) (e : Fin s → Option ι) {d ρ : ℝ}
    (hd : 0 < d) (hρ : 0 ≤ ρ) (hρd : ρ ≤ d)
    (h0 : ∀ l, 0 ≤ α l) (htop : ∀ l ∈ top, d ≤ α l)
    (hout : ∀ l ∉ top, α l ≤ d) (hcard : top.card = s)
    (herr : ∃ i, e i = none)
    (hinj : ∀ i j l, e i = some l → e j = some l → i = j) :
    (∏ i, (e i).elim ρ α) ≤ (∏ l ∈ top, α l) * (ρ / d) := by
  classical
  let β : Option ι → ℝ := fun o => o.elim 1 (fun l => α l / d)
  let W : Option ι → ℝ := fun o => o.elim ρ α
  have hb0 (o : Option ι) : 0 ≤ β o := by
    cases o <;> simp only [β, Option.elim_none, Option.elim_some]
    · norm_num
    · exact div_nonneg (h0 _) hd.le
  have himage : (∏ o ∈ univ.image e, β o) = ∏ i, β (e i) := by
    apply prod_image_of_pairwise_eq_one
    intro i _ j _ hij heq
    cases hi : e i with
    | none => simp [β, hi]
    | some l => exact False.elim (hij (hinj i j l hi (heq ▸ hi)))
  have hsel : (∏ i, β (e i)) ≤ (∏ l ∈ top, α l) / d ^ s := by
    rw [← himage]
    have ht := normalized_subset_product_bound β (top.image some) (univ.image e) hb0
      (by
        intro o ho
        obtain ⟨l, hl, rfl⟩ := mem_image.mp ho
        exact (one_le_div hd).mpr (htop l hl))
      (by
        intro o ho
        cases o with
        | none => simp [β]
        | some l => exact (div_le_one hd).mpr (hout l (by
            intro hl
            exact ho (mem_image.mpr ⟨l, hl, rfl⟩))))
    apply ht.trans_eq
    rw [prod_image (by intro i _ j _ h; exact Option.some.inj h)]
    simp only [β, Option.elim_some, prod_div_distrib, prod_const, hcard]
  obtain ⟨i, hi⟩ := herr
  have hpoint (j : Fin s) : W (e j) / d ≤ β (e j) := by
    cases e j with
    | none => exact (div_le_one hd).mpr hρd
    | some l => exact le_rfl
  have hw0 (j : Fin s) : 0 ≤ W (e j) / d := by
    cases e j with
    | none => exact div_nonneg hρ hd.le
    | some l => exact div_nonneg (h0 l) hd.le
  have haux : (∏ j, W (e j) / d) ≤ (ρ / d) * (∏ j, β (e j)) := by
    rw [← prod_erase_mul univ (fun j => W (e j) / d) (mem_univ i),
      ← prod_erase_mul univ (fun j => β (e j)) (mem_univ i)]
    simp only [hi, W, β, Option.elim_none, mul_one]
    exact (mul_le_mul_of_nonneg_right
      (prod_le_prod (fun j _ => hw0 j) (fun j _ => hpoint j))
      (div_nonneg hρ hd.le)).trans_eq (by ring)
  have h := haux.trans (mul_le_mul_of_nonneg_left hsel (div_nonneg hρ hd.le))
  simp only [prod_div_distrib, prod_const, card_univ, Fintype.card_fin] at h
  have hh := (div_le_iff₀ (pow_pos hd s)).mp h
  have heq : (ρ / d) * ((∏ l ∈ top, α l) / d ^ s) * d ^ s = (∏ l ∈ top, α l) * (ρ / d) := by
    field_simp
  exact hh.trans_eq heq

/-- One error label, with no assumption that different error rows coincide. -/
def choiceRows {ι : Type*} {s : ℕ} (P : Fin s → ι → Fin s → ℂ)
    (E : Matrix (Fin s) (Fin s) ℂ) (e : Fin s → Option ι) :
    Matrix (Fin s) (Fin s) ℂ := fun i => match e i with
      | none => E i
      | some l => P i l

/-- Exact mixed-row expansion of the determinant difference. -/
theorem determinant_difference_expansion {ι : Type*} [Fintype ι] [DecidableEq ι]
    {s : ℕ} (P : Fin s → ι → Fin s → ℂ) (E : Matrix (Fin s) (Fin s) ℂ) :
    Matrix.det (fun i j => (∑ l, P i l j) + E i j) - Matrix.det (fun i j => ∑ l, P i l j) =
      ∑ e : Fin s → Option ι,
        if ∃ i, e i = none then (choiceRows P E e).det else 0 := by
  classical
  have hsum (E : Matrix (Fin s) (Fin s) ℂ) :
      Matrix.det (fun i j => (∑ l, P i l j) + E i j) =
        ∑ e : Fin s → Option ι, (choiceRows P E e).det := by
    rw [show (fun i j => (∑ l, P i l j) + E i j) =
        (fun i j => ∑ l : Option ι, (match l with
          | none => E i
          | some k => P i k) j) by
      ext i j
      simp only [Fintype.sum_option]
      ring]
    exact row_expansion _
  have hzero : Matrix.det (fun i j => ∑ l, P i l j) =
      ∑ e : Fin s → Option ι, (choiceRows P 0 e).det := by
    simpa using hsum 0
  rw [hsum E, hzero, ← sum_sub_distrib]
  apply sum_congr rfl
  intro e _
  by_cases he : ∃ i, e i = none
  · rw [if_pos he]
    obtain ⟨i, hi⟩ := he
    have hz : (choiceRows P 0 e).det = 0 := Matrix.det_eq_zero_of_row_eq_zero i
      (by intro j; simp [choiceRows, hi])
    rw [hz, sub_zero]
  · rw [if_neg he]
    have hm : choiceRows P E e = choiceRows P 0 e := by
      ext i j
      cases h : e i with
      | none => exact False.elim (he ⟨i, h⟩)
      | some l => simp [choiceRows, h]
    rw [hm, sub_self]

/-- Sum the mixed terms, retaining the finite count (m+1)^s.
The per-term estimate is supplied by cancellation, ordered subset products,
and the geometric row estimate above. -/
theorem determinant_difference_rate {ι : Type*} [Fintype ι] [DecidableEq ι]
    {s n : ℕ} (P : Fin s → ι → Fin s → ℂ) (E : Matrix (Fin s) (Fin s) ℂ)
    {D B : ℝ} (hD : 0 < D) (hB : 0 ≤ B)
    (hterm : ∀ e : Fin s → Option ι, (∃ i, e i = none) →
      ‖(choiceRows P E e).det‖ / D ^ n ≤ B) :
    ‖Matrix.det (fun i j => (∑ l, P i l j) + E i j) - Matrix.det (fun i j => ∑ l, P i l j)‖ / D ^ n ≤
      (Fintype.card ι + 1 : ℝ) ^ s * B := by
  classical
  rw [determinant_difference_expansion]
  apply (div_le_iff₀ (pow_pos hD n)).mpr
  have ht (e : Fin s → Option ι) :
      ‖if ∃ i, e i = none then (choiceRows P E e).det else 0‖ ≤ B * D ^ n := by
    split_ifs with he
    · exact (div_le_iff₀ (pow_pos hD n)).mp (hterm e he)
    · simp only [norm_zero]
      exact mul_nonneg hB (pow_pos hD n).le
  calc
    _ ≤ ∑ e : Fin s → Option ι,
        ‖if ∃ i, e i = none then (choiceRows P E e).det else 0‖ := norm_sum_le _ _
    _ ≤ ∑ _e : Fin s → Option ι, B * D ^ n := sum_le_sum (fun e _ => ht e)
    _ = _ := by simp [Fintype.card_fun, Fintype.card_option]; ring

/-- Full finite mixed-row estimate. The scalar/profile factorization includes the
geometric pole rows. Its error rows may depend arbitrarily on their row index.
All subset ordering and repeated-pole cancellation are discharged here. -/
theorem mixed_determinant_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {s n : ℕ} (a : Fin s → ι → ℂ) (v : ι → Fin s → ℂ) (poles : ι → ℂ)
    (E : Matrix (Fin s) (Fin s) ℂ) (top : Finset ι) {K d ρ : ℝ}
    (hK : 0 ≤ K) (hd : 0 < d) (hρ : 0 ≤ ρ) (hρd : ρ ≤ d)
    (htop : ∀ l ∈ top, d ≤ ‖poles l‖) (hout : ∀ l ∉ top, ‖poles l‖ ≤ d)
    (hcard : top.card = s) (hP : ∀ i l j, ‖a i l * v l j‖ ≤ K)
    (hE : ∀ i j, ‖E i j‖ ≤ K * ρ ^ n) :
    ‖Matrix.det (fun i j => (∑ l, (a i l * v l j) * poles l ^ n) + E i j) - Matrix.det (fun i j => ∑ l, (a i l * v l j) * poles l ^ n)‖ / (∏ l ∈ top, ‖poles l‖) ^ n ≤
      (Fintype.card ι + 1 : ℝ) ^ s * (s.factorial * K ^ s * (ρ / d) ^ n) := by
  classical
  let P : Fin s → ι → Fin s → ℂ := fun i l j => (a i l * v l j) * poles l ^ n
  have hD : 0 < ∏ l ∈ top, ‖poles l‖ := prod_pos (fun l hl => hd.trans_le (htop l hl))
  apply determinant_difference_rate P E hD (by positivity)
  intro e herr
  by_cases hinj : ∀ i j l, e i = some l → e j = some l → i = j
  · let w : Fin s → ℝ := fun i => (e i).elim ρ (fun l => ‖poles l‖)
    apply det_geometric_rate (choiceRows P E e) w hK
      (by
        intro i
        cases he : e i with
        | none => simpa [w, he] using hρ
        | some l => simpa [w, he] using norm_nonneg (poles l)) hD (div_nonneg hρ hd.le)
      (choice_weight_bound (fun l => ‖poles l‖) top e hd hρ hρd
        (fun l => norm_nonneg _) htop hout hcard herr hinj)
    intro i j
    cases he : e i with
    | none => simpa [choiceRows, he, w] using hE i j
    | some l =>
      simp only [choiceRows, he, P, w, Option.elim_some, norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_right (by simpa only [norm_mul] using hP i l j)
        (pow_nonneg (norm_nonneg _) n)
  · push Not at hinj
    obtain ⟨i, j, l, hi, hj, hij⟩ := hinj
    let b : Fin s → ℂ := fun u => (e u).elim 1 (fun k => a u k * poles k ^ n)
    let V : Matrix (Fin s) (Fin s) ℂ := fun u => (e u).elim (E u) v
    have hm : choiceRows P E e = fun u w => b u * V u w := by
      ext u w
      cases he : e u <;> simp [choiceRows, he, P, b, V]
      ring
    have hv : V i = V j := by simp [V, hi, hj]
    rw [hm, repeated_pole_zero b V hij hv, norm_zero, zero_div]
    positivity

/-- The coefficient form of the mixed-row estimate with an explicit uniform
profile constant. Take C=max(A,max |c_l|) and B=max(1,ρ,max |poles_l|).
With ρ=R⁻¹ and d the last retained modulus, the rate is (R*d)⁻¹. -/
theorem coefficient_determinant_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {s n : ℕ} (hs : 0 < s) (c poles : ι → ℂ) (e : ℕ → ℂ)
    (top : Finset ι) {C B d ρ : ℝ} (hC : 0 ≤ C) (hB : 1 ≤ B)
    (hd : 0 < d) (hρ : 0 ≤ ρ) (hρd : ρ ≤ d) (hρB : ρ ≤ B)
    (hc : ∀ l, ‖c l‖ ≤ C) (hp : ∀ l, ‖poles l‖ ≤ B)
    (htop : ∀ l ∈ top, d ≤ ‖poles l‖) (hout : ∀ l ∉ top, ‖poles l‖ ≤ d)
    (hcard : top.card = s) (he : ∀ k, ‖e k‖ ≤ C * ρ ^ k) :
    ‖Matrix.det (fun i j : Fin s =>
        (∑ l, c l * poles l ^ (n + i.val + (s - 1 - j.val))) + e (n + i.val + (s - 1 - j.val))) - Matrix.det (fun i j : Fin s => ∑ l, c l * poles l ^ (n + i.val + (s - 1 - j.val)))‖ / (∏ l ∈ top, ‖poles l‖) ^ n ≤
      (Fintype.card ι + 1 : ℝ) ^ s * (s.factorial * (C * B ^ (2 * s - 2)) ^ s * (ρ / d) ^ n) := by
  let K := C * B ^ (2 * s - 2)
  have hB0 : 0 ≤ B := by linarith
  have hδ (i j : Fin s) : i.val + (s - 1 - j.val) ≤ 2 * s - 2 := by omega
  have hb (i j : Fin s) : B ^ (i.val + (s - 1 - j.val)) ≤ B ^ (2 * s - 2) :=
    pow_le_pow_right₀ hB (hδ i j)
  have hP (i : Fin s) (l : ι) (j : Fin s) :
      ‖(c l * poles l ^ i.val) * poles l ^ (s - 1 - j.val)‖ ≤ K := by
    simp only [norm_mul, norm_pow]
    calc
      _ = ‖c l‖ * ‖poles l‖ ^ (i.val + (s - 1 - j.val)) := by rw [pow_add]; ring
      _ ≤ C * B ^ (i.val + (s - 1 - j.val)) :=
        mul_le_mul (hc l) (pow_le_pow_left₀ (norm_nonneg _) (hp l) _)
          (pow_nonneg (norm_nonneg _) _) hC
      _ ≤ K := mul_le_mul_of_nonneg_left (hb i j) hC
  have hE (i j : Fin s) : ‖e (n + i.val + (s - 1 - j.val))‖ ≤ K * ρ ^ n := by
    apply (he _).trans
    rw [show n + i.val + (s - 1 - j.val) = n + (i.val + (s - 1 - j.val)) by omega, pow_add]
    have hr := (pow_le_pow_left₀ hρ hρB (i.val + (s - 1 - j.val))).trans (hb i j)
    have hm := mul_le_mul_of_nonneg_left hr (mul_nonneg hC (pow_nonneg hρ n))
    dsimp [K]
    nlinarith only [hm]
  have h := mixed_determinant_bound (fun i l => c l * poles l ^ i.val)
    (fun l j => poles l ^ (s - 1 - j.val)) poles
    (fun i j => e (n + i.val + (s - 1 - j.val))) top
    (mul_nonneg hC (pow_nonneg hB0 _)) hd hρ hρd htop hout hcard hP hE
  simpa only [K, pow_add, mul_assoc, mul_left_comm, mul_comm] using h

end Reinmann.SplitPairMixedRows
