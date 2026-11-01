/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.ToeplitzMeasure
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Uniqueness among arbitrary finite unit-circle representing measures

The singular finite moment problem determines a measure, not just finite data.
This is a shared prerequisite; no arithmetic positivity is supplied.
-/

noncomputable section

namespace Reinmann.ToeplitzMeasureUniqueness

open Matrix Polynomial MeasureTheory Reinmann.ToeplitzKernel Reinmann.ToeplitzAtomic
  Reinmann.ToeplitzSimpleRoots Reinmann.ToeplitzExtension
  Reinmann.ToeplitzUniqueness Reinmann.ToeplitzMeasure
open scoped ComplexOrder ENNReal

lemma integral_pairing {n : ℕ} {T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {μ : Measure ℂ} (hμ : Represents T μ) {p q : ℂ[X]}
    (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n) :
    (∫ z, star (p.eval z) * q.eval z ∂μ) = pairing T p q := by
  letI := hμ.finite
  have hexp (z : ℂ) : star (p.eval z) * q.eval z =
      ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
        (star (p.coeff i) * q.coeff j) * (star (z ^ (i : ℕ)) * z ^ (j : ℕ)) := by
    rw [← eval_coeff_sum hp, ← eval_coeff_sum hq, star_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [star_mul]
    ring
  simp_rw [hexp]
  rw [integral_finsetSum]
  · unfold pairing
    simp only [coeffVec, dotProduct, mulVec, Pi.star_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _
      rw [integral_const_mul, ← hμ.entries i j]
      ring
    · intro j _
      exact integrable_of_continuous_circle hμ.circle (by fun_prop)
  · intro i _
    exact integrable_of_continuous_circle hμ.circle (by fun_prop)

/-- Any kernel polynomial vanishes almost everywhere for a representing measure. -/
theorem eval_zero_ae_of_kernel {n : ℕ}
    {T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {μ : Measure ℂ} (hμ : Represents T μ) {q : ℂ[X]} (hq : q.natDegree ≤ n)
    (hk : T *ᵥ coeffVec n q = 0) : ∀ᵐ z ∂μ, q.eval z = 0 := by
  letI := hμ.finite
  have hi : Integrable (fun z => star (q.eval z) * q.eval z) μ :=
    integrable_of_continuous_circle hμ.circle (by fun_prop)
  have hr (z : ℂ) : (star (q.eval z) * q.eval z).re = ‖q.eval z‖ ^ 2 := by
    have he : star (q.eval z) * q.eval z = (‖q.eval z‖ ^ 2 : ℝ) := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
      rfl
    rw [he, Complex.ofReal_re]
  have hir : Integrable (fun z => ‖q.eval z‖ ^ 2) μ := by
    simpa only [RCLike.re_to_complex, hr] using hi.re
  have he : (∫ z, ‖q.eval z‖ ^ 2 ∂μ) = 0 := by
    simp_rw [← hr]
    have hi_re := integral_re hi
    change (∫ z, (star (q.eval z) * q.eval z).re ∂μ) =
      (∫ z, star (q.eval z) * q.eval z ∂μ).re at hi_re
    rw [hi_re, integral_pairing hμ hq hq]
    simp [pairing, hk]
  have hz := (integral_eq_zero_iff_of_nonneg (fun z => sq_nonneg ‖q.eval z‖) hir).mp he
  filter_upwards [hz] with z hz
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)

/-- At most n nodes confine every positive Borel competitor to the same nodes. -/
theorem ae_mem_of_card_le {n : ℕ} {s : Finset ℂ} {w : ℂ → ℝ}
    (hs : s.card ≤ n) {μ : Measure ℂ} (hμ : Represents (atomicMatrix n s w) μ) :
    ∀ᵐ z ∂μ, z ∈ s := by
  let q := Lagrange.nodal s id
  have hq : q.natDegree ≤ n := by rw [Lagrange.natDegree_nodal]; exact hs
  have hk : atomicMatrix n s w *ᵥ coeffVec n q = 0 := by
    apply atomicMatrix_kernel s w hq
    intro z hz
    simpa only [id_eq] using (Lagrange.eval_nodal_at_node (v := id) hz)
  filter_upwards [eval_zero_ae_of_kernel hμ hq hk] with z hz
  have hp : (∏ x ∈ s, (z - x)) = 0 := by
    simpa only [q, Lagrange.eval_nodal, id_eq] using hz
  obtain ⟨x, hx, hzx⟩ := Finset.prod_eq_zero_iff.mp hp
  rw [sub_eq_zero.mp hzx]
  exact hx

lemma measure_eq_atomic_of_ae_mem {μ : Measure ℂ} [IsFiniteMeasure μ]
    {s : Finset ℂ} (hμ : ∀ᵐ z ∂μ, z ∈ s) :
    μ = atomicMeasure s (fun z => (μ {z}).toReal) := by
  calc
    μ = ∑ z ∈ s, μ {z} • Measure.dirac z := Measure.ae_mem_finset_iff.mp hμ
    _ = atomicMeasure s (fun z => (μ {z}).toReal) := by
      unfold atomicMeasure
      apply Finset.sum_congr rfl
      intro z _
      rw [ENNReal.ofReal_toReal (measure_ne_top μ {z})]

/-- A representation with at most n nodes determines every finite positive circle measure. -/
theorem measure_eq_atomic_of_card_le {n : ℕ} {s : Finset ℂ} {w : ℂ → ℝ}
    (hs : s.card ≤ n) {μ : Measure ℂ} (hμ : Represents (atomicMatrix n s w) μ) :
    μ = atomicMeasure s w := by
  letI := hμ.finite
  have he := measure_eq_atomic_of_ae_mem (ae_mem_of_card_le hs hμ)
  have hentries : atomicMatrix n s w =
      atomicMatrix n s (fun z => (μ {z}).toReal) := by
    ext i j
    conv_lhs =>
      rw [hμ.entries i j, he, integral_atomicMeasure s _ (fun _ _ => ENNReal.toReal_nonneg)]
    apply Finset.sum_congr rfl
    intro z _
    ring
  have hw := weights_eq_on_support (hs.trans (Nat.le_succ n)) hentries
  calc
    μ = atomicMeasure s (fun z => (μ {z}).toReal) := he
    _ = atomicMeasure s w := by
      unfold atomicMeasure
      apply Finset.sum_congr rfl
      intro z hz
      rw [hw z hz]

/-- Singular PSD Toeplitz matrices have a unique representing finite positive circle measure. -/
theorem exists_unique_representing_measure_singular {n : ℕ}
    {T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hpsd : T.PosSemidef) (htoe : IsToeplitz T) (hrank : T.rank ≤ n) :
    ∃! μ : Measure ℂ, Represents T μ := by
  obtain ⟨s, w, hcard, hnodes, hentries⟩ :=
    ToeplitzRepresentation.exists_atomic_representation hpsd htoe
  have heq : T = atomicMatrix n s w := by ext i j; exact hentries i j
  refine ⟨atomicMeasure s w, ?_, ?_⟩
  · rw [heq]
    exact atomicMeasure_represents s w (fun z hz => ⟨(hnodes z hz).1, (hnodes z hz).2.le⟩)
  · intro μ hμ
    rw [heq] at hμ
    exact measure_eq_atomic_of_card_le (by omega) hμ

lemma atomicMeasure_singleton (s : Finset ℂ) (w : ℂ → ℝ) (x : ℂ) :
    atomicMeasure s w {x} = if x ∈ s then ENNReal.ofReal (w x) else 0 := by
  simp [atomicMeasure, Measure.finsetSum_apply, Measure.smul_apply,
    Set.indicator_apply]

/-- Distinct positive finite supports define different measures. -/
lemma atomicMeasure_ne_of_support_ne {s t : Finset ℂ} {w v : ℂ → ℝ}
    (hs : ∀ z ∈ s, 0 < w z) (ht : ∀ z ∈ t, 0 < v z) (hne : s ≠ t) :
    atomicMeasure s w ≠ atomicMeasure t v := by
  intro heq
  apply hne
  ext x
  have hx := congrArg (fun μ : Measure ℂ => μ {x}) heq
  simp only [atomicMeasure_singleton] at hx
  constructor
  · intro hxs
    by_contra hxt
    rw [if_pos hxs, if_neg hxt] at hx
    exact (ne_of_gt (ENNReal.ofReal_pos.mpr (hs x hxs))) hx
  · intro hxt
    by_contra hxs
    rw [if_pos hxt, if_neg hxs] at hx
    exact (ne_of_gt (ENNReal.ofReal_pos.mpr (ht x hxt))) hx.symm

/-- Every full-rank PSD Toeplitz matrix has distinct finite positive circle measures. -/
theorem nonunique_representing_measure_of_full_rank {n : ℕ}
    {T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hpsd : T.PosSemidef) (htoe : IsToeplitz T) (hrank : T.rank = n + 1) :
    ∃ μ ν : Measure ℂ, Represents T μ ∧ Represents T ν ∧ μ ≠ ν := by
  obtain ⟨s, t, w, v, _, _, hne, hs, ht, hsT, htT⟩ :=
    ToeplitzFullRank.nonunique_of_full_rank hpsd htoe hrank
  refine ⟨atomicMeasure s w, atomicMeasure t v, ?_, ?_, ?_⟩
  · rw [hsT]
    exact atomicMeasure_represents s w (fun z hz => ⟨(hs z hz).1, (hs z hz).2.le⟩)
  · rw [htT]
    exact atomicMeasure_represents t v (fun z hz => ⟨(ht z hz).1, (ht z hz).2.le⟩)
  · exact atomicMeasure_ne_of_support_ne (fun z hz => (hs z hz).2)
      (fun z hz => (ht z hz).2) hne

/-- The finite positive circle moment problem has a unique measure exactly in singular rank. -/
theorem unique_representing_measure_iff_singular {n : ℕ}
    {T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hpsd : T.PosSemidef) (htoe : IsToeplitz T) :
    (∃! μ : Measure ℂ, Represents T μ) ↔ T.rank ≤ n := by
  constructor
  · rintro ⟨μ, _, huni⟩
    by_contra hnot
    have hrank : T.rank = n + 1 := by
      have hb := T.rank_le_width
      omega
    obtain ⟨ν, ξ, hν, hξ, hne⟩ :=
      nonunique_representing_measure_of_full_rank hpsd htoe hrank
    exact hne ((huni ν hν).trans (huni ξ hξ).symm)
  · exact exists_unique_representing_measure_singular hpsd htoe

end Reinmann.ToeplitzMeasureUniqueness
