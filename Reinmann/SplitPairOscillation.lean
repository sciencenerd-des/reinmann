/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push

/-! Finite geometric-sum oscillation, with no irrational-rotation hypothesis. -/
noncomputable section
namespace Reinmann.SplitPairOscillation
open Finset

/-- A geometric block on the unit circle has a bound independent of its start. -/
theorem norm_geometric_block {u w : ℂ} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    (hne : u ≠ 1) (m N : ℕ) :
    ‖∑ j ∈ range N, w * u ^ (m + j)‖ ≤ 2 / ‖1 - u‖ := by
  have hd : 0 < ‖1 - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hne))
  have he : (∑ j ∈ range N, w * u ^ (m + j)) =
      w * u ^ m * ∑ j ∈ range N, u ^ j := by
    simp_rw [pow_add, ← mul_assoc]
    rw [mul_sum]
  rw [he, norm_mul, norm_mul, hw, norm_pow, hu]
  simp only [one_pow, one_mul]
  apply (le_div_iff₀ hd).mpr
  rw [← norm_mul, geom_sum_mul_neg]
  calc
    ‖1 - u ^ N‖ ≤ ‖(1 : ℂ)‖ + ‖u ^ N‖ := norm_sub_le _ _
    _ = 2 := by norm_num [norm_pow, hu]

/-- Pointwise square identity for a unit complex number. -/
theorem real_square {z : ℂ} (hz : ‖z‖ = 1) : z.re ^ 2 = (1 + (z ^ 2).re) / 2 := by
  have hn : z.re ^ 2 + z.im ^ 2 = 1 := by
    have h : ‖z‖ ^ 2 = 1 := by rw [hz]; norm_num
    rw [Complex.sq_norm, Complex.normSq_apply] at h
    simpa only [pow_two] using h
  simp only [pow_two, Complex.mul_re]
  nlinarith

/-- The real parts in a block have bounded sum. -/
theorem real_sum_le {u w : ℂ} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    (hne : u ≠ 1) (m N : ℕ) :
    ∑ j ∈ range N, (w * u ^ (m + j)).re ≤ 2 / ‖1 - u‖ := by
  calc
    _ = (∑ j ∈ range N, w * u ^ (m + j)).re := by simp
    _ ≤ ‖∑ j ∈ range N, w * u ^ (m + j)‖ := Complex.re_le_norm _
    _ ≤ _ := norm_geometric_block hu hw hne m N

/-- The second moment cannot remain small on arbitrarily long blocks. -/
theorem real_square_sum_ge {u w : ℂ} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    (hne : u ^ 2 ≠ 1) (m N : ℕ) :
    (N : ℝ) / 2 - 1 / ‖1 - u ^ 2‖ ≤
      ∑ j ∈ range N, (w * u ^ (m + j)).re ^ 2 := by
  have hunit (j : ℕ) : ‖w * u ^ (m + j)‖ = 1 := by simp [norm_pow, hu, hw]
  have he : (∑ j ∈ range N, (w * u ^ (m + j)).re ^ 2) =
      ((N : ℝ) + (∑ j ∈ range N, w ^ 2 * (u ^ 2) ^ (m + j)).re) / 2 := by
    simp_rw [real_square (hunit _), mul_pow, ← pow_mul, Nat.mul_comm 2, pow_mul]
    simp_rw [div_eq_mul_inv]
    rw [← sum_mul, sum_add_distrib]
    simp
  have hb := norm_geometric_block (u := u ^ 2) (w := w ^ 2)
    (by simp [norm_pow, hu]) (by simp [norm_pow, hw]) hne m N
  have hr := (abs_le.mp (Complex.abs_re_le_norm
    (∑ j ∈ range N, w ^ 2 * (u ^ 2) ^ (m + j)))).1
  rw [he]
  simp only [div_eq_mul_inv] at hb ⊢
  nlinarith

/-- Explicit finite-block negative phase, uniformly over the starting rank. -/
theorem exists_negative_phase {u w : ℂ} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    (hne : u ≠ 1) (hne2 : u ^ 2 ≠ 1) (m N : ℕ)
    (hN : 4 / ‖1 - u ^ 2‖ + 6 / ‖1 - u‖ < (N : ℝ)) :
    ∃ j ∈ range N, (w * u ^ (m + j)).re < -(1 / 4 : ℝ) := by
  by_contra h
  push Not at h
  have hbound (j : ℕ) (hj : j ∈ range N) :
      (w * u ^ (m + j)).re ^ 2 ≤
        (3 / 4 : ℝ) * (w * u ^ (m + j)).re + 1 / 4 := by
    have hl := h j hj
    have hu' : (w * u ^ (m + j)).re ≤ 1 := by
      calc
        _ ≤ ‖w * u ^ (m + j)‖ := Complex.re_le_norm _
        _ = 1 := by simp [norm_pow, hu, hw]
    nlinarith [mul_nonneg (by linarith : 0 ≤ (w * u ^ (m + j)).re + 1 / 4)
      (by linarith : 0 ≤ 1 - (w * u ^ (m + j)).re)]
  have hs := sum_le_sum hbound
  rw [sum_add_distrib, ← mul_sum] at hs
  simp only [sum_const, card_range, nsmul_eq_mul] at hs
  have hfirst := real_sum_le hu hw hne m N
  have hsecond := real_square_sum_ge hu hw hne2 m N
  simp only [div_eq_mul_inv] at hN hfirst hsecond hs
  nlinarith

/-- The same block contains a positive phase bounded away from zero. -/
theorem exists_positive_phase {u w : ℂ} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    (hne : u ≠ 1) (hne2 : u ^ 2 ≠ 1) (m N : ℕ)
    (hN : 4 / ‖1 - u ^ 2‖ + 6 / ‖1 - u‖ < (N : ℝ)) :
    ∃ j ∈ range N, (1 / 4 : ℝ) < (w * u ^ (m + j)).re := by
  obtain ⟨j, hj, h⟩ := exists_negative_phase hu (show ‖-w‖ = 1 by simpa) hne hne2 m N hN
  refine ⟨j, hj, ?_⟩
  simp only [neg_mul, Complex.neg_re] at h
  linarith

open Filter in
/-- A vanishing perturbation preserves the two signs on unbounded ranks. This
is an intermediate analytic lemma; it does not assume a determinant identity. -/
theorem perturbed_phase_both_signs {u w : ℂ} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    (hne : u ≠ 1) (hne2 : u ^ 2 ≠ 1) {a : ℝ} (ha : 0 < a)
    {e : ℕ → ℝ} (he : Tendsto e atTop (nhds 0)) :
    (∀ M, ∃ n ≥ M, a * (w * u ^ n).re + e n < 0) ∧
    (∀ M, ∃ n ≥ M, 0 < a * (w * u ^ n).re + e n) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (4 / ‖1 - u ^ 2‖ + 6 / ‖1 - u‖)
  obtain ⟨B, hB⟩ := Metric.tendsto_atTop.mp he (a / 8) (by linarith)
  have herr (n : ℕ) (hn : B ≤ n) : |e n| < a / 8 := by
    simpa only [Real.dist_eq, sub_zero] using hB n hn
  constructor
  · intro M
    obtain ⟨j, _, hj⟩ := exists_negative_phase hu hw hne hne2 (max M B) N hN
    refine ⟨max M B + j, by omega, ?_⟩
    have hb := (abs_lt.mp (herr (max M B + j) (by omega))).2
    nlinarith
  · intro M
    obtain ⟨j, _, hj⟩ := exists_positive_phase hu hw hne hne2 (max M B) N hN
    refine ⟨max M B + j, by omega, ?_⟩
    have hb := (abs_lt.mp (herr (max M B + j) (by omega))).1
    nlinarith

open Filter in
/-- A finite sum of strictly subunit geometric terms really tends to zero. -/
theorem finite_geometric_tail_tendsto {ι : Type*} [Fintype ι]
    (c v : ι → ℂ) (hv : ∀ i, ‖v i‖ < 1) :
    Tendsto (fun n : ℕ => ∑ i, c i * v i ^ n) atTop (nhds 0) := by
  convert tendsto_finsetSum Finset.univ
    (fun i _ => (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (hv i)).const_mul (c i)) using 1
  simp

open Filter in
/-- Oscillation for a computed finite exponential sum with a conjugate leading
pair. The error limit here is proved from the individual strict modulus gaps. -/
theorem finite_split_sum_both_signs {ι : Type*} [Fintype ι]
    {K u : ℂ} (hK : K ≠ 0) (hu : ‖u‖ = 1)
    (hne : u ≠ 1) (hne2 : u ^ 2 ≠ 1) (c v : ι → ℂ) (hv : ∀ i, ‖v i‖ < 1) :
    (∀ M, ∃ n ≥ M,
      (K * u ^ n + star K * (star u) ^ n + ∑ i, c i * v i ^ n).re < 0) ∧
    (∀ M, ∃ n ≥ M,
      0 < (K * u ^ n + star K * (star u) ^ n + ∑ i, c i * v i ^ n).re) := by
  let w : ℂ := K / (‖K‖ : ℂ)
  have hk : 0 < ‖K‖ := norm_pos_iff.mpr hK
  have hw : ‖w‖ = 1 := by
    dsimp [w]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk, div_self hk.ne']
  have he := (Complex.continuous_re.tendsto (0 : ℂ)).comp
    (finite_geometric_tail_tendsto c v hv)
  have h := perturbed_phase_both_signs hu hw hne hne2 (show 0 < 2 * ‖K‖ by positivity) he
  have hphase (n : ℕ) :
      (K * u ^ n + star K * (star u) ^ n + ∑ i, c i * v i ^ n).re =
      (2 * ‖K‖) * (w * u ^ n).re + (∑ i, c i * v i ^ n).re := by
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

/-- Uniform exponential control of a finite geometric remainder. -/
theorem norm_finite_geometric_tail_le {ι : Type*} [Fintype ι] (c v : ι → ℂ)
    {ρ : ℝ} (_hρ : 0 ≤ ρ) (hv : ∀ i, ‖v i‖ ≤ ρ) (n : ℕ) :
    ‖∑ i, c i * v i ^ n‖ ≤ (∑ i, ‖c i‖) * ρ ^ n := by
  calc
    _ ≤ ∑ i, ‖c i * v i ^ n‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖c i‖ * ρ ^ n := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hv i) n) (norm_nonneg _)
    _ = _ := (Finset.sum_mul _ _ _).symm

/-- Finitely many strict modulus gaps admit one common rate below1. -/
theorem exists_geometric_rate {ι : Type*} [Finite ι] (v : ι → ℂ)
    (hv : ∀ i, ‖v i‖ < 1) : ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ∀ i, ‖v i‖ ≤ ρ := by
  classical
  letI := Fintype.ofFinite ι
  have haux (S : Finset ι) : ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ∀ i ∈ S, ‖v i‖ ≤ ρ := by
    classical
    induction S using Finset.induction_on with
    | empty => exact ⟨1/2, by norm_num, by norm_num, by simp⟩
    | @insert i S hi ih =>
      obtain ⟨ρ, hpos, hlt, hbound⟩ := ih
      refine ⟨max ρ ((‖v i‖+1)/2), lt_of_lt_of_le hpos (le_max_left _ _),
        max_lt hlt (by linarith [hv i]), ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with hij | hj
      · subst j
        exact (show ‖v i‖ ≤ (‖v i‖+1)/2 by linarith [hv i]).trans (le_max_right _ _)
      · exact (hbound j hj).trans (le_max_left _ _)
  obtain ⟨ρ, hpos, hlt, hb⟩ := haux Finset.univ
  exact ⟨ρ, hpos, hlt, fun i => hb i (Finset.mem_univ i)⟩

end Reinmann.SplitPairOscillation
