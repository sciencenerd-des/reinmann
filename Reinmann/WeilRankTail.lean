import Mathlib.Algebra.Field.GeomSum
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Signed algebra behind the Weil omitted-mode tail

These are exact identities at arbitrary expansion order. They do not assert
that the analytic Weil matrix, or any computed interval, has been formalized.
-/
noncomputable section
namespace Reinmann.WeilRankTail

/-- Pair the positive and negative Fourier modes before taking absolute values. -/
theorem paired_displacement (b c n i : ℝ)
    (hm : n - i ≠ 0) (hp : n + i ≠ 0) :
    (b - c) / (n - i) + (b + c) / (n + i) =
      2 * (b * n - c * i) / (n ^ 2 - i ^ 2) := by
  have hd : n ^ 2 - i ^ 2 ≠ 0 := by
    have he : n ^ 2 - i ^ 2 = (n - i) * (n + i) := by ring
    rw [he]
    exact mul_ne_zero hm hp
  field_simp
  ring

/-- Finite geometric expansion with its exact signed remainder. -/
theorem geometric_remainder (x : ℝ) (R : ℕ) (hx : 1 - x ≠ 0) :
    1 / (1 - x) = (∑ r ∈ Finset.range R, x ^ r) + x ^ R / (1 - x) := by
  have h := geom_sum_mul_neg x R
  field_simp
  nlinarith [h]

/-- Uniform scalar control of the common remainder, without splitting moments. -/
theorem geometric_remainder_abs (x q : ℝ) (R : ℕ)
    (hx : 0 ≤ x) (hxq : x ≤ q) (hq : q < 1) :
    |1 / (1 - x) - (∑ r ∈ Finset.range R, x ^ r)| ≤ q ^ R / (1 - q) := by
  have hd : 0 < 1 - x := by linarith
  have he : 1 / (1 - x) - (∑ r ∈ Finset.range R, x ^ r) =
      x ^ R / (1 - x) := by
    linarith [geometric_remainder x R (ne_of_gt hd)]
  rw [he, abs_of_nonneg (div_nonneg (pow_nonneg hx R) (le_of_lt hd))]
  exact div_le_div₀ (pow_nonneg (hx.trans hxq) R) (pow_le_pow_left₀ hx hxq R)
    (by linarith) (by linarith)

/-- The exact omitted even component in the orthonormal Fourier coordinates.
The sum is signed; its leading coefficient is the common boundary sum. -/
theorem paired_even_tail {ι : Type*} (s : Finset ι) (u j b : ι → ℝ)
    (u₀ bₙ n : ℝ) (hn : n ≠ 0)
    (hm : ∀ i ∈ s, n - j i ≠ 0) (hp : ∀ i ∈ s, n + j i ≠ 0) :
    Real.sqrt 2 * bₙ * u₀ / n +
      (∑ i ∈ s, u i * ((bₙ - b i) / (n - j i) + (bₙ + b i) / (n + j i))) =
    Real.sqrt 2 * bₙ * (u₀ + Real.sqrt 2 * ∑ i ∈ s, u i) / n +
      (2 * bₙ / n) * (∑ i ∈ s, u i * j i ^ 2 / (n ^ 2 - j i ^ 2)) -
      2 * (∑ i ∈ s, j i * b i * u i / (n ^ 2 - j i ^ 2)) := by
  have ht : ∀ i ∈ s,
      u i * ((bₙ - b i) / (n - j i) + (bₙ + b i) / (n + j i)) =
        2 * bₙ / n * u i +
          (2 * bₙ / n) * (u i * j i ^ 2 / (n ^ 2 - j i ^ 2)) -
          2 * (j i * b i * u i / (n ^ 2 - j i ^ 2)) := by
    intro i hi
    rw [paired_displacement bₙ (b i) n (j i) (hm i hi) (hp i hi)]
    have hd : n ^ 2 - j i ^ 2 ≠ 0 := by
      have he : n ^ 2 - j i ^ 2 = (n - j i) * (n + j i) := by ring
      rw [he]
      exact mul_ne_zero (hm i hi) (hp i hi)
    field_simp
    ring
  rw [Finset.sum_congr rfl ht]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hs : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := Real.mul_self_sqrt (by norm_num)
  linear_combination (-(bₙ * (∑ i ∈ s, u i) / n)) * hs

/-- Arbitrary-order expansion of the paired denominator, including order zero. -/
theorem denominator_remainder (n i : ℝ) (R : ℕ)
    (hn : n ≠ 0) (hd : n ^ 2 - i ^ 2 ≠ 0) :
    1 / (n ^ 2 - i ^ 2) =
      (∑ r ∈ Finset.range R, (i ^ 2 / n ^ 2) ^ r) / n ^ 2 +
        (i ^ 2 / n ^ 2) ^ R / (n ^ 2 - i ^ 2) := by
  have h := geom_sum_mul_neg (i ^ 2 / n ^ 2) R
  have hn2 : n ^ 2 ≠ 0 := pow_ne_zero _ hn
  have he : (∑ r ∈ Finset.range R, (i ^ 2 / n ^ 2) ^ r) *
      (n ^ 2 - i ^ 2) = n ^ 2 * (1 - (i ^ 2 / n ^ 2) ^ R) := by
    calc
      _ = n ^ 2 * ((∑ r ∈ Finset.range R, (i ^ 2 / n ^ 2) ^ r) *
          (1 - i ^ 2 / n ^ 2)) := by field_simp
      _ = _ := by rw [h]
  field_simp
  nlinarith [he]

/-- Summation preserves the signed moments and one common remainder. -/
theorem weighted_moment_remainder {ι : Type*} (s : Finset ι)
    (w j : ι → ℝ) (n : ℝ) (R : ℕ) (hn : n ≠ 0)
    (hd : ∀ i ∈ s, n ^ 2 - j i ^ 2 ≠ 0) :
    (∑ i ∈ s, w i / (n ^ 2 - j i ^ 2)) =
      (∑ r ∈ Finset.range R, (∑ i ∈ s, w i * (j i ^ 2 / n ^ 2) ^ r)) /
        n ^ 2 +
      ∑ i ∈ s, w i * (j i ^ 2 / n ^ 2) ^ R / (n ^ 2 - j i ^ 2) := by
  calc
    _ = ∑ i ∈ s, (w i * (∑ r ∈ Finset.range R, (j i ^ 2 / n ^ 2) ^ r) /
        n ^ 2 + w i * (j i ^ 2 / n ^ 2) ^ R / (n ^ 2 - j i ^ 2)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have h := denominator_remainder n (j i) R hn (hd i hi)
      calc
        _ = w i * (1 / (n ^ 2 - j i ^ 2)) := by ring
        _ = _ := by rw [h]; ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, div_eq_mul_inv, Finset.sum_mul,
        Finset.mul_sum]
      rw [Finset.sum_comm]

end Reinmann.WeilRankTail
