/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.FinitePFBaseline
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Positive inverse-zero power sums alone do not give Schur/Toeplitz positivity.
The polynomial (1+X)(1+X/3+X²/9) has a negative rank-three, shift-two minor.
This is an exact obstruction to a proposed shortcut, not an arithmetic model. -/
noncomputable section
namespace Reinmann.CornerPowerSumCounterexample

noncomputable def powerSum (k : ℕ) : ℝ :=
  1 + 2 * (1 / 3 : ℝ) ^ k * Real.cos ((k : ℝ) * Real.pi / 3)

/-- All positive-order power sums are uniformly positive. -/
theorem powerSum_ge_third (k : ℕ) (hk : 0 < k) : (1 / 3 : ℝ) ≤ powerSum k := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  have hp : 0 ≤ (1 / 3 : ℝ) ^ n := by positivity
  have hp1 : (1 / 3 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hc := Real.neg_one_le_cos (((n + 1 : ℕ) : ℝ) * Real.pi / 3)
  have hmul := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ (1 / 3 : ℝ) ^ (n + 1))
  unfold powerSum
  rw [pow_succ] at hmul ⊢
  nlinarith

/-- Ordinary coefficients of the displayed cubic. -/
def mu (n : ℕ) : ℝ :=
  if n = 0 then 1 else if n = 1 then 4 / 3 else if n = 2 then 4 / 9
  else if n = 3 then 1 / 9 else 0

theorem shift_two_rank_three :
    (Matrix.of fun i j : Fin 3 => sequenceToeplitz mu (i.val + 2) j.val).det =
      (-23 / 729 : ℝ) := by
  norm_num [Matrix.det_fin_three, sequenceToeplitz, mu]

theorem not_finitePF_three : ¬ FinitePF mu 3 := by
  intro h
  have hr : StrictMono (fun i : Fin 3 => i.val + 2) := by
    intro i j hij
    exact Nat.add_lt_add_right hij 2
  have hc : StrictMono (fun i : Fin 3 => i.val) := fun _ _ hij => hij
  have hh := h 3 le_rfl (fun i => i.val + 2) (fun i => i.val) hr hc
  rw [shift_two_rank_three] at hh
  norm_num at hh

end Reinmann.CornerPowerSumCounterexample
