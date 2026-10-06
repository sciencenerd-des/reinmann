import Reinmann.TuranDeficit

/-!
Algebraic controls for the normalized-deficit research program.
These theorems do not assert the analytic Lambert or Xi curvature estimates.
-/
noncomputable section
namespace Reinmann

/-- Normalized deficit for coefficients (n+1)/n! of (1+z) exp(z). -/
def realZeroControlEpsilon (x : ℝ) : ℝ :=
  (x ^ 2 + 3 * x + 1) / (x + 1) ^ 2

/-- The exponential-series coefficients gamma_n=n+1 have Turan difference 1. -/
theorem realZeroControl_turan (x : ℝ) :
    (x + 1) ^ 2 - x * (x + 2) = 1 := by ring

/-- Despite the constant Turan difference, the scaled deficit is not log-concave. -/
theorem realZeroControl_scaled_deficit_fails :
    realZeroControlEpsilon 3 ^ 2 <
      realZeroControlEpsilon 2 * realZeroControlEpsilon 4 := by
  norm_num [realZeroControlEpsilon]

/-- Positive numerator of the continuous curvature after x=y+3. -/
theorem realZeroControl_curvature_numerator_pos (y : ℝ) (hy : 0 ≤ y) :
    0 < 2 * (y + 3) ^ 3 + (y + 3) ^ 2 - 8 * (y + 3) - 5 := by
  have hid : 2 * (y + 3) ^ 3 + (y + 3) ^ 2 - 8 * (y + 3) - 5 =
      2 * y ^ 3 + 19 * y ^ 2 + 52 * y + 34 := by ring
  rw [hid]
  positivity

/-- Positive numerator of the negative discrete slack after x=y+3. -/
theorem realZeroControl_discrete_numerator_pos (y : ℝ) (hy : 0 ≤ y) :
    0 < 2 * (y + 3) ^ 5 + 5 * (y + 3) ^ 4 - 6 * (y + 3) ^ 3 -
      25 * (y + 3) ^ 2 - 20 * (y + 3) - 5 := by
  have hid : 2 * (y + 3) ^ 5 + 5 * (y + 3) ^ 4 - 6 * (y + 3) ^ 3 -
      25 * (y + 3) ^ 2 - 20 * (y + 3) - 5 =
      2 * y ^ 5 + 35 * y ^ 4 + 234 * y ^ 3 + 731 * y ^ 2 + 1018 * y + 439 := by ring
  rw [hid]
  positivity

/-- Final sign deduction once an analytic error budget has been established. -/
theorem curvature_negative_of_half_budget (Q E C : ℝ)
    (hQ : 0 < Q) (hE : E ≤ Q / 2) (hC : C ≤ -Q + E) : C < 0 := by
  linarith

#print axioms realZeroControl_turan
#print axioms realZeroControl_scaled_deficit_fails
#print axioms realZeroControl_curvature_numerator_pos
#print axioms realZeroControl_discrete_numerator_pos
#print axioms curvature_negative_of_half_budget

end Reinmann
