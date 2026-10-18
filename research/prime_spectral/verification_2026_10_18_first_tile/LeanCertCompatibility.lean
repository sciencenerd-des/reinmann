import LeanCert.Core.IntervalRat.Taylor
import Mathlib.Tactic.NormNum
open LeanCert.Core
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace LeanCertCompatibility
theorem exp_bound : Real.exp 1 ≤ 3 := by
  have hx : (1 : ℝ) ∈ IntervalRat.singleton 1 := by
    constructor <;> norm_num [IntervalRat.singleton]
  have h := IntervalRat.mem_expComputable hx 10
  have hu : ((IntervalRat.expComputable (IntervalRat.singleton 1) 10).hi : ℝ) ≤ 3 := by
    have hr : (IntervalRat.expComputable (IntervalRat.singleton 1) 10).hi ≤ (3 : ℚ) := by
      decide +kernel
    exact_mod_cast hr
  exact h.2.trans hu
theorem log_bound : Real.log (3/2) ≤ 1/2 := by
  have hx : (3/2 : ℝ) ∈ IntervalRat.singleton (3/2) := by
    constructor <;> norm_num [IntervalRat.singleton]
  have hp : (0 : ℚ) < (IntervalRat.singleton (3/2)).lo := by
    norm_num [IntervalRat.singleton]
  have h := IntervalRat.mem_logComputable hx hp 10
  have hr : (IntervalRat.logComputable (IntervalRat.singleton (3/2)) 10).hi ≤ (1/2 : ℚ) := by
    decide +kernel
  have hu : ((IntervalRat.logComputable (IntervalRat.singleton (3/2)) 10).hi : ℝ) ≤ 1/2 := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hr
    norm_num at hc
    exact hc
  exact h.2.trans hu
#print axioms exp_bound
#print axioms log_bound
end LeanCertCompatibility
