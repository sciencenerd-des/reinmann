import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Form-energy control for a Fourier-observable certificate

These are scalar consequences of the actual full spectral decomposition.
The closed Weil form, compact resolvent, min-max bounds and Fourier
Cauchy-Schwarz estimate are written analytic dependencies, not proved here.
No finite matrix gap is identified with a full spectral gap by this module.
-/
noncomputable section
namespace Reinmann.WeilGroundFourier

/-- Spectral mass outside a unit ground eigenvector, for a unit form-domain
trial. The last inequality is the FULL spectral energy lower estimate. -/
def FormProjectionHypothesis (mu ground second mass : ℝ) : Prop :=
  0 ≤ mass ∧ mass ≤ 1 ∧ ground * (1 - mass) + second * mass ≤ mu

theorem orthogonal_mass_le {mu ground second mass lower next : ℝ}
    (h : FormProjectionHypothesis mu ground second mass)
    (hl : lower ≤ ground) (hn : next ≤ second) (hg : lower < next) :
    mass ≤ (mu - lower) / (next - lower) := by
  obtain ⟨hm, hm1, he⟩ := h
  have ha := mul_le_mul_of_nonneg_right hl (sub_nonneg.mpr hm1)
  have hb := mul_le_mul_of_nonneg_right hn hm
  apply (le_div_iff₀ (sub_pos.mpr hg)).mpr
  nlinarith

/-- The phase is chosen so overlap is real nonnegative. -/
theorem overlap_lower {overlap mass q : ℝ}
    (ho : 0 ≤ overlap) (hp : overlap ^ 2 + mass = 1) (hm : mass ≤ q) :
    Real.sqrt (1 - q) ≤ overlap := by
  exact Real.sqrt_le_iff.mpr ⟨ho, by nlinarith⟩

theorem phase_distance_sq_le {distance overlap mass q : ℝ}
    (ho : 0 ≤ overlap) (hp : overlap ^ 2 + mass = 1)
    (hm0 : 0 ≤ mass) (hm : mass ≤ q)
    (hd : distance ^ 2 = 2 - 2 * overlap) : distance ^ 2 ≤ 2 * q := by
  have ho1 : overlap ≤ 1 := by nlinarith
  have hprod := mul_nonneg ho (sub_nonneg.mpr ho1)
  nlinarith

/-- The Fourier-functional bound is an analytic input; this is not its proof. -/
theorem observable_error_le {error K distance q : ℝ}
    (hK : 0 ≤ K) (hd : 0 ≤ distance) (hq : 0 ≤ q)
    (hs : distance ^ 2 ≤ 2 * q) (he : |error| ≤ K * distance) :
    |error| ≤ K * Real.sqrt (2 * q) := by
  have ht : distance ≤ Real.sqrt (2 * q) :=
    (Real.le_sqrt hd (by positivity)).mpr hs
  exact he.trans (mul_le_mul_of_nonneg_left ht hK)

/-- A mean estimate protects Fourier normalization at zero without a trace. -/
theorem origin_mean_pos {trialMean groundMean distance : ℝ}
    (he : |trialMean - groundMean| ≤ distance) (hc : distance < trialMean) :
    0 < groundMean := by
  obtain ⟨_, hh⟩ := abs_le.mp he
  linarith

end Reinmann.WeilGroundFourier
