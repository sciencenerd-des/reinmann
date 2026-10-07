import Reinmann.WeilTraceStability

/-!
# Full-residual trace certificate interface

These are scalar consequences of named analytic inputs. The projection
estimate must concern the full operator and a unit operator-domain trial.
The heat/forcing/Green estimates, trial residuals and actual trial traces
are not supplied by this module, nor introduced as axioms.
-/
noncomputable section
namespace Reinmann.WeilResidualTrace

/-- Pythagoras and full complementary spectral clearance, after division
by that clearance. `rho` is the full L2 residual-to-clearance ratio. -/
def ResidualProjectionHypothesis (overlap complement rho : ℝ) : Prop :=
  0 ≤ overlap ∧ overlap ^ 2 + complement ^ 2 = 1 ∧
    complement ^ 2 ≤ rho ^ 2

theorem overlap_enclosure {overlap complement rho : ℝ}
    (h : ResidualProjectionHypothesis overlap complement rho) :
    Real.sqrt (1 - rho ^ 2) ≤ overlap ∧ overlap ≤ 1 := by
  constructor
  · exact Real.sqrt_le_iff.mpr ⟨h.1, by nlinarith [h.2.1, h.2.2]⟩
  · nlinarith [sq_nonneg complement, h.2.1, h.1]

theorem overlap_pos {overlap complement rho : ℝ}
    (h : ResidualProjectionHypothesis overlap complement rho)
    (hr : 0 ≤ rho) (hr1 : rho < 1) : 0 < overlap := by
  have hs : 0 < 1 - rho ^ 2 := by nlinarith
  exact lt_of_lt_of_le (Real.sqrt_pos.mpr hs) (overlap_enclosure h).1

/-- The actual heat, localized forcing and signed Green estimates for the
complementary state. `norm` and `forcing` denote nonnegative norm bounds. -/
def ResidualTraceEstimatesHypothesis
    (trace norm forcing e2 ei H J G Q V d : ℝ) : Prop :=
  norm ≤ H * e2 + J * ei ∧ forcing ≤ G * norm + Q * ei ∧
    |trace| ≤ V * ((9 / 4 : ℝ) * forcing + d * norm)

theorem linear_residual_trace_bound
    {trace norm forcing e2 ei H J G Q V d : ℝ}
    (h : ResidualTraceEstimatesHypothesis trace norm forcing e2 ei H J G Q V d)
    (hG : 0 ≤ G) (hV : 0 ≤ V) (hd : 0 ≤ d) :
    |trace| ≤ (V * ((9 / 4 : ℝ) * G + d) * H) * e2 +
      (V * (((9 / 4 : ℝ) * G + d) * J + (9 / 4 : ℝ) * Q)) * ei := by
  have ha : 0 ≤ V * ((9 / 4 : ℝ) * G + d) := by positivity
  have hf := mul_le_mul_of_nonneg_left h.2.1 (show 0 ≤ V * (9 / 4 : ℝ) by positivity)
  have hn := mul_le_mul_of_nonneg_left h.1 ha
  nlinarith [h.2.2]

/-- The actual trace is linear on the chosen trial/ground/complement
decomposition. Endpoint evaluation of a fitted cosine profile is not this
hypothesis. -/
def TraceDecompositionHypothesis (trial overlap actual remainder : ℝ) : Prop :=
  trial = overlap * actual + remainder

/-- Sign-aware quotient enclosure. Supply all four corner bounds for
`[p-error,q+error] / [s,1]`; no positivity of the trace is assumed. -/
theorem signed_trace_enclosure {trial overlap actual remainder p q error s lo hi : ℝ}
    (h : TraceDecompositionHypothesis trial overlap actual remainder)
    (hs : 0 < s) (hsc : s ≤ overlap) (hc1 : overlap ≤ 1)
    (hp : p ≤ trial) (hq : trial ≤ q) (he : |remainder| ≤ error)
    (hl : lo ≤ p - error) (hls : lo ≤ (p - error) / s)
    (hh : q + error ≤ hi) (hhs : (q + error) / s ≤ hi) :
    lo ≤ actual ∧ actual ≤ hi := by
  have hc : 0 < overlap := lt_of_lt_of_le hs hsc
  have hls' : lo * s ≤ p - error := (le_div_iff₀ hs).mp hls
  have hhs' : q + error ≤ hi * s := (div_le_iff₀ hs).mp hhs
  obtain ⟨herl, herr⟩ := abs_le.mp he
  have hlo : lo * overlap ≤ p - error := by
    by_cases hn : 0 ≤ lo
    · have hm := mul_le_mul_of_nonneg_left hc1 hn
      nlinarith
    · have hm := mul_le_mul_of_nonpos_left hsc (le_of_not_ge hn)
      linarith
  have hhi : q + error ≤ hi * overlap := by
    by_cases hn : 0 ≤ hi
    · have hm := mul_le_mul_of_nonneg_left hsc hn
      linarith
    · have hm := mul_le_mul_of_nonpos_left hc1 (le_of_not_ge hn)
      nlinarith
  change trial = overlap * actual + remainder at h
  constructor
  · apply (mul_le_mul_iff_right₀ hc).mp
    nlinarith
  · apply (mul_le_mul_iff_right₀ hc).mp
    nlinarith

end Reinmann.WeilResidualTrace
