import Reinmann.WeilResidualTrace

/-!
# Actual-trial residual obstruction interface

All operator, form and renewal facts remain named hypotheses. In
particular a coefficient outside a trial space can bound the FULL residual
from below; a zero projected residual does not bound it from above.
-/
noncomputable section
namespace Reinmann.WeilTrialResidual

/-- The residual coefficient of a unit test vector, before normalization,
and a certified change from the saved cosine coefficient. -/
def FullResidualProbeHypothesis (coupling probe change norm residual : ℝ) : Prop :=
  |coupling - probe| ≤ change ∧ |probe| ≤ norm * residual

theorem full_residual_lower {coupling probe change norm residual : ℝ}
    (h : FullResidualProbeHypothesis coupling probe change norm residual)
    (hn : 0 < norm) : (|coupling| - change) / norm ≤ residual := by
  have ht : |coupling| ≤ |coupling - probe| + |probe| := by
    calc
      |coupling| = |(coupling - probe) + probe| := by congr 1; ring
      _ ≤ |coupling - probe| + |probe| := abs_add_le _ _
  apply (div_le_iff₀ hn).mpr
  nlinarith [h.1, h.2]

/-- Actual normalized traces of the assembled operator-domain trial,
after the written linearity/zero-trace smooth-part argument. -/
def ExactTrialTraceHypothesis (trace coefficient renewal norm : ℝ) : Prop :=
  trace = coefficient * renewal / norm

theorem exact_trial_trace_interval {trace coefficient renewal norm lo hi : ℝ}
    (h : ExactTrialTraceHypothesis trace coefficient renewal norm)
    (hc : 0 ≤ coefficient) (hj : 0 ≤ renewal)
    (hl : 0 < lo) (hln : lo ≤ norm) (hnh : norm ≤ hi) :
    coefficient * renewal / hi ≤ trace ∧ trace ≤ coefficient * renewal / lo := by
  change trace = coefficient * renewal / norm at h
  rw [h]
  have hn : 0 < norm := lt_of_lt_of_le hl hln
  constructor
  · exact div_le_div_of_nonneg_left (mul_nonneg hc hj) hn hnh
  · exact div_le_div_of_nonneg_left (mul_nonneg hc hj) hl hln

/-- A positive trial trace need not give a positive minimizing-state trace.
This proves failure of the sufficient linear-residual certificate whenever
even its L2 contribution exceeds the trial-trace upper bound. -/
theorem trace_gate_obstruction {A B lower residual epsilon₂ epsilonInf trialUpper : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hi : 0 ≤ epsilonInf)
    (hl : lower ≤ residual) (he : residual ≤ epsilon₂)
    (hf : trialUpper < A * lower) : trialUpper < A * epsilon₂ + B * epsilonInf := by
  have hm := mul_le_mul_of_nonneg_left (le_trans hl he) hA
  have hb := mul_nonneg hB hi
  linarith

/-- Cauchy--Schwarz in the ACTUAL positive form supplies the cross bound.
No finite matrix form is substituted for the actual form. -/
def PositiveFormExpansionHypothesis (trial base cross error : ℝ) : Prop :=
  trial = base + 2 * cross + error ∧ |cross| ≤ Real.sqrt (base * error)

theorem positive_form_rayleigh_change {trial base cross error : ℝ}
    (h : PositiveFormExpansionHypothesis trial base cross error)
    (he : 0 ≤ error) : |trial - base| ≤ 2 * Real.sqrt (base * error) + error := by
  have ht : |2 * cross + error| ≤ 2 * |cross| + error := by
    calc
      |2 * cross + error| ≤ |2 * cross| + |error| := abs_add_le _ _
      _ = 2 * |cross| + error := by rw [abs_mul, abs_of_nonneg he]; norm_num
  rw [h.1]
  have hid : base + 2 * cross + error - base = 2 * cross + error := by ring
  rw [hid]
  linarith [h.2]

/-- Written cutoff estimates furnish arbitrarily small ACTUAL L2 graph
norms at fixed nonzero trace. The analytic family is an explicit input. -/
def FixedTraceSmallGraphHypothesis {α : Type*} (Eligible : α → Prop)
    (graph trace : α → ℝ) (J : ℝ) : Prop :=
  ∀ epsilon > 0, ∃ f, Eligible f ∧ graph f < epsilon ∧ trace f = J

/-- No uniform graph-norm trace estimate follows from a complementary
spectral gap. This scalar obstruction needs the written cutoff family. -/
theorem fixed_trace_graph_obstruction {α : Type*} {Eligible : α → Prop}
    {graph trace : α → ℝ} {J C : ℝ}
    (h : FixedTraceSmallGraphHypothesis Eligible graph trace J)
    (hJ : 0 < J) (hC : 0 ≤ C) (hg : ∀ f, Eligible f → 0 ≤ graph f) :
    ∃ f, Eligible f ∧ C * graph f < |trace f| := by
  have hp : 0 < C + 1 := by linarith
  obtain ⟨f, hf, hsmall, ht⟩ := h (J / (C + 1)) (div_pos hJ hp)
  have hprod : graph f * (C + 1) < J := (lt_div_iff₀ hp).mp hsmall
  refine ⟨f, hf, ?_⟩
  rw [ht, abs_of_pos hJ]
  nlinarith [hg f hf]

end Reinmann.WeilTrialResidual
