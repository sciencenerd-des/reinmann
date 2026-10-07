/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.WeilTraceStability

/-!
# Scalar gates for the proposed degenerate-cluster prime-entry law

The boundary rank-two factorization, compact localized resolvents, and
Feshbach eigenvalue-counting identity are written analysis, not asserted
here. Named hypotheses expose the exact Schur and trace errors needed.
No infinite-dimensional operator theorem or novelty claim is axiomatized.
-/
noncomputable section
open Filter Topology
namespace Reinmann.WeilClusterActivation

/-- The nonnegative full-complement Schur cost is smaller than the activation
scale by a factor tending to zero. A fixed spectral gap alone does not give
this hypothesis; the compact resolvent and shrinking support are essential. -/
def LocalizedSchurCostHypothesis (cost scale omega C : ℝ) : Prop :=
  0 ≤ cost ∧ cost ≤ C * omega * scale

theorem localized_cost_ratio {cost scale omega C : ℝ}
    (hs : 0 < scale) (h : LocalizedSchurCostHypothesis cost scale omega C) :
    0 ≤ cost / scale ∧ cost / scale ≤ C * omega := by
  constructor
  · exact div_nonneg h.1 hs.le
  · exact (div_le_iff₀ hs).mpr h.2

theorem localized_cost_vanishes {ι : Type*} {l : Filter ι}
    {cost scale omega : ι → ℝ} {C : ℝ}
    (h : ∀ᶠ x in l, 0 < scale x ∧
      LocalizedSchurCostHypothesis (cost x) (scale x) (omega x) C)
    (hw : Tendsto omega l (𝓝 0)) :
    Tendsto (fun x => cost x / scale x) l (𝓝 0) := by
  have hb : ∀ᶠ x in l, 0 ≤ cost x / scale x ∧
      cost x / scale x ≤ C * omega x := by
    filter_upwards [h] with x hx
    exact localized_cost_ratio hx.1 hx.2
  exact squeeze_zero' (hb.mono fun _ hx => hx.1) (hb.mono fun _ hx => hx.2)
    (by simpa using hw.const_mul C)

/-- Feshbach inertia gives this bracket for an ordered eigenvalue once the
whole complementary block is coercive and its Schur cost is enclosed. -/
def SchurEigenvalueBracketHypothesis (actual head scale omega : ℝ) : Prop :=
  head - omega * scale ≤ actual ∧ actual ≤ head

/-- Separate the Schur error from the boundary-matrix approximation error. -/
theorem normalized_cluster_error {actual head target scale omega rho : ℝ}
    (hs : 0 < scale)
    (hb : SchurEigenvalueBracketHypothesis actual head scale omega)
    (hh : |head - target| ≤ rho * scale) :
    |(actual - target) / scale| ≤ omega + rho := by
  have hc : 0 ≤ omega * scale := by linarith [hb.1, hb.2]
  have ha : |actual - head| ≤ omega * scale := by
    apply abs_le.mpr
    constructor <;> linarith [hb.1, hb.2]
  have ht : |actual - target| ≤ (omega + rho) * scale := by
    calc
      |actual - target| = |(actual - head) + (head - target)| := by congr 1; ring
      _ ≤ |actual - head| + |head - target| := abs_add_le _ _
      _ ≤ (omega + rho) * scale := by nlinarith
  rw [abs_div, abs_of_pos hs]
  exact (div_le_iff₀ hs).mpr ht

theorem cluster_error_tendsto_zero {ι : Type*} {l : Filter ι}
    {actual head target scale omega rho : ι → ℝ}
    (h : ∀ᶠ x in l, 0 < scale x ∧
      SchurEigenvalueBracketHypothesis (actual x) (head x) (scale x) (omega x) ∧
      |head x - target x| ≤ rho x * scale x)
    (hw : Tendsto omega l (𝓝 0)) (hr : Tendsto rho l (𝓝 0)) :
    Tendsto (fun x => (actual x - target x) / scale x) l (𝓝 0) := by
  have hb : ∀ᶠ x in l,
      |(actual x - target x) / scale x| ≤ omega x + rho x := by
    filter_upwards [h] with x hx
    exact normalized_cluster_error hx.1 hx.2.1 hx.2.2
  have hz : Tendsto (fun x => |(actual x - target x) / scale x|) l (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) hb
      (by simpa using hw.add hr)
  exact tendsto_iff_dist_tendsto_zero.mpr (by simpa [Real.dist_eq, abs_div] using hz)

end Reinmann.WeilClusterActivation
