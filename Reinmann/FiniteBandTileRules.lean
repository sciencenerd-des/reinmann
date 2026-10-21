/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.RectangleTileRules
import Reinmann.FiniteBandBounds

/-! The existing finite-jet variation rule, with a newly proved height-32
coefficient majorant. No zero exclusion is assumed. -/
noncomputable section
namespace Reinmann.FiniteBandTileRules
open Finset Metric CertifiedTaylorModel CertifiedTaylorComposition RectangleTileRules

theorem xi_derivative_le {d : ℕ} {a : Jet d} {c z : ℂ} {r K : ℚ}
    (hc : c ∈ XiAdaptiveTiles.quarter 32) (ha : Sound a xiCompleted c)
    (hr0 : 0 < r) (hr1 : r < 1) (hK : derivativeBudget a r ≤ K)
    (hz : ‖z - c‖ ≤ (r : ℝ)) : ‖deriv xiCompleted z‖ ≤ (K : ℝ) := by
  have hC (n : ℕ) : ‖coefficient xiCompleted c n‖ ≤ 1000 := by
    apply FiniteBandBounds.taylor_coefficient_bound hc.1 hc.2.1
    simpa only [abs_of_nonneg hc.2.2.1] using hc.2.2.2
  have hp := derivative_bound differentiable_xiCompleted d
    (by exact_mod_cast hr0) (by exact_mod_cast hr1) hz hC
  have hhead :
      (∑ n ∈ range d, ((n + 1 : ℕ) : ℝ) * ‖coefficient xiCompleted c (n + 1)‖ * (r : ℝ) ^ n) ≤
      ((∑ n ∈ range d, (n + 1 : ℚ) *
        (size (CertifiedTaylorModel.get a (n + 1)).centre + (CertifiedTaylorModel.get a (n + 1)).radius) * r ^ n : ℚ) : ℝ) := by
    push_cast
    apply Finset.sum_le_sum
    intro n hn
    have hlt : n + 1 < d + 1 := by simp only [mem_range] at hn; omega
    have hb : ‖coefficient xiCompleted c (n + 1)‖ ≤
        ((size (CertifiedTaylorModel.get a (n + 1)).centre + (CertifiedTaylorModel.get a (n + 1)).radius : ℚ) : ℝ) := by
      simpa only [CertifiedTaylorModel.get, dif_pos hlt] using norm_le_of_contains (ha ⟨n + 1, hlt⟩)
    push_cast at hb
    gcongr
  have hbudget :
      ((∑ n ∈ range d, (n + 1 : ℚ) *
        (size (CertifiedTaylorModel.get a (n + 1)).centre + (CertifiedTaylorModel.get a (n + 1)).radius) * r ^ n : ℚ) : ℝ) +
      1000 * (r : ℝ) ^ d * ((r : ℝ) / (1 - r) ^ 2 + ((d : ℝ) + 1) / (1 - r)) =
      (derivativeBudget a r : ℝ) := by
    push_cast [derivativeBudget]
    ring
  calc
    _ ≤ _ := hp
    _ ≤ _ := add_le_add hhead le_rfl
    _ = (derivativeBudget a r : ℝ) := hbudget
    _ ≤ (K : ℝ) := by exact_mod_cast hK

/-- The numerical module supplies only rational checks and the sound jet.
All derivative-series and nonvanishing reasoning is reused at every centre. -/
theorem certified_tile_nonzero {d : ℕ} {a : Jet d} {c z : ℂ} {r K L : ℚ}
    (hc : c ∈ XiAdaptiveTiles.quarter 32) (ha : Sound a xiCompleted c)
    (hr0 : 0 < r) (hr1 : r < 1) (hK0 : 0 ≤ K) (hK : derivativeBudget a r ≤ K)
    (hL0 : 0 ≤ L) (hL : L ^ 2 ≤ (a ⟨0, by omega⟩).centre.1 ^ 2 +
      (a ⟨0, by omega⟩).centre.2 ^ 2)
    (hmargin : (a ⟨0, by omega⟩).radius + K * r < L)
    (hz : ‖z - c‖ ≤ (r : ℝ)) : xiCompleted z ≠ 0 := by
  have hreal : ((a ⟨0, by omega⟩).radius : ℝ) + (K : ℝ) * r < ‖value (a ⟨0, by omega⟩).centre‖ :=
    (show ((a ⟨0, by omega⟩).radius : ℝ) + (K : ℝ) * r < (L : ℝ) by exact_mod_cast hmargin).trans_le
      (norm_lower hL0 hL)
  have hcover := XiAdaptiveTiles.adaptive_cover_nonzero (n := 1)
    (f := xiCompleted) (S := Metric.closedBall c (r : ℝ))
    (fun _ => Metric.closedBall c (r : ℝ)) (fun _ => c)
    (fun _ => value (a ⟨0, by omega⟩).centre) (fun _ => (r : ℝ))
    (fun _ => (K : ℝ)) (fun _ => ((a ⟨0, by omega⟩).radius : ℝ))
    (fun _ => convex_closedBall c (r : ℝ)) (fun _ => by simp [hr0.le])
    (fun _ w _ => differentiable_xiCompleted w) (fun _ => by change (0 : ℝ) ≤ (K : ℝ); exact_mod_cast hK0)
    (fun _ _ hw => xi_derivative_le hc ha hr0 hr1 hK (mem_closedBall_iff_norm.mp hw))
    (fun _ => centre_contains ha)
    (fun w hw => ⟨⟨0, by omega⟩, hw, mem_closedBall_iff_norm.mp hw⟩)
    (fun _ => hreal)
  exact hcover z (mem_closedBall_iff_norm.mpr hz)

end Reinmann.FiniteBandTileRules
