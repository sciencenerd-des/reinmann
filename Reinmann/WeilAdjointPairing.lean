import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Ground-angle bounds for full adjoint residuals

These Hilbert-space inequalities justify retaining the actual finite-trial
pairing in an adjoint certificate. They do not construct the Weil operator,
prove its domain identities, or supply its ground-state angle. Those analytic
and certificate obligations remain separate.
-/
noncomputable section
open scoped InnerProductSpace

namespace Reinmann.WeilAdjointPairing
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- An orthogonal ground remainder only sees the trial-orthogonal residual. -/
theorem pairing_le_of_decomposition {u g w v : E} {c : ℂ} {s : ℝ}
    (hu : u = c • g + w) (horth : ⟪w, g⟫_ℂ = 0)
    (hc : ‖c‖ ≤ 1) (hw : ‖w‖ ≤ s) :
    ‖⟪u, v⟫_ℂ‖ ≤ ‖⟪g, v⟫_ℂ‖ + s * ‖v - ⟪g, v⟫_ℂ • g‖ := by
  have hproject : ⟪w, v - ⟪g, v⟫_ℂ • g⟫_ℂ = ⟪w, v⟫_ℂ := by
    simp [inner_sub_right, inner_smul_right, horth]
  rw [hu, inner_add_left, inner_smul_left, ← hproject]
  calc
    ‖(starRingEnd ℂ c) * ⟪g, v⟫_ℂ + ⟪w, v - ⟪g, v⟫_ℂ • g⟫_ℂ‖
        ≤ ‖(starRingEnd ℂ c) * ⟪g, v⟫_ℂ‖ + ‖⟪w, v - ⟪g, v⟫_ℂ • g⟫_ℂ‖ := norm_add_le _ _
    _ ≤ ‖⟪g, v⟫_ℂ‖ + s * ‖v - ⟪g, v⟫_ℂ • g‖ := by
      apply add_le_add
      · simpa only [norm_mul, RCLike.norm_conj, one_mul] using
          mul_le_mul_of_nonneg_right hc (norm_nonneg ⟪g, v⟫_ℂ)
      · exact (norm_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_right hw (norm_nonneg _))

/-- Canonical unit-trial version; the supplied angle is a genuine Hilbert norm. -/
theorem pairing_le_of_unit_trial {u g v : E} {s : ℝ}
    (hu : ‖u‖ = 1) (hg : ‖g‖ = 1)
    (hangle : ‖u - ⟪g, u⟫_ℂ • g‖ ≤ s) :
    ‖⟪u, v⟫_ℂ‖ ≤ ‖⟪g, v⟫_ℂ‖ + s * ‖v - ⟪g, v⟫_ℂ • g‖ := by
  apply pairing_le_of_decomposition
      (u := u) (g := g) (w := u - ⟪g, u⟫_ℂ • g) (c := ⟪g, u⟫_ℂ)
  · simpa only [add_sub_assoc] using (add_sub_cancel_left (⟪g, u⟫_ℂ • g) u).symm
  · rw [inner_sub_left, inner_smul_left, inner_self_eq_norm_sq_to_K, hg]
    simp [inner_conj_symm]
  · simpa only [hg, hu, one_mul] using norm_inner_le_norm g u
  · exact hangle

/-- Pythagoras justifies subtracting the measured pairing from a full norm. -/
theorem orthogonal_remainder_sq {g v : E} (hg : ‖g‖ = 1) :
    ‖v - ⟪g, v⟫_ℂ • g‖ ^ 2 = ‖v‖ ^ 2 - ‖⟪g, v⟫_ℂ‖ ^ 2 := by
  have horth : ⟪v - ⟪g, v⟫_ℂ • g, ⟪g, v⟫_ℂ • g⟫_ℂ = 0 := by
    rw [inner_smul_right, inner_sub_left, inner_smul_left,
      inner_self_eq_norm_sq_to_K, hg]
    simp [inner_conj_symm]
  have hp := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (v - ⟪g, v⟫_ℂ • g) (⟪g, v⟫_ℂ • g) horth
  rw [sub_add_cancel, norm_smul, hg, mul_one] at hp
  linarith

/-- The refined estimate may always be intersected with ordinary Cauchy--Schwarz. -/
theorem pairing_le_min {u g v : E} {s : ℝ}
    (hu : ‖u‖ = 1) (hg : ‖g‖ = 1)
    (hangle : ‖u - ⟪g, u⟫_ℂ • g‖ ≤ s) :
    ‖⟪u, v⟫_ℂ‖ ≤ min ‖v‖ (‖⟪g, v⟫_ℂ‖ + s * ‖v - ⟪g, v⟫_ℂ • g‖) := by
  apply le_min
  · simpa only [hu, one_mul] using norm_inner_le_norm u v
  · exact pairing_le_of_unit_trial hu hg hangle

/-- Selected action values suffice; no globally defined unbounded action is assumed. -/
theorem residual_pairing_identity {u h k r action : E} {lam nu : ℂ}
    (haction : ⟪u, action⟫_ℂ = lam * ⟪u, h⟫_ℂ)
    (hres : r = action - nu • h - k) :
    ⟪u, k⟫_ℂ = (lam - nu) * ⟪u, h⟫_ℂ - ⟪u, r⟫_ℂ := by
  rw [hres, inner_sub_right, inner_sub_right, inner_smul_right, haction]
  ring

/-- Combine separately certified ground pairings for the residual and correction. -/
theorem adjoint_pairing_le {u h k r action : E} {lam nu : ℂ} {delta R H : ℝ}
    (haction : ⟪u, action⟫_ℂ = lam * ⟪u, h⟫_ℂ)
    (hres : r = action - nu • h - k) (hdelta : ‖lam - nu‖ ≤ delta)
    (hR : ‖⟪u, r⟫_ℂ‖ ≤ R) (hH : ‖⟪u, h⟫_ℂ‖ ≤ H) :
    ‖⟪u, k⟫_ℂ‖ ≤ R + delta * H := by
  rw [residual_pairing_identity haction hres]
  have hd : 0 ≤ delta := (norm_nonneg _).trans hdelta
  calc
    ‖(lam - nu) * ⟪u, h⟫_ℂ - ⟪u, r⟫_ℂ‖
        ≤ ‖(lam - nu) * ⟪u, h⟫_ℂ‖ + ‖⟪u, r⟫_ℂ‖ := norm_sub_le _ _
    _ ≤ delta * H + R := by
      apply add_le_add _ hR
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right hdelta (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left hH hd)
    _ = R + delta * H := add_comm _ _

end Reinmann.WeilAdjointPairing
