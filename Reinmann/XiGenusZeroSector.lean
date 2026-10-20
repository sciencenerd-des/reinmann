/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.RealGenusZeroApproximants
import Reinmann.FoldedSectorGeometry
import Reinmann.XiCenterPositive

/-! Actual folded-Xi instantiations of the genus-zero sector transfer.
These theorems require the explicit product identity and zero indexing;
they do not establish the existence of that data or discharge the bridge. -/
noncomputable section
namespace Reinmann.XiGenusZeroSector

/-- All polynomial and analytic approximation steps are derived from an
explicit product identity for actual folded Xi. The identity is still an input. -/
theorem finitePF_xi_of_genusZero_product {ι : Type*} {sigma : ι → ι}
    (hsigma : Function.Involutive sigma) {a : ι → ℂ}
    (hconj : ∀ i, a (sigma i) = star (a i)) (ha : ∀ i, a i ≠ 0)
    (hsum : Summable (fun i => ‖(a i)⁻¹‖)) {m : ℕ}
    (hsector : ∀ i, Real.pi - Real.pi / ((m : ℝ) + 1) ≤ |Complex.arg (a i)|)
    (hidentity : ∀ z, foldedXi z = (XiMomentCoeff 0 : ℂ) *
      ∏' i, (1 - (a i)⁻¹ * z)) : FinitePF XiMomentCoeff m :=
  RealGenusZeroApproximants.finitePF_of_product_identity hsigma hconj ha hsum
    hsector xiMomentCoeff_zero_pos.le hidentity foldedXi_taylor

/-- The remaining classical data is explicit: an indexed product, its
summability and conjugation action, and its correspondence with strip zeros.
The existing tangent-angle interface then yields the actual named bridge. -/
theorem katkovaSectorBridge_of_strip_indexed_product {ι : Type*} {sigma : ι → ι}
    (hsigma : Function.Involutive sigma) {a : ι → ℂ}
    (hconj : ∀ i, a (sigma i) = star (a i)) (ha : ∀ i, a i ≠ 0)
    (hsum : Summable (fun i => ‖(a i)⁻¹‖)) (s : ι → ℂ)
    (hstrip : ∀ i, IsCriticalStripZero (s i))
    (hfold : ∀ i, a i = (s i - 1 / 2) ^ 2)
    (hidentity : ∀ z, foldedXi z = (XiMomentCoeff 0 : ℂ) *
      ∏' i, (1 - (a i)⁻¹ * z)) {m : ℕ} (hm : 0 < m) :
    KatkovaSectorBridge m := by
  intro hangle
  apply finitePF_xi_of_genusZero_product hsigma hconj ha hsum _ hidentity
  intro i
  have hne : s i ≠ 1 / 2 := by
    intro he
    apply ha i
    rw [hfold i, he]
    norm_num
  rw [hfold i]
  exact FoldedSectorGeometry.arg_folded_sector hm hne (hangle (s i) (hstrip i))

end Reinmann.XiGenusZeroSector
