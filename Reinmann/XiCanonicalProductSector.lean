/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.CanonicalZeroIndex
import Reinmann.XiZeroCorrespondence

/-! A canonical multiplicity index for the actual folded-Xi sector application.
The product identity and inverse-zero summability are still unproved inputs.
Conjugation indexing and strip correspondence are constructed here. -/
noncomputable section
namespace Reinmann.XiCanonicalProductSector

abbrev Index := CanonicalZeroIndex.Index foldedXi

def value (i : Index) : ℂ := CanonicalZeroIndex.value i

theorem foldedXi_zero_ne : foldedXi 0 ≠ 0 := by
  intro hz
  have hr := congrArg Complex.re hz
  exact (ne_of_gt foldedXi_zero_re_pos) hr

/-- All actual zeros occur, without a simplicity assumption. -/
theorem exists_value_iff (z : ℂ) : (∃ i : Index, value i = z) ↔ foldedXi z = 0 :=
  CanonicalZeroIndex.exists_value_iff differentiable_foldedXi foldedXi_zero_ne z

/-- Each folded zero occurs exactly its analytic multiplicity many times. -/
theorem fiber_card (z : ℂ) :
    Nat.card {i : Index // value i = z} = analyticOrderNatAt foldedXi z :=
  CanonicalZeroIndex.fiber_card foldedXi z

theorem value_ne_zero (i : Index) : value i ≠ 0 :=
  CanonicalZeroIndex.value_ne_zero foldedXi_zero_ne i

def conjugate : Index → Index :=
  CanonicalZeroIndex.conjugate differentiable_foldedXi foldedXi_conj

theorem conjugate_involutive : Function.Involutive conjugate :=
  CanonicalZeroIndex.conjugate_involutive differentiable_foldedXi foldedXi_conj

theorem value_conjugate (i : Index) : value (conjugate i) = star (value i) := rfl

def stripLift (i : Index) : ℂ := 1 / 2 + Complex.sqrt (value i)

theorem stripLift_zero (i : Index) : IsCriticalStripZero (stripLift i) :=
  XiZeroCorrespondence.folded_zero_strip (CanonicalZeroIndex.value_zero i)

theorem stripLift_fold (i : Index) : value i = (stripLift i - 1 / 2) ^ 2 := by
  simpa only [stripLift, add_sub_cancel_left] using (complex_sqrt_sq (value i)).symm

/-- Only two analytic inputs remain for the named bridge: summability over the
canonical multiplicity index and the actual, normalized product identity. -/
theorem katkovaSectorBridge_of_canonical_product
    (hsum : Summable (fun i : Index => ‖(value i)⁻¹‖))
    (hproduct : ∀ z, foldedXi z = (XiMomentCoeff 0 : ℂ) *
      ∏' i : Index, (1 - (value i)⁻¹ * z)) {m : ℕ} (hm : 0 < m) :
    KatkovaSectorBridge m :=
  XiGenusZeroSector.katkovaSectorBridge_of_strip_indexed_product
    conjugate_involutive value_conjugate value_ne_zero hsum stripLift
    stripLift_zero stripLift_fold hproduct hm

end Reinmann.XiCanonicalProductSector
