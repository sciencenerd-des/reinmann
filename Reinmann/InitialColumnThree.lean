/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.XiMomentKernel
import Reinmann.RHTheoremTargets

/-!
# Full-support initial-column `3 × 3` expansion

This module removes the support condition from the first unresolved
initial-column minor.  It proves only an exact algebraic identity: positivity
of the resulting six-term expression remains an open Xi-specific inequality.
-/

noncomputable section

open Matrix

namespace Reinmann

/-- Expand a full-support initial-column `3 × 3` Toeplitz minor into its six
signed-moment terms.  The hypothesis `2 ≤ rows 0` ensures that columns
`0, 1, 2` are supported in every selected row. -/
theorem xiInitialColumnMinorThree_det_eq
    (rows : Fin 3 → ℕ)
    (hRows : StrictMono rows)
    (hSupport : 2 ≤ rows 0) :
    (Matrix.of (fun i j : Fin 3 => XiToeplitzEntry (rows i) j.val)).det =
      XiMomentCoeff (rows 0) *
          (XiMomentCoeff (rows 1 - 1) * XiMomentCoeff (rows 2 - 2) -
            XiMomentCoeff (rows 1 - 2) * XiMomentCoeff (rows 2 - 1)) -
        XiMomentCoeff (rows 1) *
          (XiMomentCoeff (rows 0 - 1) * XiMomentCoeff (rows 2 - 2) -
            XiMomentCoeff (rows 0 - 2) * XiMomentCoeff (rows 2 - 1)) +
        XiMomentCoeff (rows 2) *
          (XiMomentCoeff (rows 0 - 1) * XiMomentCoeff (rows 1 - 2) -
            XiMomentCoeff (rows 0 - 2) * XiMomentCoeff (rows 1 - 1)) := by
  have h01 : rows 0 < rows 1 := hRows (by decide)
  have h12 : rows 1 < rows 2 := hRows (by decide)
  have h1 : 2 ≤ rows 1 := le_trans hSupport (Nat.le_of_lt h01)
  have h2 : 2 ≤ rows 2 := le_trans h1 (Nat.le_of_lt h12)
  rw [Matrix.det_fin_three]
  simp only [Matrix.of_apply]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
  rw [xiToeplitzEntry_sub (rows 0) 0 (Nat.zero_le _),
      xiToeplitzEntry_sub (rows 0) 1 (by omega),
      xiToeplitzEntry_sub (rows 0) 2 (by omega),
      xiToeplitzEntry_sub (rows 1) 0 (Nat.zero_le _),
      xiToeplitzEntry_sub (rows 1) 1 (by omega),
      xiToeplitzEntry_sub (rows 1) 2 (by omega),
      xiToeplitzEntry_sub (rows 2) 0 (Nat.zero_le _),
      xiToeplitzEntry_sub (rows 2) 1 (by omega),
      xiToeplitzEntry_sub (rows 2) 2 (by omega)]
  simp only [Nat.sub_zero]
  ring

/-- The consecutive-row initial-column case is already covered by the
contiguous positivity ladder.  This is a base case for any future row-gap
argument, not a proof of the arbitrary-row target. -/
theorem xiInitialColumnMinorThree_nonneg_of_contig
    (hContig : XiContigToeplitzTotalPositive) (m : ℕ) :
    0 ≤ (Matrix.of (fun i j : Fin 3 => XiToeplitzEntry (m + i.val) j.val)).det := by
  exact hContig 3 m

end Reinmann
