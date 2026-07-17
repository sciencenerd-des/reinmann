/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.RHTheoremTargets
import Reinmann.DodgsonCondensation

/-!
# Contiguous to Full Pólya-Frequency Bridge Target

This module names the target that, for the Riemann xi function's signed Taylor coefficients,
positivity of the contiguous Toeplitz minors implies full total positivity.
Dodgson condensation is a possible ingredient, but by itself it does not close
zero-denominator or arbitrary-index cases.  The upgrade therefore remains an
explicit theorem contract.
-/

noncomputable section

namespace Reinmann

/-- The exact open contiguous-to-full Pólya-frequency theorem target. -/
def XiContigToFullPFTheoremTarget : Prop :=
  XiContigToFullPFBridge

end Reinmann
