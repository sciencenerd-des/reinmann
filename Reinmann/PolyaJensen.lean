/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.JensenProgram
import Reinmann.XiPlanePrincipalValue

/-!
# Pólya-Jensen Equivalence Bridge Target

This module names the `PolyaJensenBridge` target, which states that the Riemann
Hypothesis is equivalent to the hyperbolicity of all Jensen polynomials
associated with the Riemann Xi function.  The classical equivalence is not yet
formalized in this repository.
-/

noncomputable section

namespace Reinmann

/-- The exact open Pólya--Jensen theorem target. -/
def PolyaJensenTheoremTarget : Prop :=
  PolyaJensenBridge

end Reinmann
