/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.ContigToFullPF
import Reinmann.VanDantzigOperator
import Reinmann.RHReductionCapstone

/-!
# Global Conditional Capstone for the Riemann Hypothesis

This module packages the current global reduction.  It is conditional: the
classical Toeplitz scaffolding and the xi-specific initial-column theorem target
must both be supplied.  Neither bundle is postulated as an axiom.
-/

noncomputable section

namespace Reinmann

/-- The two explicit bundles needed by the current global capstone. -/
structure GlobalCapstoneInputs where
  classical : ClassicalToeplitzScaffolding
  xiSpecific : KernelContigToPFInitialColumnGeFourTheorem

/-- The honest global capstone: completed classical scaffolding plus the
xi-specific kernel/initial-column theorem target imply RH. -/
theorem riemannHypothesis_of_globalCapstoneInputs
    (inputs : GlobalCapstoneInputs) : RiemannHypothesis :=
  riemannHypothesis_of_kernelContigToPFInitialColumnGeFour
    inputs.classical inputs.xiSpecific

end Reinmann
