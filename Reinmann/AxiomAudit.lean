/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.ProofArchitecture
import Reinmann.RHReductionCapstone
import Reinmann.RHTheoremTargets

/-!
# Axiom Audit

This module is a **verification harness**, not part of the mathematical development.
It is intentionally *not* imported by `Reinmann.lean`, so it never enlarges the
dependency footprint of the library proper.

Its sole job is to make the repository's headline claim — that the entire
Riemann-Hypothesis *reduction* chain is proven with no `sorry` and no custom
axioms — machine-checkable in one place.  Every `#print axioms` below must report
only Lean's three foundational axioms:

```
[propext, Classical.choice, Quot.sound]
```

If any theorem here depends on a project-declared axiom or contains `sorryAx`,
the audit script `scripts/verify_axiom_clean.sh` will detect the deviation from
that canonical list and fail.  This is the exact discipline described in
`RHReductionCapstone.lean`: the open RH-equivalent inputs are carried as named
hypotheses (`Prop`s), never as axioms, so the conditional reductions stay honest.
-/

namespace Reinmann.AxiomAudit

-- Core reduction chain: Hilbert–Pólya witness ⟹ RH (spectral branch).
#print axioms riemannHypothesis_of_twoBranchArchitecture

-- Uniqueness branch: same-height uniqueness + conjugate symmetry ⟹ RH.
#print axioms uniqueness_implies_rh

-- Architecture-level packaging of both branches.
#print axioms main_spectral_reduction
#print axioms main_uniqueness_reduction

-- The honest conditional capstone: full PF positivity + classical scaffolding ⟹ RH,
-- and the RH ↔ PF-positivity equivalence that shows why the input cannot be axiomatized.
#print axioms riemannHypothesis_of_pf_and_classical_inputs
#print axioms xiToeplitzTotalPositive_iff_riemannHypothesis

end Reinmann.AxiomAudit
