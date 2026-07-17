/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.ProofArchitecture
import Reinmann.RHReductionCapstone
import Reinmann.RHTheoremTargets
import Reinmann.LiCriterion
import Reinmann.Order3Certificate
import Reinmann.DodgsonCondensation
import Reinmann.InitialColumnThree
import Reinmann.FeketeRowGap
import Reinmann.GrassmannSyzygy
import Reinmann.FeketeAllOrders
import Reinmann.ToeplitzFullPF
import Reinmann.HyperbolicLimit
import Reinmann.HermitePoulainDerivative
import Reinmann.HermitePoulainComposition
import Reinmann.CauchyCoefficientConvergence
import Reinmann.JensenTuranBridge
import Reinmann.TuranRouteKill

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

-- Frontier advance (Phase 4): the Li-criterion route and the order-3 certificate
-- fragment. Both isolate their open analytic content in named `Prop` hypotheses.
#print axioms li_criterion_iff_rh
#print axioms riemannHypothesis_of_liCriterion
#print axioms completedXi_symmetry
#print axioms momentToeplitzOrder3Positive_of_prefix_and_tail
#print axioms order3DetExpr_pos_certificate
#print axioms momentToeplitzContigMinor_eq_order3DetExpr
#print axioms order3DetNonneg_of_ratio_nonneg
#print axioms order3RatioTailGap_of_scaled_limit
#print axioms XiOrder3PositiveScaledLimit
#print axioms xiToeplitzMinor3_eventually_nonneg_of_scaled_limit
#print axioms weightedMoment_pos_of_pos
#print axioms order3TailGap_of_ratioTailGap
#print axioms momentToeplitzOrder3Positive_of_prefix_and_ratioTail
#print axioms momentToeplitzOrder3RatioExpr_eq_adjacentGap
#print axioms order3RatioGapExpr_nonneg_of_effective_bounds
#print axioms order3RatioTailGap_of_effective_bounds
#print axioms dodgsonCondensationIdentity_fin_two
#print axioms dodgsonCondensationIdentity_fin_three
#print axioms xiInitialColumnMinorThree_det_eq
#print axioms xiInitialColumnMinorThree_nonneg_of_contig

-- Concrete Hermite--Poulain derivative leg and its Mathlib root-count bound.
#print axioms polynomialHyperbolic_derivative_of_degree_pos
#print axioms polynomial_root_count_le_derivative
#print axioms polynomial_coeff_tendsto_of_bounded_degree
#print axioms locallyUniformlyOn_univ_tendsto_real_node
#print axioms locallyUniformlyOn_univ_tendsto_mapped_real_node
#print axioms jensenPoly_one_hyperbolic
#print axioms schurSzegoComposition_one_add_X_pow
#print axioms schurSzegoComposition_one
#print axioms coefficientwiseComposition_not_hyperbolicity_preserver
#print axioms unrestrictedSchurSzegoComposition_not_hyperbolicity_preserver
#print axioms schurSzegoComposition_two
#print axioms schurSzegoComposition_three
#print axioms schurSzegoComposition_two_discriminant_nonneg
#print axioms polynomialHyperbolic_quadratic_of_discriminant
#print axioms schurSzegoComposition_two_hyperbolic_of_discriminant
#print axioms hermitePoulainSchurSzego_two_of_coeff_discriminants
#print axioms jensenPoly_two_hyperbolic_as_schurSzego
#print axioms polynomialRootsSameSign_one_add_X_pow
#print axioms jensenCoeffPoly_coeff
#print axioms hermitePoulainSchurSzego_one
#print axioms JensenPoly_eq_schurSzego_one_add_X_pow

-- Fekete row-gap induction (arbitrary-row initial-column minors).
-- The order-3 named target is closed modulo strict positivity + strict Turán;
-- the k = 4 rung additionally consumes the strict order-3 contiguous rung.
#print axioms xiInitialMinor3_gap_first
#print axioms xiInitialMinor3_gap_second
#print axioms xiMomentCoeff_strict_tp2
#print axioms xiInitialColumnMinorThreeFromContig_of_strictTuran
#print axioms xiInitialColumnMinorThreeFromContig_of_kernelRep_strictTuran
#print axioms xiInitialMinor3_pos
#print axioms xiInitialMinor4_gap_first
#print axioms xiInitialMinor4_gap_second
#print axioms xiInitialMinor4_gap_third
#print axioms xiInitialColumnMinorFourFromContig_of_strictTuran
#print axioms xiInitialColumnMinorGeFourFromContig_of_four_and_geFive
#print axioms kernelContigToPFInitialColumnGeFourTheorem_of_strictTuran_and_geFive

-- Generic Grassmann syzygy and the all-orders Fekete theorem.
-- The arbitrary-row initial-column frontier is closed at EVERY order under the
-- single strict-ladder hypothesis; RH reduces to scaffolding + kernel data +
-- strict ladder + Cryer's criterion. All still conditional; none of the inputs
-- is proved here.
#print axioms maxMinor_syzygy
#print axioms grassmann_three_term
#print axioms xiMomentStrictTuran_of_strictLadder
#print axioms xiInitialMinor_pos_of_strictLadder
#print axioms xiInitialColumnMinorTotalPositive_of_strictLadder
#print axioms xiContigToInitialColumnMinorBridge_of_strictLadder
#print axioms xiInitialColumnMinorGeFourFromContig_of_strictLadder
#print axioms kernelContigToPFInitialColumnGeFourTheorem_of_strictLadder
#print axioms riemannHypothesis_of_strictLadder_and_criterion

-- Full Pólya-frequency positivity from the strict ladder (dominance dichotomy
-- + Toeplitz reversal symmetry). Cryer's criterion and the kernel
-- representation are no longer needed by the sharpest reduction:
-- RH ⟸ classical scaffolding + strict contiguous ladder. Still conditional.
#print axioms xiMinor_eq_zero_of_lt
#print axioms xiMinor_contigRows
#print axioms xiMinor_pos_of_dominant
#print axioms xiToeplitzTotalPositive_of_strictLadder
#print axioms riemannHypothesis_of_strictLadder

-- Scaffolding program, first proved leg: bounded-degree hyperbolic limits are
-- hyperbolic; the Laguerre–Pólya closure bridge reduces to the named Jensen
-- approximation condition.
#print axioms prod_normSq_line_le
#print axioms polynomialHyperbolic_of_tendsto
#print axioms xiLaguerrePolyaClosureBridge_of_jensenApproximation

-- Falsification discipline: the (2nd, 3rd)-Turán window does not close the
-- order-3 contiguous rung at the sequence level; counterexample preserved.
#print axioms turan23_not_imp_toeplitz3

end Reinmann.AxiomAudit
