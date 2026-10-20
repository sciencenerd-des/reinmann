/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.RegularizedEulerMaclaurin
import Reinmann.UniformXiRemainders
import Reinmann.RectangleTaylor
import Reinmann.RectangleTileRules
import Reinmann.RationalBallCover
import Reinmann.RectangleFiniteFormulas
import Reinmann.RectangleLogInputs
import Reinmann.RectangleModel
import Reinmann.CertifiedTaylorModel
import Reinmann.CertifiedComplexInputs
import Reinmann.CertifiedTaylorComposition
import Reinmann.CertifiedHorner
import Reinmann.HardTileLogInputs
import Reinmann.HardTileGammaLog
import Reinmann.HardTileGammaLogJet
import Reinmann.CertifiedScalarExp
import Reinmann.CertifiedTaylorInputs
import Reinmann.HardTilePowerInputs
import Reinmann.HardTileFiniteIdentities
import Reinmann.HardTileFiniteJets
import Reinmann.TaylorDerivativeTail
import Reinmann.HardTileXi
import Reinmann.StirlingCell
import Reinmann.StirlingSum
import Reinmann.StirlingGamma
import Reinmann.StirlingAnalytic
import Reinmann.ZetaJetRemainder
import Reinmann.EulerMaclaurinFinite
import Reinmann.EulerMaclaurinZeta
import Reinmann.EulerMaclaurinAnalytic
import Reinmann.BernoulliQuadrature
import Reinmann.BernoulliBernsteinBounds
import Reinmann.EulerMaclaurinCell
import Reinmann.EulerMaclaurinTail
import Reinmann.GammaReflectionMajorant
import Reinmann.AnalyticSplitPair
import Reinmann.AnalyticToeplitzJacobi
import Reinmann.GammaHeightMajorant
import Reinmann.XiAdaptiveTiles
import Reinmann.XiLocalCauchy
import Reinmann.XiFirstTile
import Reinmann.SplitPairMixedRows
import Reinmann.SplitPairPatchedRemainder
import Reinmann.SplitPairCoefficientIdentity
import Reinmann.WeilWindowAudit
import Reinmann.XiMellinRectangle
import Reinmann.FiniteProductSplitPairControl
import Reinmann.ToeplitzComplementSigned
import Reinmann.SplitPairCauchyTail
import Reinmann.XiFiniteTheta
import Reinmann.EnclosureRules
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
import Reinmann.EffectiveAssembly
import Reinmann.FinitePFBaseline
import Reinmann.QuasiRHInputs
import Reinmann.FinitePFStrict
import Reinmann.AnalyticPFLimit
import Reinmann.XiTaylorIdentification
import Reinmann.TuranDeficit
import Reinmann.WeilRankTail
import Reinmann.CanonicalZeroIndex
import Reinmann.FinitePFAnalyticLimits
import Reinmann.FinitePFConvolution
import Reinmann.FinitePFLimits
import Reinmann.FoldedSectorGeometry
import Reinmann.GenusZeroProductLimits
import Reinmann.MatrixMinorProduct
import Reinmann.PolynomialSectorPF
import Reinmann.QuadraticPF
import Reinmann.RealGenusZeroApproximants
import Reinmann.XiCanonicalProductSector
import Reinmann.XiGenusZeroSector
import Reinmann.XiZeroCorrespondence
import Reinmann.XiHadamardProduct
import Lean.Util.CollectAxioms
import Reinmann.CoupledRankEnergy
import Reinmann.FiniteShiftChains
import Reinmann.SupportTranslation
import Reinmann.SupportPrimeForm
import Reinmann.CurvatureControls
import Reinmann.CoupledRankEnergy
import Reinmann.WeilRankTail

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
#print axioms schurSzegoComposition_three_one_add_X_pow_hyperbolic
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

-- Effective assembly (receptor architecture): per-order kernel certificates
-- propagate to the strict ladder and to RH; the general Schur–Szegő target
-- instantiates at the Jensen factor with all side conditions discharged.
#print axioms xiToeplitzContigMinor_pos_iff_moment_of_kernelRep
#print axioms kernelLadderStrict_of_certificates
#print axioms kernelEffectiveCertificates_iff_ladder
#print axioms xiContigToeplitzStrictPositive_of_kernelLadder
#print axioms riemannHypothesis_of_effectiveCertificates
#print axioms order3TailGap_of_kernelTailStrict
#print axioms polynomialHyperbolic_one_add_X_pow
#print axioms jensenPoly_hyperbolic_of_hpss
#print axioms allJensenHyperbolic_of_hpss
#print axioms riemannHypothesis_of_hpss_route

-- New finite-baseline transport and deficit algebra, not analytic Xi proofs.
#print axioms finitePF_mono
#print axioms finitePF_nonneg_scale
#print axioms finitePF_iff_upper
#print axioms xi_contig_nonneg_of_finitePF
#print axioms xi_fullPF_iff_all_finite
#print axioms order3_deficit_identity
#print axioms order3_pos_of_deficit_slack
#print axioms condensation_pos_of_quantitative_bound

-- Quantitative recurrence continuation: abstract induction and exact controls.
#print axioms all_ranks_pos_of_quantitative_condensation
#print axioms shiftedExponentialGamma_logConcave
#print axioms exponential_shift_rank2_bound_fails
#print axioms rank2_scaled_deficit_factorization
#print axioms rank2_logConcave_of_gamma_and_scaled_deficit

end Reinmann.AxiomAudit

#print axioms Reinmann.rank_slope_eq_cumulative_correction
#print axioms Reinmann.rank_lower_bound_of_cumulative_budget

#print axioms Reinmann.boundary_ratio_le_one_iff

-- Exact signed tail algebra and coupled rank energy. The infinite-series
-- result has explicit energy hypotheses, not an unproved Weil specialization.
#print axioms Reinmann.WeilRankTail.paired_displacement
#print axioms Reinmann.WeilRankTail.geometric_remainder
#print axioms Reinmann.WeilRankTail.geometric_remainder_abs
#print axioms Reinmann.WeilRankTail.paired_even_tail
#print axioms Reinmann.WeilRankTail.denominator_remainder
#print axioms Reinmann.WeilRankTail.weighted_moment_remainder

-- Actual support decomposition and the uniform prime integral form.
-- Boundary traces are not erased and the full Weil gap is not assumed.
#print axioms Reinmann.SupportTranslation.memLp_translate
#print axioms Reinmann.SupportTranslation.integrable_energy
#print axioms Reinmann.SupportTranslation.integrable_real_inner
#print axioms Reinmann.SupportTranslation.ae_support_Ioc_of_Icc
#print axioms Reinmann.SupportTranslation.translated_interval_partition
#print axioms Reinmann.SupportTranslation.energy_disintegration
#print axioms Reinmann.SupportTranslation.correlation_disintegration
#print axioms Reinmann.SupportTranslation.chain_bound_one
#print axioms Reinmann.SupportTranslation.chain_bound_two
#print axioms Reinmann.SupportTranslation.chain_bound_three
#print axioms Reinmann.SupportTranslation.chain_bound_five
#print axioms Reinmann.SupportTranslation.translation_bound
#print axioms Reinmann.SupportTranslation.translation_two
#print axioms Reinmann.SupportTranslation.translation_three
#print axioms Reinmann.SupportTranslation.translation_five
#print axioms Reinmann.SupportTranslation.translation_disjoint
#print axioms Reinmann.SupportPrimeForm.correlation_neg
#print axioms Reinmann.SupportPrimeForm.paired_correlation
#print axioms Reinmann.SupportPrimeForm.complex_correlation
#print axioms Reinmann.SupportPrimeForm.complexCorrelation_translate
#print axioms Reinmann.SupportPrimeForm.integrable_complex_product
#print axioms Reinmann.SupportPrimeForm.complexCorrelation_re
#print axioms Reinmann.SupportPrimeForm.complexCorrelation_neg
#print axioms Reinmann.SupportPrimeForm.paired_complexCorrelation
#print axioms Reinmann.SupportPrimeForm.powers_complete
#print axioms Reinmann.SupportPrimeForm.powers_subset_range
#print axioms Reinmann.SupportPrimeForm.mem_active_iff
#print axioms Reinmann.SupportPrimeForm.complexPrimeForm_eq
#print axioms Reinmann.SupportPrimeForm.allowance_eq
#print axioms Reinmann.SupportPrimeForm.primeForm_eq_prime_power_sum
#print axioms Reinmann.SupportPrimeForm.weight_nonneg
#print axioms Reinmann.SupportPrimeForm.chainConstant_nonneg
#print axioms Reinmann.SupportPrimeForm.support_guard
#print axioms Reinmann.SupportPrimeForm.allowed_chain
#print axioms Reinmann.SupportPrimeForm.logarithmic_support_guard
#print axioms Reinmann.SupportPrimeForm.individual_bound
#print axioms Reinmann.SupportPrimeForm.primeForm_bound
#print axioms Reinmann.SupportPrimeForm.complexPrimeForm_bound
#print axioms Reinmann.SupportPrimeForm.correlation_zero_of_cutoff_le
#print axioms Reinmann.WeilRankTail.rounded_forcing_energy_bound
#print axioms Reinmann.WeilRankTail.coarse_forcing_rounding_exceeds_energy_bound
#print axioms Reinmann.CoupledRankEnergy.galerkin_increment_orthogonal
#print axioms Reinmann.CoupledRankEnergy.energy_increment
#print axioms Reinmann.CoupledRankEnergy.pairing_increment
#print axioms Reinmann.CoupledRankEnergy.cumulative_pairing_budget
#print axioms Reinmann.CoupledRankEnergy.cumulative_galerkin_budget
#print axioms Reinmann.CoupledRankEnergy.uniform_galerkin_budget
#print axioms Reinmann.CoupledRankEnergy.absolute_rank_summability
#print axioms Reinmann.FiniteShiftChains.weighted_edge
#print axioms Reinmann.FiniteShiftChains.chain_two
#print axioms Reinmann.FiniteShiftChains.chain_three
#print axioms Reinmann.FiniteShiftChains.chain_five
#print axioms Reinmann.FiniteShiftChains.l2_energy
#print axioms Reinmann.FiniteShiftChains.integrated_chain_two
#print axioms Reinmann.FiniteShiftChains.integrated_chain_three
#print axioms Reinmann.FiniteShiftChains.integrated_chain_five

-- Strictness from explicit positive-factor extraction; analytic Xi inputs
-- are hypotheses rather than axioms. The determinant transport is proved.
#print axioms Reinmann.FinitePFStrict.rowStep_det_expansion
#print axioms Reinmann.FinitePFStrict.chosenRow_monotone
#print axioms Reinmann.FinitePFStrict.chosen_det_nonneg
#print axioms Reinmann.FinitePFStrict.orderedNonneg_rowStep
#print axioms Reinmann.FinitePFStrict.rowStep_det_lower
#print axioms Reinmann.FinitePFStrict.int_contig_rows_strict
#print axioms Reinmann.FinitePFStrict.contig_rowStep_lower
#print axioms Reinmann.FinitePFStrict.orderedNonneg_rowSteps
#print axioms Reinmann.FinitePFStrict.rowSteps_contig_lower
#print axioms Reinmann.FinitePFStrict.intToeplitz_linearFactor
#print axioms Reinmann.FinitePFStrict.intToeplitz_linearFactors
#print axioms Reinmann.FinitePFStrict.orderedNonneg_intToeplitz
#print axioms Reinmann.FinitePFStrict.intToeplitz_contig_zero
#print axioms Reinmann.FinitePFStrict.extracted_factors_contig_positive
#print axioms Reinmann.FinitePFStrict.linearFactors_contig_positive
#print axioms Reinmann.FinitePFStrict.linearFactors_contig_lower
#print axioms Reinmann.FinitePFStrict.xi_contig_positive_of_factor_extraction
#print axioms Reinmann.polynomial_derivatives_locallyUniformLimit
#print axioms Reinmann.differentiable_centeredXi
#print axioms Reinmann.differentiable_criticalXi
#print axioms Reinmann.criticalXi_real
#print axioms Reinmann.complex_deriv_eq_real_deriv
#print axioms Reinmann.complex_iteratedDeriv_eq_real_iteratedDeriv
#print axioms Reinmann.criticalXi_iteratedDeriv
#print axioms Reinmann.centeredXi_even_deriv
#print axioms Reinmann.xiMomentCoeff_eq_centeredXi_taylor
#print axioms Reinmann.centeredXi_even
#print axioms Reinmann.centeredXi_odd_deriv
#print axioms Reinmann.hasSum_centeredXi_even
#print axioms Reinmann.foldedXi_eq_tsum
#print axioms Reinmann.foldedXi_sq
#print axioms Reinmann.complex_sqrt_sq
#print axioms Reinmann.foldedXi_eq_sqrt
#print axioms Reinmann.hasSum_foldedXi
#print axioms Reinmann.foldedXiSeries_radius
#print axioms Reinmann.foldedXi_hasFPowerSeries
#print axioms Reinmann.differentiable_foldedXi
#print axioms Reinmann.foldedXi_taylor
#print axioms Reinmann.foldedXi_neg_square
#print axioms Reinmann.foldedXi_neg_square_zero_iff
#print axioms Reinmann.foldedXi_conj
#print axioms Reinmann.finitePF_xi_of_folded_locallyUniformLimit
#print axioms Reinmann.polynomial_coeff_tendsto_of_locallyUniformLimit
#print axioms Reinmann.finitePF_of_coefficientwise_limit
#print axioms Reinmann.finitePF_of_real_polynomial_locallyUniformLimit

-- Curvature controls, coupled rank energy, and the Weil omitted-mode algebra.
#print axioms Reinmann.realZeroControl_turan
#print axioms Reinmann.realZeroControl_scaled_deficit_fails
#print axioms Reinmann.realZeroControl_curvature_numerator_pos
#print axioms Reinmann.realZeroControl_discrete_numerator_pos
#print axioms Reinmann.curvature_negative_of_half_budget
#print axioms Reinmann.CoupledRankEnergy.galerkin_increment_orthogonal
#print axioms Reinmann.CoupledRankEnergy.energy_increment
#print axioms Reinmann.CoupledRankEnergy.pairing_increment
#print axioms Reinmann.CoupledRankEnergy.cumulative_pairing_budget
#print axioms Reinmann.CoupledRankEnergy.cumulative_galerkin_budget
#print axioms Reinmann.CoupledRankEnergy.uniform_galerkin_budget
#print axioms Reinmann.CoupledRankEnergy.absolute_rank_summability
#print axioms Reinmann.WeilRankTail.paired_displacement
#print axioms Reinmann.WeilRankTail.geometric_remainder
#print axioms Reinmann.WeilRankTail.geometric_remainder_abs
#print axioms Reinmann.WeilRankTail.paired_even_tail
#print axioms Reinmann.WeilRankTail.denominator_remainder
#print axioms Reinmann.WeilRankTail.weighted_moment_remainder

-- Zero-free half-planes and folded-zero angles (QuasiRHInputs, 2026-10-07)
#print axioms Reinmann.zetaZeroFreeRightOf_one
#print axioms Reinmann.zetaZeroFreeRightOf_half_iff_riemannHypothesis
#print axioms Reinmann.riemannHypothesis_iff_of_zeroFreeRightOf
#print axioms Reinmann.riemannHypothesis_iff_band_of_quasiRH
#print axioms Reinmann.abs_re_sub_half_le_of_zeroFreeRightOf
#print axioms Reinmann.angleBound_of_strip
#print axioms Reinmann.strip_numeric_43
#print axioms Reinmann.strip_numeric_58
#print axioms Reinmann.xi_finitePF43_of_classical
#print axioms Reinmann.xi_finitePF58_of_quasiRH
#print axioms Reinmann.forall_angleBound_iff_riemannHypothesis

-- Uniform actual-Xi Mellin truncation error; no zero-exclusion claim.
#print axioms Reinmann.norm_mul_norm_sub_one_le_rectangle
#print axioms Reinmann.xiMellinRemainder_norm_le_rectangle
#print axioms Reinmann.xiMellinTruncation_error_le_rectangle
#print axioms Reinmann.xiMellinTruncation_error_le_low_rectangle

-- Actual finite-product split-pair theorem; no entire-function or RH claim.
#print axioms Reinmann.SplitPairCoefficients.residue_ne_zero
#print axioms Reinmann.SplitPairCoefficients.basisDivisor_factor
#print axioms Reinmann.SplitPairCoefficients.polynomial_residue_identity
#print axioms Reinmann.SplitPairCoefficients.factor_mul_geometric
#print axioms Reinmann.SplitPairCoefficients.inverse_eq_residue_sum
#print axioms Reinmann.SplitPairCoefficients.reciprocal_coefficient
#print axioms Reinmann.SplitPairCoefficients.residue_conjugate
#print axioms Reinmann.SplitPairDeterminant.rowCoefficient_zero
#print axioms Reinmann.SplitPairDeterminant.row_expansion
#print axioms Reinmann.SplitPairDeterminant.coefficient_row_expansion
#print axioms Reinmann.SplitPairDeterminant.coefficient_eq_fiber
#print axioms Reinmann.SplitPairDeterminant.subset_expansion
#print axioms Reinmann.SplitPairDeterminant.coefficient_eq_vandermonde
#print axioms Reinmann.SplitPairDeterminant.coefficient_ne_zero
#print axioms Reinmann.SplitPairDeterminant.coefficient_conjugate
#print axioms Reinmann.SplitPairDeterminant.moment_im_eq_zero
#print axioms Reinmann.SplitPairModulusOrder.boundary_product_gap
#print axioms Reinmann.SplitPairOscillation.norm_geometric_block
#print axioms Reinmann.SplitPairOscillation.real_square
#print axioms Reinmann.SplitPairOscillation.real_sum_le
#print axioms Reinmann.SplitPairOscillation.real_square_sum_ge
#print axioms Reinmann.SplitPairOscillation.exists_negative_phase
#print axioms Reinmann.SplitPairOscillation.exists_positive_phase
#print axioms Reinmann.SplitPairOscillation.perturbed_phase_both_signs
#print axioms Reinmann.SplitPairOscillation.finite_geometric_tail_tendsto
#print axioms Reinmann.SplitPairOscillation.finite_split_sum_both_signs
#print axioms Reinmann.SplitPairOscillation.norm_finite_geometric_tail_le
#print axioms Reinmann.SplitPairOscillation.exists_geometric_rate
#print axioms Reinmann.FiniteProductSplitPair.minor_eq_rankMinor
#print axioms Reinmann.FiniteProductSplitPair.minor_eq_moment
#print axioms Reinmann.FiniteProductSplitPair.leading_ne_zero
#print axioms Reinmann.FiniteProductSplitPair.base_conjugate
#print axioms Reinmann.FiniteProductSplitPair.leading_conjugate
#print axioms Reinmann.FiniteProductSplitPair.minor_subset_expansion
#print axioms Reinmann.FiniteProductSplitPair.finite_product_split_pair
#print axioms Reinmann.FiniteProductSplitPair.exponential_remainder_bound
#print axioms Reinmann.FiniteProductSplitPair.minor_im_eq_zero
#print axioms Reinmann.FiniteProductSplitPair.finite_product_split_pair_of_boundary
#print axioms Reinmann.FiniteProductSplitPair.finite_product_split_pair_of_root_order
#print axioms Reinmann.FiniteProductSplitPair.quadratic_control_both_signs
#print axioms Reinmann.FiniteProductSplitPair.cubic_control_both_signs

-- Jacobi bridge, Cauchy coefficient tail, theta cutoff and enclosure rules.
#print axioms Reinmann.ToeplitzComplement.jacobi_block
#print axioms Reinmann.ToeplitzComplement.toeplitz_mul
#print axioms Reinmann.ToeplitzComplement.toeplitz_one
#print axioms Reinmann.ToeplitzComplement.toeplitz_inverse
#print axioms Reinmann.ToeplitzComplement.toeplitz_det
#print axioms Reinmann.ToeplitzComplement.complementary_minor
#print axioms Reinmann.ToeplitzComplement.minor_rescale_neg
#print axioms Reinmann.ToeplitzComplement.complementary_minor_signed
#print axioms Reinmann.ToeplitzComplement.finite_product_original_minor_eq
#print axioms Reinmann.ToeplitzComplement.finite_product_original_both_signs
#print axioms Reinmann.SplitPairCauchyTail.coefficient_hasSum
#print axioms Reinmann.SplitPairCauchyTail.coefficient_norm_le
#print axioms Reinmann.SplitPairCauchyTail.normalized_coefficient_norm_le
#print axioms Reinmann.SplitPairCauchyTail.normalized_coefficient_tendsto_zero
#print axioms Reinmann.SplitPairCauchyTail.finite_pole_coefficient_error
#print axioms Reinmann.theta_shifted_term_bound
#print axioms Reinmann.thetaFinite_error_bounds
#print axioms Reinmann.thetaFinite_error_le_uniform
#print axioms Reinmann.thetaFinite_weighted_error_le
#print axioms Reinmann.thetaFinite_integrated_error_le
#print axioms Reinmann.EnclosureRules.integral_tile_error
#print axioms Reinmann.EnclosureRules.integral_midpoint_error
#print axioms Reinmann.EnclosureRules.variation_of_deriv
#print axioms Reinmann.EnclosureRules.tile_nonzero
#print axioms Reinmann.EnclosureRules.unit_grid_cover
#print axioms Reinmann.EnclosureRules.rectangle_grid_cover
#print axioms Reinmann.EnclosureRules.rectangle_nonzero
#print axioms Reinmann.SplitPairCauchyTail.simple_pole_analytic_remainder

-- First actual Xi tile and standalone mixed-row / patched-remainder round.
#print axioms Reinmann.XiAdaptiveTiles.adaptive_cover_nonzero
#print axioms Reinmann.XiAdaptiveTiles.rectangle_nonzero_of_quarter
#print axioms Reinmann.XiAdaptiveTiles.xi_rectangle_nonzero_of_quarter
#print axioms Reinmann.XiLocalCauchy.mellin_norm_le
#print axioms Reinmann.XiLocalCauchy.completed_norm_le
#print axioms Reinmann.XiLocalCauchy.xi_norm_le
#print axioms Reinmann.XiLocalCauchy.unit_circle_bound
#print axioms Reinmann.XiLocalCauchy.coefficient_bound
#print axioms Reinmann.XiFirstTile.finiteIntegrand_eq
#print axioms Reinmann.XiFirstTile.finiteIntegrand_bound
#print axioms Reinmann.XiFirstTile.midpoint_sample
#print axioms Reinmann.XiFirstTile.finiteIntegrand_integrable
#print axioms Reinmann.XiFirstTile.finite_quadrature
#print axioms Reinmann.XiFirstTile.centre_enclosure
#print axioms Reinmann.XiFirstTile.local_derivative
#print axioms Reinmann.XiFirstTile.first_tile_nonzero
#print axioms Reinmann.SplitPairMixedRows.normalized_subset_product_bound
#print axioms Reinmann.SplitPairMixedRows.ordered_subset_product_bound
#print axioms Reinmann.SplitPairMixedRows.mixed_product_rate
#print axioms Reinmann.SplitPairMixedRows.row_expansion
#print axioms Reinmann.SplitPairMixedRows.repeated_pole_zero
#print axioms Reinmann.SplitPairMixedRows.det_norm_le_row_weights
#print axioms Reinmann.SplitPairMixedRows.det_geometric_rate
#print axioms Reinmann.SplitPairMixedRows.choice_weight_bound
#print axioms Reinmann.SplitPairMixedRows.determinant_difference_expansion
#print axioms Reinmann.SplitPairMixedRows.determinant_difference_rate
#print axioms Reinmann.SplitPairMixedRows.mixed_determinant_bound
#print axioms Reinmann.SplitPairMixedRows.coefficient_determinant_bound
#print axioms Reinmann.SplitPairPatchedRemainder.patch_finite_germs
#print axioms Reinmann.SplitPairPatchedRemainder.actual_simple_pole_remainder
#print axioms Reinmann.SplitPairCoefficientIdentity.principal_coefficient
#print axioms Reinmann.SplitPairCoefficientIdentity.coefficient_identity
#print axioms Reinmann.SplitPairCoefficientIdentity.actual_remainder_with_coefficients
#print axioms Reinmann.XiLocalCauchy.taylor_coefficient_bound
#print axioms Reinmann.SplitPairCoefficientIdentity.actual_reciprocal_coefficient_error

-- Analytic oscillation, actual Taylor Jacobi bridge and Gamma height bounds.
#print axioms Reinmann.AnalyticSplitPair.finite_split_sum_with_error_both_signs
#print axioms Reinmann.AnalyticSplitPair.moment_split_pair_perturbed
#print axioms Reinmann.AnalyticSplitPair.normalized_determinant_error_tendsto
#print axioms Reinmann.AnalyticSplitPair.derivative_conjugate
#print axioms Reinmann.AnalyticSplitPair.entire_split_pair
#print axioms Reinmann.AnalyticSplitPair.entire_split_pair_of_boundary
#print axioms Reinmann.AnalyticToeplitzJacobi.coefficient_mul
#print axioms Reinmann.AnalyticToeplitzJacobi.taylorSeries_mul
#print axioms Reinmann.AnalyticToeplitzJacobi.taylorSeries_reciprocal
#print axioms Reinmann.AnalyticToeplitzJacobi.reciprocalMinor_eq_original
#print axioms Reinmann.AnalyticToeplitzJacobi.entire_original_both_signs
#print axioms Reinmann.GammaHeightMajorant.gamma_norm_le_real
#print axioms Reinmann.GammaHeightMajorant.gamma_shift_norm
#print axioms Reinmann.GammaHeightMajorant.gamma_norm_le_shift_product
#print axioms Reinmann.GammaHeightMajorant.gamma_norm_le_height
#print axioms Reinmann.GammaHeightMajorant.xi_norm_le_gamma_product

-- Reflection anchors and the one-sided Beta comparison.
#print axioms Reinmann.GammaReflectionMajorant.beta_norm_le_real
#print axioms Reinmann.GammaReflectionMajorant.gamma_real_shift_ratio_bound
#print axioms Reinmann.GammaReflectionMajorant.gamma_norm_le_shifted_anchor
#print axioms Reinmann.GammaReflectionMajorant.gamma_reflection_norm_product
#print axioms Reinmann.GammaReflectionMajorant.gamma_half_norm_sq
#print axioms Reinmann.GammaReflectionMajorant.gamma_half_norm_sq_le_exp
#print axioms Reinmann.GammaReflectionMajorant.gamma_half_norm_le_sqrt_exp
#print axioms Reinmann.GammaReflectionMajorant.gamma_one_norm_sq

-- Exact finite Bernoulli quadrature and actual periodic-integral bounds.
#print axioms Reinmann.BernoulliQuadrature.kernel_hasDerivAt
#print axioms Reinmann.BernoulliQuadrature.kernel_continuous
#print axioms Reinmann.BernoulliQuadrature.kernel_zero
#print axioms Reinmann.BernoulliQuadrature.kernel_one
#print axioms Reinmann.BernoulliQuadrature.kernel_at_zero
#print axioms Reinmann.BernoulliQuadrature.kernel_at_one
#print axioms Reinmann.BernoulliQuadrature.integration_step
#print axioms Reinmann.BernoulliQuadrature.finite_quadrature
#print axioms Reinmann.BernoulliBernsteinBounds.abs_aeval_le_of_bernstein
#print axioms Reinmann.BernoulliBernsteinBounds.bernoulli_twelve_bernstein
#print axioms Reinmann.BernoulliBernsteinBounds.bernoulli_twelve_coefficients
#print axioms Reinmann.BernoulliBernsteinBounds.bernoulli_twelve_abs_le
#print axioms Reinmann.BernoulliBernsteinBounds.bernoulli_twelve_periodic_abs_le
#print axioms Reinmann.EulerMaclaurinCell.powerDerivative_hasDerivAt
#print axioms Reinmann.EulerMaclaurinCell.powerDerivative_zero
#print axioms Reinmann.EulerMaclaurinCell.finite_cell
#print axioms Reinmann.EulerMaclaurinTail.periodicTwelve_measurable
#print axioms Reinmann.EulerMaclaurinTail.periodicTwelve_abs_le
#print axioms Reinmann.EulerMaclaurinTail.integrand_norm_le
#print axioms Reinmann.EulerMaclaurinTail.integrand_integrable
#print axioms Reinmann.EulerMaclaurinTail.integral_norm_le
#print axioms Reinmann.EulerMaclaurinTail.remainder_norm_le

-- Finite summation, actual zeta identity and Mellin analytic continuation.
#print axioms Reinmann.EulerMaclaurinFinite.power_zero
#print axioms Reinmann.EulerMaclaurinFinite.signed_powerDerivative
#print axioms Reinmann.EulerMaclaurinFinite.normalized_cell
#print axioms Reinmann.EulerMaclaurinFinite.one_cell
#print axioms Reinmann.EulerMaclaurinFinite.kernel_fract
#print axioms Reinmann.EulerMaclaurinFinite.kernel_periodic_twelve
#print axioms Reinmann.EulerMaclaurinFinite.cellTail_eq
#print axioms Reinmann.EulerMaclaurinFinite.power_intervalIntegrable
#print axioms Reinmann.EulerMaclaurinFinite.tail_intervalIntegrable
#print axioms Reinmann.EulerMaclaurinFinite.finite_sum
#print axioms Reinmann.EulerMaclaurinZeta.cpow_tendsto_zero
#print axioms Reinmann.EulerMaclaurinZeta.power_tendsto_zero
#print axioms Reinmann.EulerMaclaurinZeta.correction_tendsto_zero
#print axioms Reinmann.EulerMaclaurinZeta.hasSum_power
#print axioms Reinmann.EulerMaclaurinZeta.integral_power
#print axioms Reinmann.EulerMaclaurinZeta.zeta_eq_model_add_remainder
#print axioms Reinmann.EulerMaclaurinZeta.zeta_error_le
#print axioms Reinmann.EulerMaclaurinAnalytic.cutoff_locallyIntegrable
#print axioms Reinmann.EulerMaclaurinAnalytic.cutoff_top
#print axioms Reinmann.EulerMaclaurinAnalytic.cutoff_zero
#print axioms Reinmann.EulerMaclaurinAnalytic.integral_eq_mellin
#print axioms Reinmann.EulerMaclaurinAnalytic.integral_differentiableAt
#print axioms Reinmann.EulerMaclaurinAnalytic.power_differentiableAt
#print axioms Reinmann.EulerMaclaurinAnalytic.correction_differentiableAt
#print axioms Reinmann.EulerMaclaurinAnalytic.model_differentiableAt
#print axioms Reinmann.EulerMaclaurinAnalytic.remainder_differentiableAt
#print axioms Reinmann.EulerMaclaurinAnalytic.zeta_eq_model_add_remainder_upper
#print axioms Reinmann.EulerMaclaurinAnalytic.zeta_error_le_upper
#print axioms Reinmann.EulerMaclaurinAnalytic.hard_disk_domain
#print axioms Reinmann.EulerMaclaurinAnalytic.hard_disk_identity
#print axioms Reinmann.EulerMaclaurinAnalytic.hard_disk_error_le

-- Complex Stirling formula with explicit order-12 remainder.
#print axioms Reinmann.StirlingCell.add_ne_zero_of_re_pos
#print axioms Reinmann.StirlingCell.logChain_hasDerivAt
#print axioms Reinmann.StirlingCell.log_cell
#print axioms Reinmann.StirlingSum.one_cell
#print axioms Reinmann.StirlingSum.cellTail_eq
#print axioms Reinmann.StirlingSum.logChain_zero_continuousOn
#print axioms Reinmann.StirlingSum.logChain_zero_intervalIntegrable
#print axioms Reinmann.StirlingSum.tailIntegrand_norm_le
#print axioms Reinmann.StirlingSum.tailIntegrand_measurable
#print axioms Reinmann.StirlingSum.majorant_integral
#print axioms Reinmann.StirlingSum.tailIntegrand_integrableOn
#print axioms Reinmann.StirlingSum.tail_norm_le
#print axioms Reinmann.StirlingSum.tailIntegrand_intervalIntegrable
#print axioms Reinmann.StirlingSum.finite_sum
#print axioms Reinmann.StirlingGamma.GammaSeq_eq_exp
#print axioms Reinmann.StirlingGamma.integral_logChain
#print axioms Reinmann.StirlingGamma.seqLog_formula
#print axioms Reinmann.StirlingGamma.tendsto_log_stirling
#print axioms Reinmann.StirlingGamma.tendsto_div_nat
#print axioms Reinmann.StirlingGamma.tendsto_log_one_add
#print axioms Reinmann.StirlingGamma.tendsto_nat_mul_log_one_add
#print axioms Reinmann.StirlingGamma.tendsto_inv_add_nat
#print axioms Reinmann.StirlingGamma.tendsto_corr
#print axioms Reinmann.StirlingGamma.tendsto_seqLog
#print axioms Reinmann.StirlingGamma.Gamma_eq
#print axioms Reinmann.StirlingGamma.Gamma_eq_exp_main_add
#print axioms Reinmann.StirlingGamma.kernel_zero_eq
#print axioms Reinmann.StirlingGamma.corr_zero_eq
#print axioms Reinmann.StirlingGamma.Gamma_add_nat
#print axioms Reinmann.StirlingGamma.Gamma_eq_shift

-- Holomorphic Stirling remainder and rational Gamma/zeta jet error bounds.
#print axioms Reinmann.StirlingAnalytic.tailIntegrand_eq
#print axioms Reinmann.StirlingAnalytic.integrand_hasDerivAt
#print axioms Reinmann.StirlingAnalytic.derivIntegrand_measurable
#print axioms Reinmann.StirlingAnalytic.derivIntegrand_norm_le
#print axioms Reinmann.StirlingAnalytic.tail_hasDerivAt
#print axioms Reinmann.StirlingAnalytic.tail_differentiableAt
#print axioms Reinmann.StirlingAnalytic.hard_disk_shift_re
#print axioms Reinmann.StirlingAnalytic.hard_disk_tail_norm_le
#print axioms Reinmann.StirlingAnalytic.shiftedTail_differentiableAt
#print axioms Reinmann.StirlingAnalytic.shiftedTail_diffContOnCl
#print axioms Reinmann.StirlingAnalytic.shiftedTail_coefficient_le
#print axioms Reinmann.StirlingAnalytic.relativeError_norm_le
#print axioms Reinmann.StirlingAnalytic.hard_disk_factors_ne
#print axioms Reinmann.StirlingAnalytic.gamma_identity
#print axioms Reinmann.StirlingAnalytic.gammaApprox_eq
#print axioms Reinmann.StirlingAnalytic.gamma_norm_le_one
#print axioms Reinmann.StirlingAnalytic.gammaApprox_norm_le_two
#print axioms Reinmann.StirlingAnalytic.gammaError_norm_le
#print axioms Reinmann.StirlingAnalytic.corr_zero_differentiableAt
#print axioms Reinmann.StirlingAnalytic.mainTerm_differentiableAt
#print axioms Reinmann.StirlingAnalytic.gammaApprox_differentiableAt
#print axioms Reinmann.StirlingAnalytic.gamma_factor_differentiableAt
#print axioms Reinmann.StirlingAnalytic.gammaError_diffContOnCl
#print axioms Reinmann.StirlingAnalytic.gammaError_coefficient_le
#print axioms Reinmann.StirlingAnalytic.gamma_coefficient_error_le
#print axioms Reinmann.ZetaJetRemainder.hard_disk_norm_le
#print axioms Reinmann.ZetaJetRemainder.rising_norm_le
#print axioms Reinmann.ZetaJetRemainder.hard_disk_re_lower
#print axioms Reinmann.ZetaJetRemainder.remainder_norm_le
#print axioms Reinmann.ZetaJetRemainder.zetaError_norm_le
#print axioms Reinmann.ZetaJetRemainder.hard_disk_ne_one
#print axioms Reinmann.ZetaJetRemainder.zetaError_differentiableAt
#print axioms Reinmann.ZetaJetRemainder.zetaError_diffContOnCl
#print axioms Reinmann.ZetaJetRemainder.zetaError_coefficient_le
#print axioms Reinmann.ZetaJetRemainder.zeta_coefficient_error_le

-- Rational Taylor arithmetic, scalar inputs, and the actual shifted Log jet.
#print axioms Reinmann.CertifiedTaylorModel.size_nonneg
#print axioms Reinmann.CertifiedTaylorModel.norm_value_le
#print axioms Reinmann.CertifiedTaylorModel.contains_exact
#print axioms Reinmann.CertifiedTaylorModel.contains_zero
#print axioms Reinmann.CertifiedTaylorModel.contains_add
#print axioms Reinmann.CertifiedTaylorModel.contains_mul
#print axioms Reinmann.CertifiedTaylorModel.contains_round
#print axioms Reinmann.CertifiedTaylorModel.contains_sum
#print axioms Reinmann.CertifiedTaylorModel.coefficient_add
#print axioms Reinmann.CertifiedTaylorModel.coefficient_mul
#print axioms Reinmann.CertifiedTaylorModel.coefficient_scale
#print axioms Reinmann.CertifiedTaylorModel.sound_add
#print axioms Reinmann.CertifiedTaylorModel.sound_mul
#print axioms Reinmann.CertifiedTaylorModel.sound_scale
#print axioms Reinmann.CertifiedTaylorModel.sound_round
#print axioms Reinmann.CertifiedTaylorModel.contains_inflate
#print axioms Reinmann.CertifiedTaylorModel.sound_perturb
#print axioms Reinmann.CertifiedTaylorModel.norm_le_of_contains
#print axioms Reinmann.CertifiedTaylorModel.centre_contains
#print axioms Reinmann.CertifiedComplexInputs.log_partial_bound
#print axioms Reinmann.CertifiedComplexInputs.log_enclosure
#print axioms Reinmann.CertifiedComplexInputs.log_mul_enclosure
#print axioms Reinmann.CertifiedComplexInputs.log_pow_enclosure
#print axioms Reinmann.CertifiedComplexInputs.log_recenter
#print axioms Reinmann.CertifiedComplexInputs.log_scaled_enclosure
#print axioms Reinmann.CertifiedComplexInputs.exponential_coefficient
#print axioms Reinmann.CertifiedComplexInputs.exp_series_error
#print axioms Reinmann.CertifiedComplexInputs.exp_series_contains
#print axioms Reinmann.CertifiedComplexInputs.log_series_error
#print axioms Reinmann.CertifiedComplexInputs.log_series_contains
#print axioms Reinmann.CertifiedComplexInputs.exp_phase_reduce
#print axioms Reinmann.CertifiedComplexInputs.gamma_log_centre_reduce
#print axioms Reinmann.CertifiedComplexInputs.gamma_log_centre_norm
#print axioms Reinmann.CertifiedTaylorComposition.coefficient_deriv
#print axioms Reinmann.CertifiedTaylorComposition.coefficient_exp_succ
#print axioms Reinmann.CertifiedTaylorComposition.coefficient_log_succ
#print axioms Reinmann.CertifiedTaylorComposition.coefficient_inv_succ
#print axioms Reinmann.CertifiedTaylorComposition.exp_coefficients_sound
#print axioms Reinmann.CertifiedTaylorComposition.inv_coefficients_sound
#print axioms Reinmann.CertifiedTaylorComposition.log_coefficients_sound
#print axioms Reinmann.CertifiedHorner.horner_eq_sum
#print axioms Reinmann.CertifiedHorner.horner_contains
#print axioms Reinmann.CertifiedHorner.exp_horner_eq
#print axioms Reinmann.CertifiedHorner.log_horner_eq
#print axioms Reinmann.HardTileGammaLog.log_polynomial
#print axioms Reinmann.HardTileGammaLog.log_two_contains
#print axioms Reinmann.HardTileGammaLog.gamma_log_contains
#print axioms Reinmann.HardTileGammaLog.gamma_log_radius
#print axioms Reinmann.HardTileGammaLogJet.shifted_analytic
#print axioms Reinmann.HardTileGammaLogJet.shifted_value
#print axioms Reinmann.HardTileGammaLogJet.shifted_nonzero
#print axioms Reinmann.HardTileGammaLogJet.shifted_slit
#print axioms Reinmann.HardTileGammaLogJet.shifted_coefficient
#print axioms Reinmann.HardTileGammaLogJet.affine_sound
#print axioms Reinmann.HardTileGammaLogJet.inverse_sound
#print axioms Reinmann.HardTileGammaLogJet.log_sound
#print axioms Reinmann.HardTileGammaLogJet.log_radius

-- Positive-real scalar logarithms, including every prime up to 19 and log pi.
#print axioms Reinmann.HardTileLogInputs.log_2
#print axioms Reinmann.HardTileLogInputs.log_3
#print axioms Reinmann.HardTileLogInputs.log_4
#print axioms Reinmann.HardTileLogInputs.log_5
#print axioms Reinmann.HardTileLogInputs.log_6
#print axioms Reinmann.HardTileLogInputs.log_7
#print axioms Reinmann.HardTileLogInputs.log_8
#print axioms Reinmann.HardTileLogInputs.log_9
#print axioms Reinmann.HardTileLogInputs.log_10
#print axioms Reinmann.HardTileLogInputs.log_11
#print axioms Reinmann.HardTileLogInputs.log_12
#print axioms Reinmann.HardTileLogInputs.log_13
#print axioms Reinmann.HardTileLogInputs.log_14
#print axioms Reinmann.HardTileLogInputs.log_15
#print axioms Reinmann.HardTileLogInputs.log_16
#print axioms Reinmann.HardTileLogInputs.log_17
#print axioms Reinmann.HardTileLogInputs.log_18
#print axioms Reinmann.HardTileLogInputs.log_19
#print axioms Reinmann.HardTileLogInputs.log_20
#print axioms Reinmann.HardTileLogInputs.log_21
#print axioms Reinmann.HardTileLogInputs.log_pi

-- Complete degree-eight Gamma/zeta/Xi hard-tile jet and nonvanishing certificate.
#print axioms Reinmann.CertifiedScalarExp.disk_ext
#print axioms Reinmann.CertifiedScalarExp.contains_real
#print axioms Reinmann.CertifiedScalarExp.pi_contains
#print axioms Reinmann.CertifiedScalarExp.sound
#print axioms Reinmann.CertifiedTaylorInputs.constant_sound
#print axioms Reinmann.CertifiedTaylorInputs.variable_sound
#print axioms Reinmann.CertifiedTaylorInputs.value_eq_of_exact
#print axioms Reinmann.CertifiedTaylorInputs.sound_congr
#print axioms Reinmann.CertifiedTaylorInputs.exp_sound
#print axioms Reinmann.HardTilePowerInputs.power2_checks
#print axioms Reinmann.HardTilePowerInputs.power2_value
#print axioms Reinmann.HardTilePowerInputs.power3_checks
#print axioms Reinmann.HardTilePowerInputs.power3_value
#print axioms Reinmann.HardTilePowerInputs.power4_checks
#print axioms Reinmann.HardTilePowerInputs.power4_value
#print axioms Reinmann.HardTilePowerInputs.power5_checks
#print axioms Reinmann.HardTilePowerInputs.power5_value
#print axioms Reinmann.HardTilePowerInputs.power6_checks
#print axioms Reinmann.HardTilePowerInputs.power6_value
#print axioms Reinmann.HardTilePowerInputs.power7_checks
#print axioms Reinmann.HardTilePowerInputs.power7_value
#print axioms Reinmann.HardTilePowerInputs.power8_checks
#print axioms Reinmann.HardTilePowerInputs.power8_value
#print axioms Reinmann.HardTilePowerInputs.power9_checks
#print axioms Reinmann.HardTilePowerInputs.power9_value
#print axioms Reinmann.HardTilePowerInputs.power10_checks
#print axioms Reinmann.HardTilePowerInputs.power10_value
#print axioms Reinmann.HardTilePowerInputs.power11_checks
#print axioms Reinmann.HardTilePowerInputs.power11_value
#print axioms Reinmann.HardTilePowerInputs.power12_checks
#print axioms Reinmann.HardTilePowerInputs.power12_value
#print axioms Reinmann.HardTilePowerInputs.power13_checks
#print axioms Reinmann.HardTilePowerInputs.power13_value
#print axioms Reinmann.HardTilePowerInputs.power14_checks
#print axioms Reinmann.HardTilePowerInputs.power14_value
#print axioms Reinmann.HardTilePowerInputs.power15_checks
#print axioms Reinmann.HardTilePowerInputs.power15_value
#print axioms Reinmann.HardTilePowerInputs.power16_checks
#print axioms Reinmann.HardTilePowerInputs.power16_value
#print axioms Reinmann.HardTilePowerInputs.power17_checks
#print axioms Reinmann.HardTilePowerInputs.power17_value
#print axioms Reinmann.HardTilePowerInputs.power18_checks
#print axioms Reinmann.HardTilePowerInputs.power18_value
#print axioms Reinmann.HardTilePowerInputs.power19_checks
#print axioms Reinmann.HardTilePowerInputs.power19_value
#print axioms Reinmann.HardTilePowerInputs.power20_checks
#print axioms Reinmann.HardTilePowerInputs.power20_value
#print axioms Reinmann.HardTilePowerInputs.power21_checks
#print axioms Reinmann.HardTilePowerInputs.power21_value
#print axioms Reinmann.HardTileFiniteIdentities.negative_powers
#print axioms Reinmann.HardTileFiniteIdentities.stirlingMain_eq
#print axioms Reinmann.HardTileFiniteIdentities.cpow_neg_eq
#print axioms Reinmann.HardTileFiniteIdentities.cpow_neg_sub
#print axioms Reinmann.HardTileFiniteIdentities.rising_eq
#print axioms Reinmann.HardTileFiniteIdentities.dirichletTerm_one
#print axioms Reinmann.HardTileFiniteIdentities.cpow_one_sub
#print axioms Reinmann.HardTileFiniteIdentities.power_eq
#print axioms Reinmann.HardTileFiniteIdentities.correction_eq
#print axioms Reinmann.HardTileFiniteIdentities.emFinite_eq
#print axioms Reinmann.HardTileFiniteJets.A_variable
#print axioms Reinmann.HardTileFiniteJets.S_variable
#print axioms Reinmann.HardTileFiniteJets.A_log2
#print axioms Reinmann.HardTileFiniteJets.S_log2
#print axioms Reinmann.HardTileFiniteJets.A_logpi
#print axioms Reinmann.HardTileFiniteJets.S_logpi
#print axioms Reinmann.HardTileFiniteJets.A_shift
#print axioms Reinmann.HardTileFiniteJets.S_shift
#print axioms Reinmann.HardTileFiniteJets.A_shiftinv
#print axioms Reinmann.HardTileFiniteJets.S_shiftinv
#print axioms Reinmann.HardTileFiniteJets.A_shiftlog
#print axioms Reinmann.HardTileFiniteJets.S_shiftlog
#print axioms Reinmann.HardTileFiniteJets.A_q0
#print axioms Reinmann.HardTileFiniteJets.S_q0
#print axioms Reinmann.HardTileFiniteJets.A_wmhalf
#print axioms Reinmann.HardTileFiniteJets.S_wmhalf
#print axioms Reinmann.HardTileFiniteJets.A_wlog
#print axioms Reinmann.HardTileFiniteJets.S_wlog
#print axioms Reinmann.HardTileFiniteJets.A_negw
#print axioms Reinmann.HardTileFiniteJets.S_negw
#print axioms Reinmann.HardTileFiniteJets.A_mainbase
#print axioms Reinmann.HardTileFiniteJets.S_mainbase
#print axioms Reinmann.HardTileFiniteJets.A_log2pi
#print axioms Reinmann.HardTileFiniteJets.S_log2pi
#print axioms Reinmann.HardTileFiniteJets.A_halfLog2pi
#print axioms Reinmann.HardTileFiniteJets.S_halfLog2pi
#print axioms Reinmann.HardTileFiniteJets.A_mainconstant
#print axioms Reinmann.HardTileFiniteJets.S_mainconstant
#print axioms Reinmann.HardTileFiniteJets.A_iw2
#print axioms Reinmann.HardTileFiniteJets.S_iw2
#print axioms Reinmann.HardTileFiniteJets.A_iw3
#print axioms Reinmann.HardTileFiniteJets.S_iw3
#print axioms Reinmann.HardTileFiniteJets.A_iw4
#print axioms Reinmann.HardTileFiniteJets.S_iw4
#print axioms Reinmann.HardTileFiniteJets.A_iw5
#print axioms Reinmann.HardTileFiniteJets.S_iw5
#print axioms Reinmann.HardTileFiniteJets.A_iw6
#print axioms Reinmann.HardTileFiniteJets.S_iw6
#print axioms Reinmann.HardTileFiniteJets.A_iw7
#print axioms Reinmann.HardTileFiniteJets.S_iw7
#print axioms Reinmann.HardTileFiniteJets.A_iw8
#print axioms Reinmann.HardTileFiniteJets.S_iw8
#print axioms Reinmann.HardTileFiniteJets.A_iw9
#print axioms Reinmann.HardTileFiniteJets.S_iw9
#print axioms Reinmann.HardTileFiniteJets.A_iw10
#print axioms Reinmann.HardTileFiniteJets.S_iw10
#print axioms Reinmann.HardTileFiniteJets.A_iw11
#print axioms Reinmann.HardTileFiniteJets.S_iw11
#print axioms Reinmann.HardTileFiniteJets.A_gcorr1
#print axioms Reinmann.HardTileFiniteJets.S_gcorr1
#print axioms Reinmann.HardTileFiniteJets.A_maincorr1
#print axioms Reinmann.HardTileFiniteJets.S_maincorr1
#print axioms Reinmann.HardTileFiniteJets.A_gcorr2
#print axioms Reinmann.HardTileFiniteJets.S_gcorr2
#print axioms Reinmann.HardTileFiniteJets.A_maincorr2
#print axioms Reinmann.HardTileFiniteJets.S_maincorr2
#print axioms Reinmann.HardTileFiniteJets.A_gcorr3
#print axioms Reinmann.HardTileFiniteJets.S_gcorr3
#print axioms Reinmann.HardTileFiniteJets.A_maincorr3
#print axioms Reinmann.HardTileFiniteJets.S_maincorr3
#print axioms Reinmann.HardTileFiniteJets.A_gcorr4
#print axioms Reinmann.HardTileFiniteJets.S_gcorr4
#print axioms Reinmann.HardTileFiniteJets.A_maincorr4
#print axioms Reinmann.HardTileFiniteJets.S_maincorr4
#print axioms Reinmann.HardTileFiniteJets.A_gcorr5
#print axioms Reinmann.HardTileFiniteJets.S_gcorr5
#print axioms Reinmann.HardTileFiniteJets.A_maincorr5
#print axioms Reinmann.HardTileFiniteJets.S_maincorr5
#print axioms Reinmann.HardTileFiniteJets.A_gcorr6
#print axioms Reinmann.HardTileFiniteJets.S_gcorr6
#print axioms Reinmann.HardTileFiniteJets.A_maincorr6
#print axioms Reinmann.HardTileFiniteJets.S_maincorr6
#print axioms Reinmann.HardTileFiniteJets.expGammaMainValue_checks
#print axioms Reinmann.HardTileFiniteJets.A_expGammaMain
#print axioms Reinmann.HardTileFiniteJets.S_expGammaMain
#print axioms Reinmann.HardTileFiniteJets.A_halfVariable
#print axioms Reinmann.HardTileFiniteJets.S_halfVariable
#print axioms Reinmann.HardTileFiniteJets.V_gammaInv0
#print axioms Reinmann.HardTileFiniteJets.N_gammaInv0
#print axioms Reinmann.HardTileFiniteJets.A_gammaInv0
#print axioms Reinmann.HardTileFiniteJets.S_gammaInv0
#print axioms Reinmann.HardTileFiniteJets.A_q1
#print axioms Reinmann.HardTileFiniteJets.S_q1
#print axioms Reinmann.HardTileFiniteJets.A_shift1
#print axioms Reinmann.HardTileFiniteJets.S_shift1
#print axioms Reinmann.HardTileFiniteJets.V_gammaInv1
#print axioms Reinmann.HardTileFiniteJets.N_gammaInv1
#print axioms Reinmann.HardTileFiniteJets.A_gammaInv1
#print axioms Reinmann.HardTileFiniteJets.S_gammaInv1
#print axioms Reinmann.HardTileFiniteJets.A_gammaInvProd1
#print axioms Reinmann.HardTileFiniteJets.S_gammaInvProd1
#print axioms Reinmann.HardTileFiniteJets.A_q2
#print axioms Reinmann.HardTileFiniteJets.S_q2
#print axioms Reinmann.HardTileFiniteJets.A_shift2
#print axioms Reinmann.HardTileFiniteJets.S_shift2
#print axioms Reinmann.HardTileFiniteJets.V_gammaInv2
#print axioms Reinmann.HardTileFiniteJets.N_gammaInv2
#print axioms Reinmann.HardTileFiniteJets.A_gammaInv2
#print axioms Reinmann.HardTileFiniteJets.S_gammaInv2
#print axioms Reinmann.HardTileFiniteJets.A_gammaInvProd2
#print axioms Reinmann.HardTileFiniteJets.S_gammaInvProd2
#print axioms Reinmann.HardTileFiniteJets.A_q3
#print axioms Reinmann.HardTileFiniteJets.S_q3
#print axioms Reinmann.HardTileFiniteJets.A_shift3
#print axioms Reinmann.HardTileFiniteJets.S_shift3
#print axioms Reinmann.HardTileFiniteJets.V_gammaInv3
#print axioms Reinmann.HardTileFiniteJets.N_gammaInv3
#print axioms Reinmann.HardTileFiniteJets.A_gammaInv3
#print axioms Reinmann.HardTileFiniteJets.S_gammaInv3
#print axioms Reinmann.HardTileFiniteJets.A_gammaInvProd3
#print axioms Reinmann.HardTileFiniteJets.S_gammaInvProd3
#print axioms Reinmann.HardTileFiniteJets.A_q4
#print axioms Reinmann.HardTileFiniteJets.S_q4
#print axioms Reinmann.HardTileFiniteJets.A_shift4
#print axioms Reinmann.HardTileFiniteJets.S_shift4
#print axioms Reinmann.HardTileFiniteJets.V_gammaInv4
#print axioms Reinmann.HardTileFiniteJets.N_gammaInv4
#print axioms Reinmann.HardTileFiniteJets.A_gammaInv4
#print axioms Reinmann.HardTileFiniteJets.S_gammaInv4
#print axioms Reinmann.HardTileFiniteJets.A_gammaInvProd4
#print axioms Reinmann.HardTileFiniteJets.S_gammaInvProd4
#print axioms Reinmann.HardTileFiniteJets.A_q5
#print axioms Reinmann.HardTileFiniteJets.S_q5
#print axioms Reinmann.HardTileFiniteJets.A_shift5
#print axioms Reinmann.HardTileFiniteJets.S_shift5
#print axioms Reinmann.HardTileFiniteJets.V_gammaInv5
#print axioms Reinmann.HardTileFiniteJets.N_gammaInv5
#print axioms Reinmann.HardTileFiniteJets.A_gammaInv5
#print axioms Reinmann.HardTileFiniteJets.S_gammaInv5
#print axioms Reinmann.HardTileFiniteJets.A_gammaInvProd5
#print axioms Reinmann.HardTileFiniteJets.S_gammaInvProd5
#print axioms Reinmann.HardTileFiniteJets.A_q6
#print axioms Reinmann.HardTileFiniteJets.S_q6
#print axioms Reinmann.HardTileFiniteJets.A_shift6
#print axioms Reinmann.HardTileFiniteJets.S_shift6
#print axioms Reinmann.HardTileFiniteJets.V_gammaInv6
#print axioms Reinmann.HardTileFiniteJets.N_gammaInv6
#print axioms Reinmann.HardTileFiniteJets.A_gammaInv6
#print axioms Reinmann.HardTileFiniteJets.S_gammaInv6
#print axioms Reinmann.HardTileFiniteJets.A_gammaInvProd6
#print axioms Reinmann.HardTileFiniteJets.S_gammaInvProd6
#print axioms Reinmann.HardTileFiniteJets.A_q7
#print axioms Reinmann.HardTileFiniteJets.S_q7
#print axioms Reinmann.HardTileFiniteJets.A_shift7
#print axioms Reinmann.HardTileFiniteJets.S_shift7
#print axioms Reinmann.HardTileFiniteJets.V_gammaInv7
#print axioms Reinmann.HardTileFiniteJets.N_gammaInv7
#print axioms Reinmann.HardTileFiniteJets.A_gammaInv7
#print axioms Reinmann.HardTileFiniteJets.S_gammaInv7
#print axioms Reinmann.HardTileFiniteJets.A_gammaInvProd7
#print axioms Reinmann.HardTileFiniteJets.S_gammaInvProd7
#print axioms Reinmann.HardTileFiniteJets.A_q8
#print axioms Reinmann.HardTileFiniteJets.S_q8
#print axioms Reinmann.HardTileFiniteJets.A_shift8
#print axioms Reinmann.HardTileFiniteJets.S_shift8
#print axioms Reinmann.HardTileFiniteJets.V_gammaInv8
#print axioms Reinmann.HardTileFiniteJets.N_gammaInv8
#print axioms Reinmann.HardTileFiniteJets.A_gammaInv8
#print axioms Reinmann.HardTileFiniteJets.S_gammaInv8
#print axioms Reinmann.HardTileFiniteJets.A_gammaInvProd8
#print axioms Reinmann.HardTileFiniteJets.S_gammaInvProd8
#print axioms Reinmann.HardTileFiniteJets.A_q9
#print axioms Reinmann.HardTileFiniteJets.S_q9
#print axioms Reinmann.HardTileFiniteJets.A_shift9
#print axioms Reinmann.HardTileFiniteJets.S_shift9
#print axioms Reinmann.HardTileFiniteJets.V_gammaInv9
#print axioms Reinmann.HardTileFiniteJets.N_gammaInv9
#print axioms Reinmann.HardTileFiniteJets.A_gammaInv9
#print axioms Reinmann.HardTileFiniteJets.S_gammaInv9
#print axioms Reinmann.HardTileFiniteJets.A_gammaInvProd9
#print axioms Reinmann.HardTileFiniteJets.S_gammaInvProd9
#print axioms Reinmann.HardTileFiniteJets.A_q10
#print axioms Reinmann.HardTileFiniteJets.S_q10
#print axioms Reinmann.HardTileFiniteJets.A_shift10
#print axioms Reinmann.HardTileFiniteJets.S_shift10
#print axioms Reinmann.HardTileFiniteJets.V_gammaInv10
#print axioms Reinmann.HardTileFiniteJets.N_gammaInv10
#print axioms Reinmann.HardTileFiniteJets.A_gammaInv10
#print axioms Reinmann.HardTileFiniteJets.S_gammaInv10
#print axioms Reinmann.HardTileFiniteJets.A_gammaInvProd10
#print axioms Reinmann.HardTileFiniteJets.S_gammaInvProd10
#print axioms Reinmann.HardTileFiniteJets.A_q11
#print axioms Reinmann.HardTileFiniteJets.S_q11
#print axioms Reinmann.HardTileFiniteJets.A_shift11
#print axioms Reinmann.HardTileFiniteJets.S_shift11
#print axioms Reinmann.HardTileFiniteJets.V_gammaInv11
#print axioms Reinmann.HardTileFiniteJets.N_gammaInv11
#print axioms Reinmann.HardTileFiniteJets.A_gammaInv11
#print axioms Reinmann.HardTileFiniteJets.S_gammaInv11
#print axioms Reinmann.HardTileFiniteJets.A_gammaInvProd11
#print axioms Reinmann.HardTileFiniteJets.S_gammaInvProd11
#print axioms Reinmann.HardTileFiniteJets.A_gammaFinite
#print axioms Reinmann.HardTileFiniteJets.S_gammaFinite
#print axioms Reinmann.HardTileFiniteJets.A_negLog2
#print axioms Reinmann.HardTileFiniteJets.S_negLog2
#print axioms Reinmann.HardTileFiniteJets.A_arg2
#print axioms Reinmann.HardTileFiniteJets.S_arg2
#print axioms Reinmann.HardTileFiniteJets.term2Value_checks
#print axioms Reinmann.HardTileFiniteJets.A_term2
#print axioms Reinmann.HardTileFiniteJets.S_term2
#print axioms Reinmann.HardTileFiniteJets.A_log3
#print axioms Reinmann.HardTileFiniteJets.S_log3
#print axioms Reinmann.HardTileFiniteJets.A_negLog3
#print axioms Reinmann.HardTileFiniteJets.S_negLog3
#print axioms Reinmann.HardTileFiniteJets.A_arg3
#print axioms Reinmann.HardTileFiniteJets.S_arg3
#print axioms Reinmann.HardTileFiniteJets.term3Value_checks
#print axioms Reinmann.HardTileFiniteJets.A_term3
#print axioms Reinmann.HardTileFiniteJets.S_term3
#print axioms Reinmann.HardTileFiniteJets.A_log4
#print axioms Reinmann.HardTileFiniteJets.S_log4
#print axioms Reinmann.HardTileFiniteJets.A_negLog4
#print axioms Reinmann.HardTileFiniteJets.S_negLog4
#print axioms Reinmann.HardTileFiniteJets.A_arg4
#print axioms Reinmann.HardTileFiniteJets.S_arg4
#print axioms Reinmann.HardTileFiniteJets.term4Value_checks
#print axioms Reinmann.HardTileFiniteJets.A_term4
#print axioms Reinmann.HardTileFiniteJets.S_term4
#print axioms Reinmann.HardTileFiniteJets.A_log5
#print axioms Reinmann.HardTileFiniteJets.S_log5
#print axioms Reinmann.HardTileFiniteJets.A_negLog5
#print axioms Reinmann.HardTileFiniteJets.S_negLog5
#print axioms Reinmann.HardTileFiniteJets.A_arg5
#print axioms Reinmann.HardTileFiniteJets.S_arg5
#print axioms Reinmann.HardTileFiniteJets.term5Value_checks
#print axioms Reinmann.HardTileFiniteJets.A_term5
#print axioms Reinmann.HardTileFiniteJets.S_term5
#print axioms Reinmann.HardTileFiniteJets.A_log6
#print axioms Reinmann.HardTileFiniteJets.S_log6
#print axioms Reinmann.HardTileFiniteJets.A_negLog6
#print axioms Reinmann.HardTileFiniteJets.S_negLog6
#print axioms Reinmann.HardTileFiniteJets.A_arg6
#print axioms Reinmann.HardTileFiniteJets.S_arg6
#print axioms Reinmann.HardTileFiniteJets.term6Value_checks
#print axioms Reinmann.HardTileFiniteJets.A_term6
#print axioms Reinmann.HardTileFiniteJets.S_term6
#print axioms Reinmann.HardTileFiniteJets.A_log7
#print axioms Reinmann.HardTileFiniteJets.S_log7
#print axioms Reinmann.HardTileFiniteJets.A_negLog7
#print axioms Reinmann.HardTileFiniteJets.S_negLog7
#print axioms Reinmann.HardTileFiniteJets.A_arg7
#print axioms Reinmann.HardTileFiniteJets.S_arg7
#print axioms Reinmann.HardTileFiniteJets.term7Value_checks
#print axioms Reinmann.HardTileFiniteJets.A_term7
#print axioms Reinmann.HardTileFiniteJets.S_term7
#print axioms Reinmann.HardTileFiniteJets.A_log8
#print axioms Reinmann.HardTileFiniteJets.S_log8
#print axioms Reinmann.HardTileFiniteJets.A_negLog8
#print axioms Reinmann.HardTileFiniteJets.S_negLog8
#print axioms Reinmann.HardTileFiniteJets.A_arg8
#print axioms Reinmann.HardTileFiniteJets.S_arg8
#print axioms Reinmann.HardTileFiniteJets.term8Value_checks
#print axioms Reinmann.HardTileFiniteJets.A_term8
#print axioms Reinmann.HardTileFiniteJets.S_term8
#print axioms Reinmann.HardTileFiniteJets.A_log9
#print axioms Reinmann.HardTileFiniteJets.S_log9
#print axioms Reinmann.HardTileFiniteJets.A_negLog9
#print axioms Reinmann.HardTileFiniteJets.S_negLog9
#print axioms Reinmann.HardTileFiniteJets.A_arg9
#print axioms Reinmann.HardTileFiniteJets.S_arg9
#print axioms Reinmann.HardTileFiniteJets.term9Value_checks
#print axioms Reinmann.HardTileFiniteJets.A_term9
#print axioms Reinmann.HardTileFiniteJets.S_term9
#print axioms Reinmann.HardTileFiniteJets.A_log10
#print axioms Reinmann.HardTileFiniteJets.S_log10
#print axioms Reinmann.HardTileFiniteJets.A_negLog10
#print axioms Reinmann.HardTileFiniteJets.S_negLog10
#print axioms Reinmann.HardTileFiniteJets.A_arg10
#print axioms Reinmann.HardTileFiniteJets.S_arg10
#print axioms Reinmann.HardTileFiniteJets.term10Value_checks
#print axioms Reinmann.HardTileFiniteJets.A_term10
#print axioms Reinmann.HardTileFiniteJets.S_term10
#print axioms Reinmann.HardTileFiniteJets.A_log11
#print axioms Reinmann.HardTileFiniteJets.S_log11
#print axioms Reinmann.HardTileFiniteJets.A_negLog11
#print axioms Reinmann.HardTileFiniteJets.S_negLog11
#print axioms Reinmann.HardTileFiniteJets.A_arg11
#print axioms Reinmann.HardTileFiniteJets.S_arg11
#print axioms Reinmann.HardTileFiniteJets.term11Value_checks
#print axioms Reinmann.HardTileFiniteJets.A_term11
#print axioms Reinmann.HardTileFiniteJets.S_term11
#print axioms Reinmann.HardTileFiniteJets.A_log12
#print axioms Reinmann.HardTileFiniteJets.S_log12
#print axioms Reinmann.HardTileFiniteJets.A_negLog12
#print axioms Reinmann.HardTileFiniteJets.S_negLog12
#print axioms Reinmann.HardTileFiniteJets.A_arg12
#print axioms Reinmann.HardTileFiniteJets.S_arg12
#print axioms Reinmann.HardTileFiniteJets.term12Value_checks
#print axioms Reinmann.HardTileFiniteJets.A_term12
#print axioms Reinmann.HardTileFiniteJets.S_term12
#print axioms Reinmann.HardTileFiniteJets.A_log13
#print axioms Reinmann.HardTileFiniteJets.S_log13
#print axioms Reinmann.HardTileFiniteJets.A_negLog13
#print axioms Reinmann.HardTileFiniteJets.S_negLog13
#print axioms Reinmann.HardTileFiniteJets.A_arg13
#print axioms Reinmann.HardTileFiniteJets.S_arg13
#print axioms Reinmann.HardTileFiniteJets.term13Value_checks
#print axioms Reinmann.HardTileFiniteJets.A_term13
#print axioms Reinmann.HardTileFiniteJets.S_term13
#print axioms Reinmann.HardTileFiniteJets.A_log14
#print axioms Reinmann.HardTileFiniteJets.S_log14
#print axioms Reinmann.HardTileFiniteJets.A_negLog14
#print axioms Reinmann.HardTileFiniteJets.S_negLog14
#print axioms Reinmann.HardTileFiniteJets.A_arg14
#print axioms Reinmann.HardTileFiniteJets.S_arg14
#print axioms Reinmann.HardTileFiniteJets.term14Value_checks
#print axioms Reinmann.HardTileFiniteJets.A_term14
#print axioms Reinmann.HardTileFiniteJets.S_term14
#print axioms Reinmann.HardTileFiniteJets.A_log15
#print axioms Reinmann.HardTileFiniteJets.S_log15
#print axioms Reinmann.HardTileFiniteJets.A_negLog15
#print axioms Reinmann.HardTileFiniteJets.S_negLog15
#print axioms Reinmann.HardTileFiniteJets.A_arg15
#print axioms Reinmann.HardTileFiniteJets.S_arg15
#print axioms Reinmann.HardTileFiniteJets.term15Value_checks
#print axioms Reinmann.HardTileFiniteJets.A_term15
#print axioms Reinmann.HardTileFiniteJets.S_term15
#print axioms Reinmann.HardTileFiniteJets.A_log16
#print axioms Reinmann.HardTileFiniteJets.S_log16
#print axioms Reinmann.HardTileFiniteJets.A_negLog16
#print axioms Reinmann.HardTileFiniteJets.S_negLog16
#print axioms Reinmann.HardTileFiniteJets.A_arg16
#print axioms Reinmann.HardTileFiniteJets.S_arg16
#print axioms Reinmann.HardTileFiniteJets.term16Value_checks
#print axioms Reinmann.HardTileFiniteJets.A_term16
#print axioms Reinmann.HardTileFiniteJets.S_term16
#print axioms Reinmann.HardTileFiniteJets.A_log17
#print axioms Reinmann.HardTileFiniteJets.S_log17
#print axioms Reinmann.HardTileFiniteJets.A_negLog17
#print axioms Reinmann.HardTileFiniteJets.S_negLog17
#print axioms Reinmann.HardTileFiniteJets.A_arg17
#print axioms Reinmann.HardTileFiniteJets.S_arg17
#print axioms Reinmann.HardTileFiniteJets.term17Value_checks
#print axioms Reinmann.HardTileFiniteJets.A_term17
#print axioms Reinmann.HardTileFiniteJets.S_term17
#print axioms Reinmann.HardTileFiniteJets.A_log18
#print axioms Reinmann.HardTileFiniteJets.S_log18
#print axioms Reinmann.HardTileFiniteJets.A_negLog18
#print axioms Reinmann.HardTileFiniteJets.S_negLog18
#print axioms Reinmann.HardTileFiniteJets.A_arg18
#print axioms Reinmann.HardTileFiniteJets.S_arg18
#print axioms Reinmann.HardTileFiniteJets.term18Value_checks
#print axioms Reinmann.HardTileFiniteJets.A_term18
#print axioms Reinmann.HardTileFiniteJets.S_term18
#print axioms Reinmann.HardTileFiniteJets.A_log19
#print axioms Reinmann.HardTileFiniteJets.S_log19
#print axioms Reinmann.HardTileFiniteJets.A_negLog19
#print axioms Reinmann.HardTileFiniteJets.S_negLog19
#print axioms Reinmann.HardTileFiniteJets.A_arg19
#print axioms Reinmann.HardTileFiniteJets.S_arg19
#print axioms Reinmann.HardTileFiniteJets.term19Value_checks
#print axioms Reinmann.HardTileFiniteJets.A_term19
#print axioms Reinmann.HardTileFiniteJets.S_term19
#print axioms Reinmann.HardTileFiniteJets.A_log20
#print axioms Reinmann.HardTileFiniteJets.S_log20
#print axioms Reinmann.HardTileFiniteJets.A_negLog20
#print axioms Reinmann.HardTileFiniteJets.S_negLog20
#print axioms Reinmann.HardTileFiniteJets.A_arg20
#print axioms Reinmann.HardTileFiniteJets.S_arg20
#print axioms Reinmann.HardTileFiniteJets.term20Value_checks
#print axioms Reinmann.HardTileFiniteJets.A_term20
#print axioms Reinmann.HardTileFiniteJets.S_term20
#print axioms Reinmann.HardTileFiniteJets.A_log21
#print axioms Reinmann.HardTileFiniteJets.S_log21
#print axioms Reinmann.HardTileFiniteJets.A_negLog21
#print axioms Reinmann.HardTileFiniteJets.S_negLog21
#print axioms Reinmann.HardTileFiniteJets.A_arg21
#print axioms Reinmann.HardTileFiniteJets.S_arg21
#print axioms Reinmann.HardTileFiniteJets.term21Value_checks
#print axioms Reinmann.HardTileFiniteJets.A_term21
#print axioms Reinmann.HardTileFiniteJets.S_term21
#print axioms Reinmann.HardTileFiniteJets.A_initial2
#print axioms Reinmann.HardTileFiniteJets.S_initial2
#print axioms Reinmann.HardTileFiniteJets.A_initial3
#print axioms Reinmann.HardTileFiniteJets.S_initial3
#print axioms Reinmann.HardTileFiniteJets.A_initial4
#print axioms Reinmann.HardTileFiniteJets.S_initial4
#print axioms Reinmann.HardTileFiniteJets.A_initial5
#print axioms Reinmann.HardTileFiniteJets.S_initial5
#print axioms Reinmann.HardTileFiniteJets.A_initial6
#print axioms Reinmann.HardTileFiniteJets.S_initial6
#print axioms Reinmann.HardTileFiniteJets.A_initial7
#print axioms Reinmann.HardTileFiniteJets.S_initial7
#print axioms Reinmann.HardTileFiniteJets.A_initial8
#print axioms Reinmann.HardTileFiniteJets.S_initial8
#print axioms Reinmann.HardTileFiniteJets.A_initial9
#print axioms Reinmann.HardTileFiniteJets.S_initial9
#print axioms Reinmann.HardTileFiniteJets.A_initial10
#print axioms Reinmann.HardTileFiniteJets.S_initial10
#print axioms Reinmann.HardTileFiniteJets.A_initial11
#print axioms Reinmann.HardTileFiniteJets.S_initial11
#print axioms Reinmann.HardTileFiniteJets.A_initial12
#print axioms Reinmann.HardTileFiniteJets.S_initial12
#print axioms Reinmann.HardTileFiniteJets.A_initial13
#print axioms Reinmann.HardTileFiniteJets.S_initial13
#print axioms Reinmann.HardTileFiniteJets.A_initial14
#print axioms Reinmann.HardTileFiniteJets.S_initial14
#print axioms Reinmann.HardTileFiniteJets.A_initial15
#print axioms Reinmann.HardTileFiniteJets.S_initial15
#print axioms Reinmann.HardTileFiniteJets.A_initial16
#print axioms Reinmann.HardTileFiniteJets.S_initial16
#print axioms Reinmann.HardTileFiniteJets.A_initial17
#print axioms Reinmann.HardTileFiniteJets.S_initial17
#print axioms Reinmann.HardTileFiniteJets.A_initial18
#print axioms Reinmann.HardTileFiniteJets.S_initial18
#print axioms Reinmann.HardTileFiniteJets.A_initial19
#print axioms Reinmann.HardTileFiniteJets.S_initial19
#print axioms Reinmann.HardTileFiniteJets.A_initial20
#print axioms Reinmann.HardTileFiniteJets.S_initial20
#print axioms Reinmann.HardTileFiniteJets.A_q12
#print axioms Reinmann.HardTileFiniteJets.S_q12
#print axioms Reinmann.HardTileFiniteJets.A_sminusone
#print axioms Reinmann.HardTileFiniteJets.S_sminusone
#print axioms Reinmann.HardTileFiniteJets.V_sminusoneInv
#print axioms Reinmann.HardTileFiniteJets.N_sminusoneInv
#print axioms Reinmann.HardTileFiniteJets.A_sminusoneInv
#print axioms Reinmann.HardTileFiniteJets.S_sminusoneInv
#print axioms Reinmann.HardTileFiniteJets.A_emIntegralProduct
#print axioms Reinmann.HardTileFiniteJets.S_emIntegralProduct
#print axioms Reinmann.HardTileFiniteJets.A_emIntegral
#print axioms Reinmann.HardTileFiniteJets.S_emIntegral
#print axioms Reinmann.HardTileFiniteJets.A_emHalf
#print axioms Reinmann.HardTileFiniteJets.S_emHalf
#print axioms Reinmann.HardTileFiniteJets.A_emInitialIntegral
#print axioms Reinmann.HardTileFiniteJets.S_emInitialIntegral
#print axioms Reinmann.HardTileFiniteJets.A_emInitialHalf
#print axioms Reinmann.HardTileFiniteJets.S_emInitialHalf
#print axioms Reinmann.HardTileFiniteJets.A_factor1
#print axioms Reinmann.HardTileFiniteJets.S_factor1
#print axioms Reinmann.HardTileFiniteJets.A_rising2
#print axioms Reinmann.HardTileFiniteJets.S_rising2
#print axioms Reinmann.HardTileFiniteJets.A_factor2
#print axioms Reinmann.HardTileFiniteJets.S_factor2
#print axioms Reinmann.HardTileFiniteJets.A_rising3
#print axioms Reinmann.HardTileFiniteJets.S_rising3
#print axioms Reinmann.HardTileFiniteJets.A_factor3
#print axioms Reinmann.HardTileFiniteJets.S_factor3
#print axioms Reinmann.HardTileFiniteJets.A_rising4
#print axioms Reinmann.HardTileFiniteJets.S_rising4
#print axioms Reinmann.HardTileFiniteJets.A_factor4
#print axioms Reinmann.HardTileFiniteJets.S_factor4
#print axioms Reinmann.HardTileFiniteJets.A_rising5
#print axioms Reinmann.HardTileFiniteJets.S_rising5
#print axioms Reinmann.HardTileFiniteJets.A_factor5
#print axioms Reinmann.HardTileFiniteJets.S_factor5
#print axioms Reinmann.HardTileFiniteJets.A_rising6
#print axioms Reinmann.HardTileFiniteJets.S_rising6
#print axioms Reinmann.HardTileFiniteJets.A_factor6
#print axioms Reinmann.HardTileFiniteJets.S_factor6
#print axioms Reinmann.HardTileFiniteJets.A_rising7
#print axioms Reinmann.HardTileFiniteJets.S_rising7
#print axioms Reinmann.HardTileFiniteJets.A_factor7
#print axioms Reinmann.HardTileFiniteJets.S_factor7
#print axioms Reinmann.HardTileFiniteJets.A_rising8
#print axioms Reinmann.HardTileFiniteJets.S_rising8
#print axioms Reinmann.HardTileFiniteJets.A_factor8
#print axioms Reinmann.HardTileFiniteJets.S_factor8
#print axioms Reinmann.HardTileFiniteJets.A_rising9
#print axioms Reinmann.HardTileFiniteJets.S_rising9
#print axioms Reinmann.HardTileFiniteJets.A_factor9
#print axioms Reinmann.HardTileFiniteJets.S_factor9
#print axioms Reinmann.HardTileFiniteJets.A_rising10
#print axioms Reinmann.HardTileFiniteJets.S_rising10
#print axioms Reinmann.HardTileFiniteJets.A_factor10
#print axioms Reinmann.HardTileFiniteJets.S_factor10
#print axioms Reinmann.HardTileFiniteJets.A_rising11
#print axioms Reinmann.HardTileFiniteJets.S_rising11
#print axioms Reinmann.HardTileFiniteJets.A_emCorrProduct1
#print axioms Reinmann.HardTileFiniteJets.S_emCorrProduct1
#print axioms Reinmann.HardTileFiniteJets.A_emCorr1
#print axioms Reinmann.HardTileFiniteJets.S_emCorr1
#print axioms Reinmann.HardTileFiniteJets.A_emAfterCorr1
#print axioms Reinmann.HardTileFiniteJets.S_emAfterCorr1
#print axioms Reinmann.HardTileFiniteJets.A_emCorrProduct2
#print axioms Reinmann.HardTileFiniteJets.S_emCorrProduct2
#print axioms Reinmann.HardTileFiniteJets.A_emCorr2
#print axioms Reinmann.HardTileFiniteJets.S_emCorr2
#print axioms Reinmann.HardTileFiniteJets.A_emAfterCorr2
#print axioms Reinmann.HardTileFiniteJets.S_emAfterCorr2
#print axioms Reinmann.HardTileFiniteJets.A_emCorrProduct3
#print axioms Reinmann.HardTileFiniteJets.S_emCorrProduct3
#print axioms Reinmann.HardTileFiniteJets.A_emCorr3
#print axioms Reinmann.HardTileFiniteJets.S_emCorr3
#print axioms Reinmann.HardTileFiniteJets.A_emAfterCorr3
#print axioms Reinmann.HardTileFiniteJets.S_emAfterCorr3
#print axioms Reinmann.HardTileFiniteJets.A_emCorrProduct4
#print axioms Reinmann.HardTileFiniteJets.S_emCorrProduct4
#print axioms Reinmann.HardTileFiniteJets.A_emCorr4
#print axioms Reinmann.HardTileFiniteJets.S_emCorr4
#print axioms Reinmann.HardTileFiniteJets.A_emAfterCorr4
#print axioms Reinmann.HardTileFiniteJets.S_emAfterCorr4
#print axioms Reinmann.HardTileFiniteJets.A_emCorrProduct5
#print axioms Reinmann.HardTileFiniteJets.S_emCorrProduct5
#print axioms Reinmann.HardTileFiniteJets.A_emCorr5
#print axioms Reinmann.HardTileFiniteJets.S_emCorr5
#print axioms Reinmann.HardTileFiniteJets.A_emAfterCorr5
#print axioms Reinmann.HardTileFiniteJets.S_emAfterCorr5
#print axioms Reinmann.HardTileFiniteJets.A_emCorrProduct6
#print axioms Reinmann.HardTileFiniteJets.S_emCorrProduct6
#print axioms Reinmann.HardTileFiniteJets.A_emCorr6
#print axioms Reinmann.HardTileFiniteJets.S_emCorr6
#print axioms Reinmann.HardTileFiniteJets.A_emAfterCorr6
#print axioms Reinmann.HardTileFiniteJets.S_emAfterCorr6
#print axioms Reinmann.HardTileFiniteJets.gammaMain_identity
#print axioms Reinmann.HardTileFiniteJets.gammaFinite_identity
#print axioms Reinmann.HardTileFiniteJets.term1_identity
#print axioms Reinmann.HardTileFiniteJets.term2_identity
#print axioms Reinmann.HardTileFiniteJets.term3_identity
#print axioms Reinmann.HardTileFiniteJets.term4_identity
#print axioms Reinmann.HardTileFiniteJets.term5_identity
#print axioms Reinmann.HardTileFiniteJets.term6_identity
#print axioms Reinmann.HardTileFiniteJets.term7_identity
#print axioms Reinmann.HardTileFiniteJets.term8_identity
#print axioms Reinmann.HardTileFiniteJets.term9_identity
#print axioms Reinmann.HardTileFiniteJets.term10_identity
#print axioms Reinmann.HardTileFiniteJets.term11_identity
#print axioms Reinmann.HardTileFiniteJets.term12_identity
#print axioms Reinmann.HardTileFiniteJets.term13_identity
#print axioms Reinmann.HardTileFiniteJets.term14_identity
#print axioms Reinmann.HardTileFiniteJets.term15_identity
#print axioms Reinmann.HardTileFiniteJets.term16_identity
#print axioms Reinmann.HardTileFiniteJets.term17_identity
#print axioms Reinmann.HardTileFiniteJets.term18_identity
#print axioms Reinmann.HardTileFiniteJets.term19_identity
#print axioms Reinmann.HardTileFiniteJets.term20_identity
#print axioms Reinmann.HardTileFiniteJets.term21_identity
#print axioms Reinmann.HardTileFiniteJets.rising1_identity
#print axioms Reinmann.HardTileFiniteJets.rising2_identity
#print axioms Reinmann.HardTileFiniteJets.rising3_identity
#print axioms Reinmann.HardTileFiniteJets.rising4_identity
#print axioms Reinmann.HardTileFiniteJets.rising5_identity
#print axioms Reinmann.HardTileFiniteJets.rising6_identity
#print axioms Reinmann.HardTileFiniteJets.rising7_identity
#print axioms Reinmann.HardTileFiniteJets.rising8_identity
#print axioms Reinmann.HardTileFiniteJets.rising9_identity
#print axioms Reinmann.HardTileFiniteJets.rising10_identity
#print axioms Reinmann.HardTileFiniteJets.rising11_identity
#print axioms Reinmann.HardTileFiniteJets.zetaFinite_identity
#print axioms Reinmann.TaylorDerivativeTail.derivative_bound
#print axioms Reinmann.HardTileXi.A_negLogPi
#print axioms Reinmann.HardTileXi.S_negLogPi
#print axioms Reinmann.HardTileXi.A_piArg
#print axioms Reinmann.HardTileXi.S_piArg
#print axioms Reinmann.HardTileXi.piPowerValue_checks
#print axioms Reinmann.HardTileXi.A_piPower
#print axioms Reinmann.HardTileXi.S_piPower
#print axioms Reinmann.HardTileXi.A_polyPrefactor
#print axioms Reinmann.HardTileXi.S_polyPrefactor
#print axioms Reinmann.HardTileXi.A_prefactor
#print axioms Reinmann.HardTileXi.S_prefactor
#print axioms Reinmann.HardTileXi.A_gammaActual
#print axioms Reinmann.HardTileXi.S_gammaApprox
#print axioms Reinmann.HardTileXi.S_gammaPerturb
#print axioms Reinmann.HardTileXi.S_gammaActual
#print axioms Reinmann.HardTileXi.A_zetaActual
#print axioms Reinmann.HardTileXi.S_zetaApprox
#print axioms Reinmann.HardTileXi.S_zetaPerturb
#print axioms Reinmann.HardTileXi.S_zetaActual
#print axioms Reinmann.HardTileXi.A_prefactorGamma
#print axioms Reinmann.HardTileXi.S_prefactorGamma
#print axioms Reinmann.HardTileXi.A_xiProduct
#print axioms Reinmann.HardTileXi.S_xiProduct
#print axioms Reinmann.HardTileXi.piPower_eq
#print axioms Reinmann.HardTileXi.xiProduct_eq_xiCompleted
#print axioms Reinmann.HardTileXi.quarter_ball_domain
#print axioms Reinmann.HardTileXi.xiProduct_eventuallyEq
#print axioms Reinmann.HardTileXi.xiCompleted_sound
#print axioms Reinmann.HardTileXi.xiCompleted_coefficient_error_budget
#print axioms Reinmann.HardTileXi.hard_centre_value
#print axioms Reinmann.HardTileXi.hard_centre_enclosure
#print axioms Reinmann.HardTileXi.xiCompleted_coeff_le_thousand
#print axioms Reinmann.HardTileXi.xiCompleted_coeff_norm_le
#print axioms Reinmann.HardTileXi.xiCompleted_coeff_le_bound
#print axioms Reinmann.HardTileXi.hard_tile_deriv_le
#print axioms Reinmann.HardTileXi.hard_tile_nonzero
#print axioms Reinmann.HardTileXi.hard_tile_zeta_nonzero

-- Uniform evaluator, regularization and closed-cell coverage rules.

#print axioms Reinmann.RegularizedEulerMaclaurin.regularZeta_one
#print axioms Reinmann.RegularizedEulerMaclaurin.regularZeta_of_ne
#print axioms Reinmann.RegularizedEulerMaclaurin.regularZeta_eventuallyEq
#print axioms Reinmann.RegularizedEulerMaclaurin.regularZeta_differentiableAt_of_ne
#print axioms Reinmann.RegularizedEulerMaclaurin.regularZeta_differentiable
#print axioms Reinmann.RegularizedEulerMaclaurin.regularModel_eq
#print axioms Reinmann.RegularizedEulerMaclaurin.regularModel_differentiable
#print axioms Reinmann.RegularizedEulerMaclaurin.regularZeta_eq_model_add_remainder
#print axioms Reinmann.RegularizedEulerMaclaurin.gammaFactor_differentiableAt
#print axioms Reinmann.RegularizedEulerMaclaurin.piFactor_differentiable
#print axioms Reinmann.RegularizedEulerMaclaurin.piFactor_eq_cpow
#print axioms Reinmann.RegularizedEulerMaclaurin.xi_eq_regular_product_of_ne
#print axioms Reinmann.RegularizedEulerMaclaurin.xi_eq_regular_product
#print axioms Reinmann.UniformXiRemainders.disk_re_bounds
#print axioms Reinmann.UniformXiRemainders.disk_norm_bounds
#print axioms Reinmann.UniformXiRemainders.gamma_norm_le_two
#print axioms Reinmann.UniformXiRemainders.gamma_norm_le_one_high
#print axioms Reinmann.UniformXiRemainders.shifted_tail_norm_le
#print axioms Reinmann.UniformXiRemainders.gamma_identity
#print axioms Reinmann.UniformXiRemainders.gammaApprox_eq
#print axioms Reinmann.UniformXiRemainders.gammaError_norm_le
#print axioms Reinmann.UniformXiRemainders.gammaApprox_differentiableAt
#print axioms Reinmann.UniformXiRemainders.gamma_coefficient_error_le
#print axioms Reinmann.UniformXiRemainders.zetaError_differentiable
#print axioms Reinmann.UniformXiRemainders.zetaError_norm_le
#print axioms Reinmann.UniformXiRemainders.zeta_coefficient_error_le
#print axioms Reinmann.RectangleTaylor.constant_sound
#print axioms Reinmann.RectangleTaylor.variable_sound
#print axioms Reinmann.RectangleTaylor.value_eq_of_exact
#print axioms Reinmann.RectangleTaylor.sound_congr
#print axioms Reinmann.RectangleTaylor.exp_sound
#print axioms Reinmann.RectangleTileRules.derivative_bound
#print axioms Reinmann.RectangleTileRules.norm_lower
#print axioms Reinmann.RectangleTileRules.xi_derivative_le
#print axioms Reinmann.RectangleTileRules.certified_tile_nonzero
#print axioms Reinmann.RationalBallCover.square_between
#print axioms Reinmann.RationalBallCover.rectangle_ball
#print axioms Reinmann.RationalBallCover.split_x
#print axioms Reinmann.RationalBallCover.split_y
#print axioms Reinmann.RectangleFiniteFormulas.power_eq
#print axioms Reinmann.RectangleFiniteFormulas.correction_eq
#print axioms Reinmann.RectangleFiniteFormulas.regularExpr_eq
#print axioms Reinmann.RectangleLogInputs.log_22
#print axioms Reinmann.RectangleLogInputs.log_23
#print axioms Reinmann.RectangleLogInputs.log_24
#print axioms Reinmann.RectangleLogInputs.log_25
#print axioms Reinmann.RectangleLogInputs.log_26
#print axioms Reinmann.RectangleLogInputs.log_27
#print axioms Reinmann.RectangleLogInputs.log2_contains
#print axioms Reinmann.RectangleLogInputs.log3_contains
#print axioms Reinmann.RectangleLogInputs.log4_contains
#print axioms Reinmann.RectangleLogInputs.log5_contains
#print axioms Reinmann.RectangleLogInputs.log6_contains
#print axioms Reinmann.RectangleLogInputs.log7_contains
#print axioms Reinmann.RectangleLogInputs.log8_contains
#print axioms Reinmann.RectangleLogInputs.log9_contains
#print axioms Reinmann.RectangleLogInputs.log10_contains
#print axioms Reinmann.RectangleLogInputs.log11_contains
#print axioms Reinmann.RectangleLogInputs.log12_contains
#print axioms Reinmann.RectangleLogInputs.log13_contains
#print axioms Reinmann.RectangleLogInputs.log14_contains
#print axioms Reinmann.RectangleLogInputs.log15_contains
#print axioms Reinmann.RectangleLogInputs.log16_contains
#print axioms Reinmann.RectangleLogInputs.log17_contains
#print axioms Reinmann.RectangleLogInputs.log18_contains
#print axioms Reinmann.RectangleLogInputs.log19_contains
#print axioms Reinmann.RectangleLogInputs.log20_contains
#print axioms Reinmann.RectangleLogInputs.log21_contains
#print axioms Reinmann.RectangleLogInputs.log22_contains
#print axioms Reinmann.RectangleLogInputs.log23_contains
#print axioms Reinmann.RectangleLogInputs.log24_contains
#print axioms Reinmann.RectangleLogInputs.log25_contains
#print axioms Reinmann.RectangleLogInputs.log26_contains
#print axioms Reinmann.RectangleLogInputs.log27_contains
#print axioms Reinmann.RectangleLogInputs.logpi_contains
#print axioms Reinmann.RectangleModel.A_variable
#print axioms Reinmann.RectangleModel.A_halfVariable
#print axioms Reinmann.RectangleModel.A_q0
#print axioms Reinmann.RectangleModel.A_base
#print axioms Reinmann.RectangleModel.A_q1
#print axioms Reinmann.RectangleModel.A_shift
#print axioms Reinmann.RectangleModel.P_shiftInv
#print axioms Reinmann.RectangleModel.N_shiftInv
#print axioms Reinmann.RectangleModel.A_shiftInv
#print axioms Reinmann.RectangleModel.L_shiftLog
#print axioms Reinmann.RectangleModel.A_shiftLog
#print axioms Reinmann.RectangleModel.A_q2
#print axioms Reinmann.RectangleModel.A_shiftMinusHalf
#print axioms Reinmann.RectangleModel.A_mainLead
#print axioms Reinmann.RectangleModel.A_negativeShift
#print axioms Reinmann.RectangleModel.A_mainMinusShift
#print axioms Reinmann.RectangleModel.A_log2
#print axioms Reinmann.RectangleModel.A_logpi
#print axioms Reinmann.RectangleModel.A_logTwoPi
#print axioms Reinmann.RectangleModel.A_halfLogTwoPi
#print axioms Reinmann.RectangleModel.A_mainConstant
#print axioms Reinmann.RectangleModel.A_invPower2
#print axioms Reinmann.RectangleModel.A_invPower3
#print axioms Reinmann.RectangleModel.A_invPower4
#print axioms Reinmann.RectangleModel.A_invPower5
#print axioms Reinmann.RectangleModel.A_invPower6
#print axioms Reinmann.RectangleModel.A_invPower7
#print axioms Reinmann.RectangleModel.A_invPower8
#print axioms Reinmann.RectangleModel.A_invPower9
#print axioms Reinmann.RectangleModel.A_invPower10
#print axioms Reinmann.RectangleModel.A_invPower11
#print axioms Reinmann.RectangleModel.A_mainTerm1
#print axioms Reinmann.RectangleModel.A_mainCorr1
#print axioms Reinmann.RectangleModel.A_mainTerm2
#print axioms Reinmann.RectangleModel.A_mainCorr2
#print axioms Reinmann.RectangleModel.A_mainTerm3
#print axioms Reinmann.RectangleModel.A_mainCorr3
#print axioms Reinmann.RectangleModel.A_mainTerm4
#print axioms Reinmann.RectangleModel.A_mainCorr4
#print axioms Reinmann.RectangleModel.A_mainTerm5
#print axioms Reinmann.RectangleModel.A_mainCorr5
#print axioms Reinmann.RectangleModel.A_mainTerm6
#print axioms Reinmann.RectangleModel.A_mainCorr6
#print axioms Reinmann.RectangleModel.A_gammaExp
#print axioms Reinmann.RectangleModel.P_gammaInverse0
#print axioms Reinmann.RectangleModel.N_gammaInverse0
#print axioms Reinmann.RectangleModel.A_gammaInverse0
#print axioms Reinmann.RectangleModel.A_gammaFactor1
#print axioms Reinmann.RectangleModel.P_gammaInverse1
#print axioms Reinmann.RectangleModel.N_gammaInverse1
#print axioms Reinmann.RectangleModel.A_gammaInverse1
#print axioms Reinmann.RectangleModel.A_gammaProduct1
#print axioms Reinmann.RectangleModel.A_q3
#print axioms Reinmann.RectangleModel.A_gammaFactor2
#print axioms Reinmann.RectangleModel.P_gammaInverse2
#print axioms Reinmann.RectangleModel.N_gammaInverse2
#print axioms Reinmann.RectangleModel.A_gammaInverse2
#print axioms Reinmann.RectangleModel.A_gammaProduct2
#print axioms Reinmann.RectangleModel.A_q4
#print axioms Reinmann.RectangleModel.A_gammaFactor3
#print axioms Reinmann.RectangleModel.P_gammaInverse3
#print axioms Reinmann.RectangleModel.N_gammaInverse3
#print axioms Reinmann.RectangleModel.A_gammaInverse3
#print axioms Reinmann.RectangleModel.A_gammaProduct3
#print axioms Reinmann.RectangleModel.A_q5
#print axioms Reinmann.RectangleModel.A_gammaFactor4
#print axioms Reinmann.RectangleModel.P_gammaInverse4
#print axioms Reinmann.RectangleModel.N_gammaInverse4
#print axioms Reinmann.RectangleModel.A_gammaInverse4
#print axioms Reinmann.RectangleModel.A_gammaProduct4
#print axioms Reinmann.RectangleModel.A_q6
#print axioms Reinmann.RectangleModel.A_gammaFactor5
#print axioms Reinmann.RectangleModel.P_gammaInverse5
#print axioms Reinmann.RectangleModel.N_gammaInverse5
#print axioms Reinmann.RectangleModel.A_gammaInverse5
#print axioms Reinmann.RectangleModel.A_gammaProduct5
#print axioms Reinmann.RectangleModel.A_q7
#print axioms Reinmann.RectangleModel.A_gammaFactor6
#print axioms Reinmann.RectangleModel.P_gammaInverse6
#print axioms Reinmann.RectangleModel.N_gammaInverse6
#print axioms Reinmann.RectangleModel.A_gammaInverse6
#print axioms Reinmann.RectangleModel.A_gammaProduct6
#print axioms Reinmann.RectangleModel.A_q8
#print axioms Reinmann.RectangleModel.A_gammaFactor7
#print axioms Reinmann.RectangleModel.P_gammaInverse7
#print axioms Reinmann.RectangleModel.N_gammaInverse7
#print axioms Reinmann.RectangleModel.A_gammaInverse7
#print axioms Reinmann.RectangleModel.A_gammaProduct7
#print axioms Reinmann.RectangleModel.A_q9
#print axioms Reinmann.RectangleModel.A_gammaFactor8
#print axioms Reinmann.RectangleModel.P_gammaInverse8
#print axioms Reinmann.RectangleModel.N_gammaInverse8
#print axioms Reinmann.RectangleModel.A_gammaInverse8
#print axioms Reinmann.RectangleModel.A_gammaProduct8
#print axioms Reinmann.RectangleModel.A_q10
#print axioms Reinmann.RectangleModel.A_gammaFactor9
#print axioms Reinmann.RectangleModel.P_gammaInverse9
#print axioms Reinmann.RectangleModel.N_gammaInverse9
#print axioms Reinmann.RectangleModel.A_gammaInverse9
#print axioms Reinmann.RectangleModel.A_gammaProduct9
#print axioms Reinmann.RectangleModel.A_q11
#print axioms Reinmann.RectangleModel.A_gammaFactor10
#print axioms Reinmann.RectangleModel.P_gammaInverse10
#print axioms Reinmann.RectangleModel.N_gammaInverse10
#print axioms Reinmann.RectangleModel.A_gammaInverse10
#print axioms Reinmann.RectangleModel.A_gammaProduct10
#print axioms Reinmann.RectangleModel.A_q12
#print axioms Reinmann.RectangleModel.A_gammaFactor11
#print axioms Reinmann.RectangleModel.P_gammaInverse11
#print axioms Reinmann.RectangleModel.N_gammaInverse11
#print axioms Reinmann.RectangleModel.A_gammaInverse11
#print axioms Reinmann.RectangleModel.A_gammaProduct11
#print axioms Reinmann.RectangleModel.A_gammaFinite
#print axioms Reinmann.RectangleModel.A_gammaActual
#print axioms Reinmann.RectangleModel.A_negLog2
#print axioms Reinmann.RectangleModel.A_arg2
#print axioms Reinmann.RectangleModel.A_term2
#print axioms Reinmann.RectangleModel.A_log3
#print axioms Reinmann.RectangleModel.A_negLog3
#print axioms Reinmann.RectangleModel.A_arg3
#print axioms Reinmann.RectangleModel.A_term3
#print axioms Reinmann.RectangleModel.A_log4
#print axioms Reinmann.RectangleModel.A_negLog4
#print axioms Reinmann.RectangleModel.A_arg4
#print axioms Reinmann.RectangleModel.A_term4
#print axioms Reinmann.RectangleModel.A_log5
#print axioms Reinmann.RectangleModel.A_negLog5
#print axioms Reinmann.RectangleModel.A_arg5
#print axioms Reinmann.RectangleModel.A_term5
#print axioms Reinmann.RectangleModel.A_log6
#print axioms Reinmann.RectangleModel.A_negLog6
#print axioms Reinmann.RectangleModel.A_arg6
#print axioms Reinmann.RectangleModel.A_term6
#print axioms Reinmann.RectangleModel.A_log7
#print axioms Reinmann.RectangleModel.A_negLog7
#print axioms Reinmann.RectangleModel.A_arg7
#print axioms Reinmann.RectangleModel.A_term7
#print axioms Reinmann.RectangleModel.A_log8
#print axioms Reinmann.RectangleModel.A_negLog8
#print axioms Reinmann.RectangleModel.A_arg8
#print axioms Reinmann.RectangleModel.A_term8
#print axioms Reinmann.RectangleModel.A_log9
#print axioms Reinmann.RectangleModel.A_negLog9
#print axioms Reinmann.RectangleModel.A_arg9
#print axioms Reinmann.RectangleModel.A_term9
#print axioms Reinmann.RectangleModel.A_log10
#print axioms Reinmann.RectangleModel.A_negLog10
#print axioms Reinmann.RectangleModel.A_arg10
#print axioms Reinmann.RectangleModel.A_term10
#print axioms Reinmann.RectangleModel.A_log11
#print axioms Reinmann.RectangleModel.A_negLog11
#print axioms Reinmann.RectangleModel.A_arg11
#print axioms Reinmann.RectangleModel.A_term11
#print axioms Reinmann.RectangleModel.A_log12
#print axioms Reinmann.RectangleModel.A_negLog12
#print axioms Reinmann.RectangleModel.A_arg12
#print axioms Reinmann.RectangleModel.A_term12
#print axioms Reinmann.RectangleModel.A_log13
#print axioms Reinmann.RectangleModel.A_negLog13
#print axioms Reinmann.RectangleModel.A_arg13
#print axioms Reinmann.RectangleModel.A_term13
#print axioms Reinmann.RectangleModel.A_log14
#print axioms Reinmann.RectangleModel.A_negLog14
#print axioms Reinmann.RectangleModel.A_arg14
#print axioms Reinmann.RectangleModel.A_term14
#print axioms Reinmann.RectangleModel.A_log15
#print axioms Reinmann.RectangleModel.A_negLog15
#print axioms Reinmann.RectangleModel.A_arg15
#print axioms Reinmann.RectangleModel.A_term15
#print axioms Reinmann.RectangleModel.A_log16
#print axioms Reinmann.RectangleModel.A_negLog16
#print axioms Reinmann.RectangleModel.A_arg16
#print axioms Reinmann.RectangleModel.A_term16
#print axioms Reinmann.RectangleModel.A_log17
#print axioms Reinmann.RectangleModel.A_negLog17
#print axioms Reinmann.RectangleModel.A_arg17
#print axioms Reinmann.RectangleModel.A_term17
#print axioms Reinmann.RectangleModel.A_log18
#print axioms Reinmann.RectangleModel.A_negLog18
#print axioms Reinmann.RectangleModel.A_arg18
#print axioms Reinmann.RectangleModel.A_term18
#print axioms Reinmann.RectangleModel.A_log19
#print axioms Reinmann.RectangleModel.A_negLog19
#print axioms Reinmann.RectangleModel.A_arg19
#print axioms Reinmann.RectangleModel.A_term19
#print axioms Reinmann.RectangleModel.A_log20
#print axioms Reinmann.RectangleModel.A_negLog20
#print axioms Reinmann.RectangleModel.A_arg20
#print axioms Reinmann.RectangleModel.A_term20
#print axioms Reinmann.RectangleModel.A_log21
#print axioms Reinmann.RectangleModel.A_negLog21
#print axioms Reinmann.RectangleModel.A_arg21
#print axioms Reinmann.RectangleModel.A_term21
#print axioms Reinmann.RectangleModel.A_log22
#print axioms Reinmann.RectangleModel.A_negLog22
#print axioms Reinmann.RectangleModel.A_arg22
#print axioms Reinmann.RectangleModel.A_term22
#print axioms Reinmann.RectangleModel.A_log23
#print axioms Reinmann.RectangleModel.A_negLog23
#print axioms Reinmann.RectangleModel.A_arg23
#print axioms Reinmann.RectangleModel.A_term23
#print axioms Reinmann.RectangleModel.A_log24
#print axioms Reinmann.RectangleModel.A_negLog24
#print axioms Reinmann.RectangleModel.A_arg24
#print axioms Reinmann.RectangleModel.A_term24
#print axioms Reinmann.RectangleModel.A_log25
#print axioms Reinmann.RectangleModel.A_negLog25
#print axioms Reinmann.RectangleModel.A_arg25
#print axioms Reinmann.RectangleModel.A_term25
#print axioms Reinmann.RectangleModel.A_log26
#print axioms Reinmann.RectangleModel.A_negLog26
#print axioms Reinmann.RectangleModel.A_arg26
#print axioms Reinmann.RectangleModel.A_term26
#print axioms Reinmann.RectangleModel.A_log27
#print axioms Reinmann.RectangleModel.A_negLog27
#print axioms Reinmann.RectangleModel.A_arg27
#print axioms Reinmann.RectangleModel.A_term27
#print axioms Reinmann.RectangleModel.A_initial2
#print axioms Reinmann.RectangleModel.A_initial3
#print axioms Reinmann.RectangleModel.A_initial4
#print axioms Reinmann.RectangleModel.A_initial5
#print axioms Reinmann.RectangleModel.A_initial6
#print axioms Reinmann.RectangleModel.A_initial7
#print axioms Reinmann.RectangleModel.A_initial8
#print axioms Reinmann.RectangleModel.A_initial9
#print axioms Reinmann.RectangleModel.A_initial10
#print axioms Reinmann.RectangleModel.A_initial11
#print axioms Reinmann.RectangleModel.A_initial12
#print axioms Reinmann.RectangleModel.A_initial13
#print axioms Reinmann.RectangleModel.A_initial14
#print axioms Reinmann.RectangleModel.A_initial15
#print axioms Reinmann.RectangleModel.A_initial16
#print axioms Reinmann.RectangleModel.A_initial17
#print axioms Reinmann.RectangleModel.A_initial18
#print axioms Reinmann.RectangleModel.A_initial19
#print axioms Reinmann.RectangleModel.A_initial20
#print axioms Reinmann.RectangleModel.A_initial21
#print axioms Reinmann.RectangleModel.A_initial22
#print axioms Reinmann.RectangleModel.A_initial23
#print axioms Reinmann.RectangleModel.A_initial24
#print axioms Reinmann.RectangleModel.A_initial25
#print axioms Reinmann.RectangleModel.A_initial26
#print axioms Reinmann.RectangleModel.A_endpointHalf
#print axioms Reinmann.RectangleModel.A_initialHalf
#print axioms Reinmann.RectangleModel.A_risingFactor1
#print axioms Reinmann.RectangleModel.A_rising2
#print axioms Reinmann.RectangleModel.A_risingFactor2
#print axioms Reinmann.RectangleModel.A_rising3
#print axioms Reinmann.RectangleModel.A_risingFactor3
#print axioms Reinmann.RectangleModel.A_rising4
#print axioms Reinmann.RectangleModel.A_risingFactor4
#print axioms Reinmann.RectangleModel.A_rising5
#print axioms Reinmann.RectangleModel.A_risingFactor5
#print axioms Reinmann.RectangleModel.A_rising6
#print axioms Reinmann.RectangleModel.A_risingFactor6
#print axioms Reinmann.RectangleModel.A_rising7
#print axioms Reinmann.RectangleModel.A_risingFactor7
#print axioms Reinmann.RectangleModel.A_rising8
#print axioms Reinmann.RectangleModel.A_risingFactor8
#print axioms Reinmann.RectangleModel.A_rising9
#print axioms Reinmann.RectangleModel.A_risingFactor9
#print axioms Reinmann.RectangleModel.A_rising10
#print axioms Reinmann.RectangleModel.A_risingFactor10
#print axioms Reinmann.RectangleModel.A_rising11
#print axioms Reinmann.RectangleModel.A_zetaCorrProduct1
#print axioms Reinmann.RectangleModel.A_zetaCorr1
#print axioms Reinmann.RectangleModel.A_zetaPart1
#print axioms Reinmann.RectangleModel.A_zetaCorrProduct2
#print axioms Reinmann.RectangleModel.A_zetaCorr2
#print axioms Reinmann.RectangleModel.A_zetaPart2
#print axioms Reinmann.RectangleModel.A_zetaCorrProduct3
#print axioms Reinmann.RectangleModel.A_zetaCorr3
#print axioms Reinmann.RectangleModel.A_zetaPart3
#print axioms Reinmann.RectangleModel.A_zetaCorrProduct4
#print axioms Reinmann.RectangleModel.A_zetaCorr4
#print axioms Reinmann.RectangleModel.A_zetaPart4
#print axioms Reinmann.RectangleModel.A_zetaCorrProduct5
#print axioms Reinmann.RectangleModel.A_zetaCorr5
#print axioms Reinmann.RectangleModel.A_zetaPart5
#print axioms Reinmann.RectangleModel.A_zetaCorrProduct6
#print axioms Reinmann.RectangleModel.A_zetaCorr6
#print axioms Reinmann.RectangleModel.A_zetaPart6
#print axioms Reinmann.RectangleModel.A_q13
#print axioms Reinmann.RectangleModel.A_sminusone
#print axioms Reinmann.RectangleModel.A_zetaRegularPart
#print axioms Reinmann.RectangleModel.A_zetaIntegral
#print axioms Reinmann.RectangleModel.A_zetaFinite
#print axioms Reinmann.RectangleModel.A_zetaActual
#print axioms Reinmann.RectangleModel.A_negativeHalfLogPi
#print axioms Reinmann.RectangleModel.A_piArg
#print axioms Reinmann.RectangleModel.A_piPower
#print axioms Reinmann.RectangleModel.A_piGamma
#print axioms Reinmann.RectangleModel.A_xiProduct
#print axioms Reinmann.RectangleModel.gammaMain_identity
#print axioms Reinmann.RectangleModel.shift_identity
#print axioms Reinmann.RectangleModel.gammaFinite_identity
#print axioms Reinmann.RectangleModel.term_1_identity
#print axioms Reinmann.RectangleModel.term_2_identity
#print axioms Reinmann.RectangleModel.term_3_identity
#print axioms Reinmann.RectangleModel.term_4_identity
#print axioms Reinmann.RectangleModel.term_5_identity
#print axioms Reinmann.RectangleModel.term_6_identity
#print axioms Reinmann.RectangleModel.term_7_identity
#print axioms Reinmann.RectangleModel.term_8_identity
#print axioms Reinmann.RectangleModel.term_9_identity
#print axioms Reinmann.RectangleModel.term_10_identity
#print axioms Reinmann.RectangleModel.term_11_identity
#print axioms Reinmann.RectangleModel.term_12_identity
#print axioms Reinmann.RectangleModel.term_13_identity
#print axioms Reinmann.RectangleModel.term_14_identity
#print axioms Reinmann.RectangleModel.term_15_identity
#print axioms Reinmann.RectangleModel.term_16_identity
#print axioms Reinmann.RectangleModel.term_17_identity
#print axioms Reinmann.RectangleModel.term_18_identity
#print axioms Reinmann.RectangleModel.term_19_identity
#print axioms Reinmann.RectangleModel.term_20_identity
#print axioms Reinmann.RectangleModel.term_21_identity
#print axioms Reinmann.RectangleModel.term_22_identity
#print axioms Reinmann.RectangleModel.term_23_identity
#print axioms Reinmann.RectangleModel.term_24_identity
#print axioms Reinmann.RectangleModel.term_25_identity
#print axioms Reinmann.RectangleModel.term_26_identity
#print axioms Reinmann.RectangleModel.term_27_identity
#print axioms Reinmann.RectangleModel.rising_1_identity
#print axioms Reinmann.RectangleModel.rising_2_identity
#print axioms Reinmann.RectangleModel.rising_3_identity
#print axioms Reinmann.RectangleModel.rising_4_identity
#print axioms Reinmann.RectangleModel.rising_5_identity
#print axioms Reinmann.RectangleModel.rising_6_identity
#print axioms Reinmann.RectangleModel.rising_7_identity
#print axioms Reinmann.RectangleModel.rising_8_identity
#print axioms Reinmann.RectangleModel.rising_9_identity
#print axioms Reinmann.RectangleModel.rising_10_identity
#print axioms Reinmann.RectangleModel.rising_11_identity
#print axioms Reinmann.RectangleModel.zetaFinite_identity
#print axioms Reinmann.RectangleModel.piPower_identity
#print axioms Reinmann.RectangleModel.xiProduct_identity
#print axioms Reinmann.RectangleModel.gamma_sound
#print axioms Reinmann.RectangleModel.zeta_sound
#print axioms Reinmann.RectangleModel.xi_sound
#print axioms Reinmann.RectangleModel.log_scaled16_contains

-- PF43 chain: every theorem constant in these modules and in Reinmann.PNTPlus.*.
open Lean in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for i in [:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    if "Reinmann.PNTPlus.".isPrefixOf m.toString ||
        m == `Reinmann.CanonicalZeroIndex ||
        m == `Reinmann.FinitePFAnalyticLimits ||
        m == `Reinmann.FinitePFConvolution ||
        m == `Reinmann.FinitePFLimits ||
        m == `Reinmann.FoldedSectorGeometry ||
        m == `Reinmann.GenusZeroProductLimits ||
        m == `Reinmann.MatrixMinorProduct ||
        m == `Reinmann.PolynomialSectorPF ||
        m == `Reinmann.QuadraticPF ||
        m == `Reinmann.RealGenusZeroApproximants ||
        m == `Reinmann.XiCanonicalProductSector ||
        m == `Reinmann.XiGenusZeroSector ||
        m == `Reinmann.XiZeroCorrespondence ||
        m == `Reinmann.XiHadamardProduct then
      let d := env.header.moduleData[i]!
      for j in [:d.constNames.size] do
        if d.constants[j]!.isTheorem then
          names := names.push d.constNames[j]!
  for n in names.qsort Name.lt do
    let axioms ← collectAxioms n
    if axioms.isEmpty then
      logInfo m!"'{n}' does not depend on any axioms"
    else
      logInfo m!"'{n}' depends on axioms: {axioms.qsort Name.lt |>.map MessageData.ofConstName |>.toList}"
