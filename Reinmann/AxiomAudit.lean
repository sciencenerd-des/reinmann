/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
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
