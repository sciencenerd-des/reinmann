# RH Theorem Targets from the Current Knowledge Base

**Status:** theorem-target map, not a proof of RH.

The current program now has three explicit levels.  This keeps the work honest:
we can push hard toward RH without confusing partial positivity with the full
Pólya-frequency statement that would actually close the problem.

## Level 1: Order-3 frontier

Lean target:

- `Order3FrontierTheorem`
- `xiToeplitzOrder3Positive_of_order3Frontier`
- `xiToeplitzOrder3Positive_of_order3CrossField`

Mathematical meaning:

Prove the first Toeplitz determinant beyond the known Turán/order-2 rung.  The
candidate sources are combinatorial Hodge theory, Lorentzian polynomial
coefficients, lattice-path total positivity, Weil/Hodge positivity models,
Euclidean convexity inequalities, or hyperbolic spectral trace formulas.

This would be genuine progress, but it would not solve RH by itself.

## Level 2: Contiguous all-order kernel positivity

Lean target:

- `KernelContigTotalPositive`
- `XiContigToeplitzTotalPositive`
- `xiContigToeplitzTotalPositive_iff_kernelContig`
- `xiContigToeplitzTotalPositive_of_kernelContigWitness`

Mathematical meaning:

Prove every contiguous factorial-weighted moment Toeplitz determinant coming
from Polya's xi-kernel.  This is much stronger than order 3 and would give a
coherent analytic/combinatorial ladder.

This is still not the full Edrei-ASW Pólya-frequency condition, because RH needs
arbitrary Toeplitz minors, not only contiguous blocks.

## Level 2.5: Contiguous-to-full PF upgrade

Lean target:

- `XiContigToFullPFBridge`
- `XiArbitraryMinorReductionToContig`
- `XiMinorContigCertificate`
- `XiAllMinorContigCertificates`
- `xiToeplitzEntry_nonneg_of_contig`
- `XiMomentCoeffNonnegativeFromContig`
- `xiMomentCoeffNonnegative_of_contig`
- `XiMomentCoeffPositive`
- `xiMomentCoeffPositive_of_kernelRep`
- `xiMinorZeroContigCertificate`
- `exists_xiMinorZeroContigCertificate`
- `xiContiguousMinorSelfCertificate`
- `exists_contiguousMinorSelfCertificate`
- `xiMinorOneContigCertificate`
- `exists_xiMinorOneContigCertificate`
- `xiZeroSupportMinorCertificate`
- `exists_xiZeroSupportMinorCertificate`
- `xiZeroRowMinorCertificate`
- `exists_xiZeroRowMinorCertificate`
- `xiZeroColumnMinorCertificate`
- `exists_xiZeroColumnMinorCertificate`
- `xiMinorTwoUpperRightZeroCertificate`
- `exists_xiMinorTwoUpperRightZeroCertificate`
- `XiMinorTwoFullSupportFromContig`
- `XiMinorTwoGapInequalityFromContig`
- `XiMomentRatioMongeFromContig`
- `XiMomentAdjacentRatioMongeFromContig`
- `XiMomentUnitRatioMongeFromContig`
- `xiMomentUnitRatioMonge_of_contig`
- `two_step_ratio_cancel`
- `XiMomentAdjacentRatioGap`
- `xiMomentAdjacentRatioGap_one_of_contig`
- `XiMomentAdjacentRatioGapSuccBridge`
- `xiMomentAdjacentRatioGapSuccBridge_of_strictPositivity`
- `xiMomentAdjacentRatioMonge_of_gapSuccBridge`
- `XiUnitRatioToAdjacentRatioBridge`
- `XiUnitRatioToAdjacentRatioWithPositivityBridge`
- `xiUnitRatioToAdjacentRatioBridge_of_withPositivity`
- `XiUnitRatioToAdjacentRatioWithStrictPositivityBridge`
- `xiUnitRatioToAdjacentRatioWithStrictPositivityBridge_of_gapInduction`
- `xiUnitRatioToAdjacentRatioBridge_of_strictPositivity`
- `xiUnitRatioToAdjacentRatioBridge_of_kernelRep`
- `xiMomentAdjacentRatioMonge_of_unitBridge`
- `xiMomentAdjacentRatioMonge_of_kernelRep`
- `XiUnitRatioRoute`
- `xiMomentAdjacentRatioMonge_of_unitRoute`
- `two_step_ratio_cancel_general`
- `XiAdjacentRatioToGlobalRatioBridge`
- `XiMomentRatioDistanceFromAdjacent`
- `xiMomentRatioDistance_zero`
- `xiMomentRatioDistance_succ_of_adjacent_strictPositivity`
- `xiMomentRatioMonge_of_adjacentRatio_strictPositivity`
- `XiAdjacentRatioToGlobalRatioWithStrictPositivityBridge`
- `xiAdjacentRatioToGlobalRatioWithStrictPositivityBridge_of_distanceInduction`
- `xiAdjacentRatioToGlobalRatioBridge_of_kernelRep`
- `xiMomentRatioMonge_of_adjacentRatioBridge`
- `xiMomentRatioMonge_of_kernelRep`
- `XiAdjacentRatioRoute`
- `xiMomentRatioMonge_of_adjacentRatioRoute`
- `xiMinorTwoGapInequalityFromContig_of_ratioMonge`
- `xiMinorTwoGapInequalityFromContig_of_kernelRep`
- `xiMinorTwoFullSupportFromContig_of_gapInequality`
- `xiMinorTwoFullSupportFromContig_of_kernelRep`
- `xiMinorTwoFullSupportCertificate`
- `exists_xiMinorTwoFullSupportCertificate`
- `exists_xiMinorTwoContigCertificate_of_kernelRep`
- `XiMinorThreeFullSupportFromContig`
- `XiMinorThreeFullSupportMomentFromContig`
- `xiMinorThreeFullSupportFromContig_of_moment`
- `xiMinorThreeFullSupportCertificate`
- `exists_xiMinorThreeFullSupportCertificate`
- `XiAllMinorGeThreeContigCertificates`
- `XiMinorThreeContigCertificates`
- `XiMinorThreeMixedSupportCertificates`
- `XiMinorThreeBandedMixedSupportCertificates`
- `XiMinorThreeBandedDetInequalityFromContig`
- `XiMinorThreeBandedExpandedInequalityFromContig`
- `XiMinorThreeBandedMiddleMomentInequalityFromContig`
- `XiMinorThreeBandedMiddleCompoundRatioFromContig`
- `XiMinorThreeMomentPayloadFromContig`
- `xiMinorThreeFullSupportMoment_of_momentPayload`
- `xiMinorThreeBandedMiddleCompoundRatio_of_momentPayload`
- `xiMinorThreeBandedMiddleMoment_of_compoundRatio`
- `xiMinorThreeBandedExpandedInequality_of_middleMoment`
- `XiMinorThreeBandedT01ZeroInequalityFromContig`
- `XiMinorThreeBandedT12ZeroInequalityFromContig`
- `XiMinorThreeBandedT01ZeroSimplifiedFromContig`
- `XiMinorThreeBandedT12ZeroSimplifiedFromContig`
- `XiMinorThreeBandedT01ZeroBracketFromContig`
- `XiMinorThreeBandedT12ZeroBracketFromContig`
- `xiMinorThreeBandedT01ZeroBracket_of_twoFullSupport`
- `xiMinorThreeBandedT12ZeroBracket_of_twoFullSupport`
- `xiMinorThreeBandedT01ZeroBracket_of_kernelRep`
- `xiMinorThreeBandedT12ZeroBracket_of_kernelRep`
- `xiMinorThreeBandedT01ZeroSimplified_of_bracket`
- `xiMinorThreeBandedT12ZeroSimplified_of_bracket`
- `xiMinorThreeBandedT01ZeroInequality_of_simplified`
- `xiMinorThreeBandedT12ZeroInequality_of_simplified`
- `xiMinorThreeBandedExpandedInequality_of_middleMoment_and_zeroEdges`
- `XiMinorThreeBandedEdgeCaseCertificates`
- `xiMinorThreeBandedEdgeCaseCertificates_of_zeroEdges`
- `xiMinorThreeBandedExpandedInequality_of_middleMoment_and_edgeCases`
- `xiMinorThreeBandedDetInequality_of_expanded`
- `xiMinorThreeBandedDetCertificate`
- `xiMinorThreeBandedMixedSupportCertificates_of_detInequality`
- `xiMinorThreeMixedSupportCertificates_of_banded`
- `xiMinorThreeContigCertificates_of_full_and_mixed`
- `XiAllMinorGeFourContigCertificates`
- `XiMinorFourContigCertificates`
- `XiMinorFourFullSupportFromContig`
- `XiMinorFourFullSupportMomentFromContig`
- `XiLowRankMomentPayloadFromContig`
- `xiMinorThreeMomentPayload_of_lowRankMomentPayload`
- `xiMinorFourFullSupportMoment_of_lowRankMomentPayload`
- `xiMinorFourFullSupportFromContig_of_moment`
- `xiMinorFourFullSupportCertificate`
- `exists_xiMinorFourFullSupportCertificate`
- `XiMinorFourMixedSupportCertificates`
- `XiMinorFourBandedMixedSupportCertificates`
- `xiMinorFourMixedSupportCertificates_of_banded`
- `xiMinorFourContigCertificates_of_full_and_mixed`
- `XiAllMinorGeFiveContigCertificates`
- `xiAllMinorGeFour_of_four_and_geFive`
- `xiAllMinorGeThree_of_three_and_geFour`
- `xiAllMinorContigCertificates_of_kernelRep_and_geThree`
- `arbitraryMinorReduction_of_allMinorContigCertificates`
- `xiContigToFullPFBridge_of_allMinorContigCertificates`
- `xiContigToFullPFBridge_of_kernelRep_and_geThree`
- `xiContigToFullPFBridge_of_kernelRep_three_and_geFour`
- `xiContigToFullPFBridge_of_kernelRep_threeFullMixed_and_geFour`
- `xiContigToFullPFBridge_of_kernelRep_threeFullBandedMixed_and_geFour`
- `xiContigToFullPFBridge_of_kernelRep_threeFullBandedDet_and_geFour`
- `xiContigToFullPFBridge_of_kernelRep_threeFullBandedExpanded_and_geFour`
- `xiContigToFullPFBridge_of_kernelRep_threeFullMiddleMoment_and_edgeCases_geFour`
- `xiContigToFullPFBridge_of_kernelRep_threeFullMiddleMoment_zeroEdges_geFour`
- `xiContigToFullPFBridge_of_kernelRep_threeFullMiddleMoment_simplifiedZeroEdges_geFour`
- `xiContigToFullPFBridge_of_kernelRep_threeFullMiddleMoment_bracketZeroEdges_geFour`
- `xiContigToFullPFBridge_of_kernelRep_threeFullMiddleMoment_geFour`
- `xiContigToFullPFBridge_iff_arbitraryMinorReduction`
- `KernelContigToPFTheorem`
- `KernelContigToPFGeThreeTheorem`
- `KernelContigToPFThreeAndGeFourTheorem`
- `KernelContigToPFThreeSupportSplitTheorem`
- `KernelContigToPFThreeBandedSupportTheorem`
- `KernelContigToPFThreeBandedDetTheorem`
- `KernelContigToPFThreeBandedExpandedTheorem`
- `KernelContigToPFThreeMiddleMomentTheorem`
- `KernelContigToPFThreeZeroEdgesTheorem`
- `KernelContigToPFThreeSimplifiedZeroEdgesTheorem`
- `KernelContigToPFThreeBracketZeroEdgesTheorem`
- `KernelContigToPFThreeKernelZeroEdgesTheorem`
- `KernelContigToPFThreeCompoundRatioTheorem`
- `KernelContigToPFThreeMomentCompoundRatioTheorem`
- `KernelContigToPFThreeMomentPayloadTheorem`
- `KernelContigToPFThreeMomentPayloadFourAndGeFiveTheorem`
- `KernelContigToPFThreeMomentPayloadFourSupportSplitTheorem`
- `KernelContigToPFThreeMomentPayloadFourMomentSupportSplitTheorem`
- `KernelContigToPFLowRankMomentFourMixedTheorem`
- `KernelContigToPFLowRankMomentFourBandedMixedTheorem`
- `KernelContigToPFLowRankMomentFourBandedDetTheorem`
- `KernelContigToPFLowRankMomentFourBandedUpperRightZeroTheorem`
- `KernelContigToPFLowRankMomentFourBandedRowZeroCofactorTheorem`
- `KernelContigToPFLowRankMomentFourBandedThreeCofactorTheorem`
- `KernelContigToPFLowRankMomentFourBandedNamedCofactorTheorem`
- `KernelContigToPFLowRankMomentFourBandedCofactorRowColTheorem`
- `KernelContigToPFLowRankMomentFourBandedCofactorSupportSplitTheorem`
- `KernelContigToPFLowRankMomentFourBandedCofactorJ012Theorem`
- `KernelContigToPFLowRankMomentFourBandedCofactorJ12Theorem`
- `KernelContigToPFLowRankMomentFourBandedCofactorJ2Theorem`
- `KernelContigToPFLowRankMomentFourBandedCofactorSupportSplitOnlyTheorem`
- `KernelContigToPFLowRankMomentFourBandedCofactorCaseTableTheorem`
- `KernelContigToPFLowRankMomentFourBandedCofactorNonzeroCaseTableTheorem`
- `KernelContigToPFLowRankMomentFourBandedCofactorSurvivorSplitTheorem`
- `KernelContigToPFLowRankMomentFourBandedCofactorOneSurvivorPositionTheorem`
- `KernelContigToPFLowRankMomentFourBandedCofactorPositiveOneSurvivorTheorem`
- `KernelContigToPFLowRankMomentFourBandedCofactorPositiveOneSurvivorSupportTheorem`
- `KernelContigToPFLowRankMomentFourBandedCofactorPositiveFullTheorem`
- `KernelContigToPFLowRankMomentFourBandedCofactorPositiveFullDetTheorem`
- `KernelContigToPFLowRankMomentFourBandedCofactorThreeFullTheorem`
- `KernelContigToPFLowRankMomentFourBandedCofactorThreeFullBandedTheorem`
- `KernelContigToPFLowRankMomentFourBandedCofactorJ1NonposTheorem`
- `KernelContigToPFLowRankMomentFourBandedCofactorJ1SupportSplitTheorem`
- `KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentTheorem`
- `KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroTheorem`
- `KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedExpandedTheorem`
- `KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedProductTheorem`
- `KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedSignsTheorem`
- `KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedSplitTheorem`
- `KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedTopSupportTheorem`
- `KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedTopMomentTheorem`
- `KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedTopMomentMiddleTheorem`
- `xiMinorFourBandedCofactorDet_eq_zero_of_zeroRowSupport`
- `xiMinorFourBandedCofactorDet_eq_zero_of_zeroColumnSupport`
- `xiMinorFourBandedCofactorDet_eq_zero_of_inactiveKind`
- `xiMinorFourBandedCofactorPositiveFullDet_of_threeFull`
- `xiMinorFourBandedCofactorPositiveBandedOneSurvivor_of_threeBandedDet`
- `xiMinorFourBandedCofactorOneSurvivorJ1_of_nonposDet`
- `xiMinorFourBandedCofactorOneSurvivorJ1NonposDet_of_supportSplit`
- `xiMinorFourBandedCofactorOneSurvivorJ1FullNonposDet_of_moment`
- `xiMinorFourBandedCofactorOneSurvivorJ1FullMomentNonposDet_of_zero`
- `xiMinorFourBandedCofactorOneSurvivorJ1BandedTopSupportedSplitBrackets_of_moment`
- `xiMinorFourBandedCofactorOneSurvivorJ1BandedTopUnsupportedSplitBrackets_of_middleSupported`
- `xiMinorFourBandedCofactorOneSurvivorJ1BandedSplitBrackets_of_topSupportSplit`
- `xiMinorFourBandedCofactorOneSurvivorJ1BandedBracketSigns_of_split`
- `xiMinorFourBandedCofactorOneSurvivorJ1BandedProductDominance_of_bracketSigns`
- `xiMinorFourBandedCofactorOneSurvivorJ1BandedExpandedNonpos_of_productDominance`
- `xiMinorFourBandedCofactorOneSurvivorJ1BandedNonposDet_of_expanded`
- `kernelContigToPF_of_geThree`
- `kernelContigToPFGeThree_of_three_and_geFour`
- `kernelContigToPFThreeAndGeFour_of_threeSupportSplit`
- `kernelContigToPFThreeSupportSplit_of_bandedSupport`
- `kernelContigToPFThreeBandedSupport_of_bandedDet`
- `kernelContigToPFThreeBandedDet_of_expanded`
- `kernelContigToPFThreeBandedExpanded_of_middleMoment`
- `kernelContigToPFThreeMiddleMoment_of_zeroEdges`
- `kernelContigToPFThreeZeroEdges_of_simplified`
- `kernelContigToPFThreeSimplifiedZeroEdges_of_bracketZeroEdges`
- `kernelContigToPFThreeBracketZeroEdges_of_kernelZeroEdges`
- `kernelContigToPFThreeKernelZeroEdges_of_compoundRatio`
- `kernelContigToPFThreeCompoundRatio_of_momentCompoundRatio`
- `kernelContigToPFThreeMomentCompoundRatio_of_momentPayload`
- `kernelContigToPFThreeMomentPayload_of_four_and_geFive`
- `kernelContigToPFThreeMomentPayloadFourAndGeFive_of_fourSupportSplit`
- `kernelContigToPFThreeMomentPayloadFourSupportSplit_of_fourMomentSupportSplit`
- `kernelContigToPFThreeMomentPayloadFourMomentSupportSplit_of_lowRankMoment`
- `kernelContigToPFLowRankMomentFourMixed_of_bandedMixed`
- `kernelContigToPFLowRankMomentFourBandedMixed_of_bandedDet`
- `kernelContigToPFLowRankMomentFourBandedDet_of_upperRightZero`
- `kernelContigToPFLowRankMomentFourBandedUpperRightZero_of_rowZeroCofactor`
- `kernelContigToPFLowRankMomentFourBandedRowZeroCofactor_of_threeCofactor`
- `kernelContigToPFLowRankMomentFourBandedThreeCofactor_of_namedCofactor`
- `kernelContigToPFLowRankMomentFourBandedNamedCofactor_of_rowCol`
- `kernelContigToPFLowRankMomentFourBandedCofactorRowCol_of_supportSplit`
- `kernelContigToPFLowRankMomentFourBandedCofactorSupportSplit_of_j012`
- `kernelContigToPFLowRankMomentFourBandedCofactorJ012_of_j12`
- `kernelContigToPFLowRankMomentFourBandedCofactorJ12_of_j2`
- `kernelContigToPFLowRankMomentFourBandedCofactorJ2_of_supportSplitOnly`
- `kernelContigToPFLowRankMomentFourBandedCofactorSupportSplitOnly_of_caseTable`
- `kernelContigToPFLowRankMomentFourBandedCofactorCaseTable_of_nonzeroCaseTable`
- `kernelContigToPFLowRankMomentFourBandedCofactorNonzeroCaseTable_of_survivorSplit`
- `kernelContigToPFLowRankMomentFourBandedCofactorSurvivorSplit_of_oneSurvivorPosition`
- `kernelContigToPFLowRankMomentFourBandedCofactorOneSurvivorPosition_of_positiveOneSurvivor`
- `kernelContigToPFLowRankMomentFourBandedCofactorPositiveOneSurvivor_of_support`
- `xiToeplitzTotalPositive_of_kernelContigToPF`
- `xiToeplitzTotalPositive_of_kernelContigToPFGeThree`
- `xiToeplitzTotalPositive_of_kernelContigToPFThreeAndGeFour`
- `xiToeplitzTotalPositive_of_kernelContigToPFThreeSupportSplit`
- `xiToeplitzTotalPositive_of_kernelContigToPFThreeBandedSupport`
- `xiToeplitzTotalPositive_of_kernelContigToPFThreeBandedDet`
- `xiToeplitzTotalPositive_of_kernelContigToPFThreeBandedExpanded`
- `xiToeplitzTotalPositive_of_kernelContigToPFThreeMiddleMoment`
- `xiToeplitzTotalPositive_of_kernelContigToPFThreeZeroEdges`
- `xiToeplitzTotalPositive_of_kernelContigToPFThreeSimplifiedZeroEdges`
- `xiToeplitzTotalPositive_of_kernelContigToPFThreeBracketZeroEdges`
- `xiToeplitzTotalPositive_of_kernelContigToPFThreeKernelZeroEdges`
- `xiToeplitzTotalPositive_of_kernelContigToPFThreeCompoundRatio`
- `xiToeplitzTotalPositive_of_kernelContigToPFThreeMomentCompoundRatio`
- `xiToeplitzTotalPositive_of_kernelContigToPFThreeMomentPayload`
- `xiToeplitzTotalPositive_of_kernelContigToPFThreeMomentPayloadFourAndGeFive`
- `xiToeplitzTotalPositive_of_kernelContigToPFThreeMomentPayloadFourSupportSplit`
- `xiToeplitzTotalPositive_of_kernelContigToPFThreeMomentPayloadFourMomentSupportSplit`
- `xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourMixed`
- `xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedMixed`
- `xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedDet`
- `xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedUpperRightZero`
- `xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedRowZeroCofactor`
- `xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedThreeCofactor`
- `xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedNamedCofactor`
- `xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedCofactorRowCol`
- `xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedCofactorSupportSplit`
- `xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedCofactorJ012`
- `xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedCofactorJ12`
- `xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedCofactorJ2`
- `xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedCofactorSupportSplitOnly`
- `xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedCofactorCaseTable`
- `xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedCofactorNonzeroCaseTable`
- `xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedCofactorSurvivorSplit`
- `xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedCofactorOneSurvivorPosition`
- `xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedCofactorPositiveOneSurvivor`
- `xiToeplitzTotalPositive_of_kernelContigToPFCofactorPositiveSupport`
- `xiToeplitzTotalPositive_of_kernelContigToPFCofactorPositiveFull`
- `xiToeplitzTotalPositive_of_kernelContigToPFCofactorPositiveFullDet`
- `xiToeplitzTotalPositive_of_kernelContigToPFCofactorThreeFull`
- `xiToeplitzTotalPositive_of_kernelContigToPFCofactorThreeFullBanded`
- `xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1Nonpos`
- `xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1SupportSplit`
- `xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1FullMoment`
- `xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1FullMomentZero`
- `xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1BandedExpanded`
- `xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1BandedProduct`
- `xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1BandedSigns`
- `xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1BandedSplit`
- `xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1BandedTopSupport`
- `xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1BandedTopMoment`
- `xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1BandedTopMomentMiddle`
- `riemannHypothesis_of_kernelContigToPF`
- `riemannHypothesis_of_kernelContigToPFGeThree`
- `riemannHypothesis_of_kernelContigToPFThreeAndGeFour`
- `riemannHypothesis_of_kernelContigToPFThreeSupportSplit`
- `riemannHypothesis_of_kernelContigToPFThreeBandedSupport`
- `riemannHypothesis_of_kernelContigToPFThreeBandedDet`
- `riemannHypothesis_of_kernelContigToPFThreeBandedExpanded`
- `riemannHypothesis_of_kernelContigToPFThreeMiddleMoment`
- `riemannHypothesis_of_kernelContigToPFThreeZeroEdges`
- `riemannHypothesis_of_kernelContigToPFThreeSimplifiedZeroEdges`
- `riemannHypothesis_of_kernelContigToPFThreeBracketZeroEdges`
- `riemannHypothesis_of_kernelContigToPFThreeKernelZeroEdges`
- `riemannHypothesis_of_kernelContigToPFThreeCompoundRatio`
- `riemannHypothesis_of_kernelContigToPFThreeMomentCompoundRatio`
- `riemannHypothesis_of_kernelContigToPFThreeMomentPayload`
- `riemannHypothesis_of_kernelContigToPFThreeMomentPayloadFourAndGeFive`
- `riemannHypothesis_of_kernelContigToPFThreeMomentPayloadFourSupportSplit`
- `riemannHypothesis_of_kernelContigToPFThreeMomentPayloadFourMomentSupportSplit`
- `riemannHypothesis_of_kernelContigToPFLowRankMomentFourMixed`
- `riemannHypothesis_of_kernelContigToPFLowRankMomentFourBandedMixed`
- `riemannHypothesis_of_kernelContigToPFLowRankMomentFourBandedDet`
- `riemannHypothesis_of_kernelContigToPFLowRankMomentFourBandedUpperRightZero`
- `riemannHypothesis_of_kernelContigToPFLowRankMomentFourBandedRowZeroCofactor`
- `riemannHypothesis_of_kernelContigToPFLowRankMomentFourBandedThreeCofactor`
- `riemannHypothesis_of_kernelContigToPFLowRankMomentFourBandedNamedCofactor`
- `riemannHypothesis_of_kernelContigToPFLowRankMomentFourBandedCofactorRowCol`
- `riemannHypothesis_of_kernelContigToPFLowRankMomentFourBandedCofactorSupportSplit`
- `riemannHypothesis_of_kernelContigToPFLowRankMomentFourBandedCofactorJ012`
- `riemannHypothesis_of_kernelContigToPFLowRankMomentFourBandedCofactorJ12`
- `riemannHypothesis_of_kernelContigToPFLowRankMomentFourBandedCofactorJ2`
- `riemannHypothesis_of_kernelContigToPFLowRankMomentFourBandedCofactorSupportSplitOnly`
- `riemannHypothesis_of_kernelContigToPFLowRankMomentFourBandedCofactorCaseTable`
- `riemannHypothesis_of_kernelContigToPFLowRankMomentFourBandedCofactorNonzeroCaseTable`
- `riemannHypothesis_of_kernelContigToPFLowRankMomentFourBandedCofactorSurvivorSplit`
- `riemannHypothesis_of_kernelContigToPFLowRankMomentFourBandedCofactorOneSurvivorPosition`
- `riemannHypothesis_of_kernelContigToPFLowRankMomentFourBandedCofactorPositiveOneSurvivor`
- `riemannHypothesis_of_kernelContigToPFCofactorPositiveSupport`

Mathematical meaning:

This is the next named wall.  If we prove all contiguous kernel determinants,
we still need a theorem upgrading that structured positivity to arbitrary
Toeplitz minors:

```text
XiContigToeplitzTotalPositive -> XiToeplitzTotalPositive
```

For arbitrary sequences this should not be assumed.  The only honest version is
an xi-specific theorem, probably using additional structure from Polya's kernel,
factorial weighting, a planar network model, or a variation-diminishing operator.

The bridge now has a local equivalent:

```text
XiArbitraryMinorReductionToContig
```

This says that every arbitrary Toeplitz minor has a proof of nonnegativity from
the contiguous-minor ladder.  It is the right loop target because it can be
attacked one row/column pattern at a time.  A future proof could come from:

- a Cauchy-Binet factorization into contiguous blocks;
- a planar-network path matrix whose Lindstrom-Gessel-Viennot determinant is the
  target minor;
- a variation-diminishing operator that upgrades interval minors to arbitrary
  minors for this specific xi coefficient sequence.

The bridge now also has a certificate layer:

```text
XiAllMinorContigCertificates -> XiArbitraryMinorReductionToContig
```

Each `XiMinorContigCertificate k rows cols hRows hCols` is a local proof object
for one arbitrary minor.  This is the next practical loop: build certificates
for concrete row/column patterns, detect the common algebraic shape, and then
generalize to all strictly monotone patterns.

The certificate program now has a verified base case:

```text
xiContiguousMinorSelfCertificate
```

For row pattern `rows i = m + i` and column pattern `cols j = j`, the certificate
is immediate from `XiContigToeplitzTotalPositive`.  This does not solve the
arbitrary-minor upgrade.  It marks the boundary: contiguous interval patterns
are solved by definition, and the next certificates must handle non-contiguous
row or column gaps.

The program now also has a verified arbitrary `1 x 1` certificate:

```text
xiMinorOneContigCertificate
```

For any single row and single column, either the Toeplitz entry is zero because
the column lies above the lower-triangular support, or it is the contiguous
`1 x 1` minor at offset `row - col`.  This closes the full arbitrary-minor
certificate problem in size `1`.  The next real certificate family is size `2`
with non-contiguous row or column gaps.

The program also has an arbitrary-size zero-support certificate:

```text
xiZeroSupportMinorCertificate
```

If every selected column lies strictly above every selected row, then every
entry in the lower-triangular Toeplitz submatrix is zero, so the determinant is
zero.  This closes the completely unsupported arbitrary-minor family.  The next
frontier is therefore the mixed-support case: non-contiguous `2 x 2` minors
where at least one entry is nonzero but the pattern is not a contiguous block.

This has been strengthened to a zero-row certificate:

```text
xiZeroRowMinorCertificate
```

If even one selected row lies strictly below every selected column, that row is
zero and the determinant is zero.  This closes a larger arbitrary-size family
than the all-zero-support case.  The next frontier is mixed-support minors with
no zero row, starting at non-contiguous `2 x 2` patterns.

The symmetric zero-column family is also verified:

```text
xiZeroColumnMinorCertificate
```

If one selected column lies strictly above every selected row, that column is
zero and the determinant is zero.  The remaining certificate frontier is now
mixed-support minors with no zero row and no zero column, starting at
non-contiguous `2 x 2` patterns.

The first mixed-support `2 x 2` family is now verified:

```text
xiMinorTwoUpperRightZeroCertificate
```

The auxiliary lemma `xiToeplitzEntry_nonneg_of_contig` proves every individual
Toeplitz entry is nonnegative from the contiguous `1 x 1` ladder.  Therefore,
if the upper-right entry of a `2 x 2` minor is zero, the determinant reduces to
the product of the two diagonal entries and is nonnegative.

The remaining `2 x 2` frontier is the genuinely full-support case where all
four selected Toeplitz entries are nonzero and the pattern is not a contiguous
block.  That is where a real variation-diminishing, planar-network, or
Cauchy-Binet certificate must enter.

That frontier is now named:

```text
XiMinorTwoFullSupportFromContig
```

It states that for every full-support `2 x 2` arbitrary Toeplitz minor,
contiguous positivity implies determinant nonnegativity.  Lean verifies that
this condition supplies local certificates via:

```text
xiMinorTwoFullSupportCertificate
```

So the loop has reduced the remaining `2 x 2` frontier to one exact theorem
target.  The next push is to prove or further decompose
`XiMinorTwoFullSupportFromContig`.

The determinant target is now decomposed into an explicit four-index inequality:

```text
XiMinorTwoGapInequalityFromContig
```

For rows `r0 < r1` and columns `c0 < c1` with full lower-triangular support
`c1 <= r0`, it asks for:

```text
XiMomentCoeff (r0 - c1) * XiMomentCoeff (r1 - c0)
  <= XiMomentCoeff (r0 - c0) * XiMomentCoeff (r1 - c1)
```

Lean verifies:

```text
XiMinorTwoGapInequalityFromContig -> XiMinorTwoFullSupportFromContig
```

This is now the sharp algebraic `2 x 2` condition to prove or decompose next.

The four-index inequality is now reduced to a sequence-level ratio-Monge target:

```text
XiMomentRatioMongeFromContig
```

For every `a <= b` and positive gap `d`, it asks:

```text
XiMomentCoeff a * XiMomentCoeff (b + d)
  <= XiMomentCoeff (a + d) * XiMomentCoeff b
```

This is the no-division version of saying the ratio
`XiMomentCoeff (n + d) / XiMomentCoeff n` decreases with `n`.  Lean verifies:

```text
XiMomentRatioMongeFromContig -> XiMinorTwoGapInequalityFromContig
```

The next proof attempt should attack this ratio-Monge property directly, or
decompose it into adjacent ratio monotonicity plus positivity.

That adjacent decomposition is now named:

```text
XiMomentAdjacentRatioMongeFromContig
XiAdjacentRatioToGlobalRatioBridge
```

The adjacent condition asks only for:

```text
XiMomentCoeff n * XiMomentCoeff (n + 1 + d)
  <= XiMomentCoeff (n + d) * XiMomentCoeff (n + 1)
```

for every `n` and positive gap `d`.  The propagation bridge is separated because
turning adjacent cross-multiplied inequalities into the global ratio-Monge
statement needs positivity/control of intermediate coefficients.  Lean verifies:

```text
XiAdjacentRatioRoute -> XiMomentRatioMongeFromContig
```

The next proof attempt should either prove the adjacent inequality from the
contiguous ladder or prove the propagation bridge from entry positivity plus
adjacent inequality.

The unit-gap adjacent inequality is now solved:

```text
xiMomentUnitRatioMonge_of_contig
```

It is exactly the contiguous `2 x 2` Toeplitz/Turan rung:

```text
XiMomentCoeff n * XiMomentCoeff (n + 2)
  <= XiMomentCoeff (n + 1) * XiMomentCoeff (n + 1)
```

The next bridge is now named:

```text
XiUnitRatioToAdjacentRatioBridge
```

It asks for the propagation from the proved unit-gap inequality to arbitrary
positive gap `d` in the adjacent condition.  Lean verifies:

```text
XiUnitRatioRoute -> XiMomentAdjacentRatioMongeFromContig
```

So the sequence-theoretic frontier has moved from proving the base Turan
inequality to proving that unit-gap ratio monotonicity propagates across longer
gaps.

The propagation bridge is now refined to include the positivity actually needed
for chaining:

```text
XiMomentCoeffNonnegativeFromContig
XiUnitRatioToAdjacentRatioWithPositivityBridge
```

Lean proves `XiMomentCoeffNonnegativeFromContig` from contiguous `1 x 1`
minors via:

```text
xiMomentCoeffNonnegative_of_contig
```

and verifies:

```text
XiUnitRatioToAdjacentRatioWithPositivityBridge
  -> XiUnitRatioToAdjacentRatioBridge
```

So the next target is now sharper: prove that nonnegative coefficients plus the
unit-gap Turan/log-concavity inequality propagate to arbitrary positive gaps in
the adjacent-ratio inequality.

There is also a stricter kernel-backed route:

```text
XiMomentCoeffPositive
xiMomentCoeffPositive_of_kernelRep
XiUnitRatioToAdjacentRatioWithStrictPositivityBridge
```

Pólya's positive-kernel representation supplies strict positivity of all signed
moment coefficients.  Lean verifies:

```text
XiMomentKernelRep
  -> XiUnitRatioToAdjacentRatioWithStrictPositivityBridge
  -> XiUnitRatioToAdjacentRatioBridge
```

This strict-positivity route is now solved at the sequence-algebra level.

The propagation target has now been decomposed one more level into fixed-gap
induction:

```text
XiMomentAdjacentRatioGap d
XiMomentAdjacentRatioGapSuccBridge
```

Lean verifies the base case:

```text
xiMomentAdjacentRatioGap_one_of_contig : XiMomentAdjacentRatioGap 1
```

and also verifies the algebraic cancellation step:

```text
two_step_ratio_cancel
```

This lemma says that from

```text
A * B <= C * D
C * E <= B * B
0 <= A, 0 <= B, 0 < C
```

one may conclude:

```text
A * E <= B * D
```

That cancellation closes the gap-successor theorem under strict positivity:

```text
xiMomentAdjacentRatioGapSuccBridge_of_strictPositivity
```

Consequently Lean now verifies:

```text
XiMomentKernelRep -> XiMomentAdjacentRatioMongeFromContig
```

via:

```text
xiMomentAdjacentRatioMonge_of_kernelRep
```

The next bridge was:

```text
XiAdjacentRatioToGlobalRatioBridge
```

That bridge is now also solved under strict positivity.  The proof introduces a
distance-indexed form:

```text
XiMomentRatioDistanceFromAdjacent k
```

and proves:

```text
xiMomentRatioDistance_zero
xiMomentRatioDistance_succ_of_adjacent_strictPositivity
xiMomentRatioMonge_of_adjacentRatio_strictPositivity
```

The algebraic engine is the more general no-division cancellation lemma:

```text
two_step_ratio_cancel_general
```

Consequently Lean now verifies:

```text
XiMomentKernelRep -> XiMomentRatioMongeFromContig
```

via:

```text
xiMomentRatioMonge_of_kernelRep
```

and therefore also verifies the explicit four-index full-support `2 x 2`
inequality:

```text
XiMomentKernelRep -> XiMinorTwoGapInequalityFromContig
```

via:

```text
xiMinorTwoGapInequalityFromContig_of_kernelRep
```

The determinant-form full-support `2 x 2` target is then immediate:

```text
XiMomentKernelRep -> XiMinorTwoFullSupportFromContig
```

via:

```text
xiMinorTwoFullSupportFromContig_of_kernelRep
```

The `2 x 2` full-support certificate frontier is no longer the main obstacle
once `XiMomentKernelRep` is available.  The next honest frontier is the general
arbitrary-minor upgrade for sizes `k >= 3`: find a certificate family or
structure theorem that turns contiguous positivity plus the xi kernel
representation into all arbitrary Toeplitz minors.

That frontier is now named directly:

```text
XiAllMinorGeThreeContigCertificates
```

Lean verifies the low-size closure:

```text
exists_xiMinorZeroContigCertificate
exists_xiMinorOneContigCertificate
exists_xiMinorTwoContigCertificate_of_kernelRep
```

and therefore verifies:

```text
XiMomentKernelRep
  -> XiAllMinorGeThreeContigCertificates
  -> XiAllMinorContigCertificates
```

via:

```text
xiAllMinorContigCertificates_of_kernelRep_and_geThree
```

This plugs into the full PF bridge:

```text
XiMomentKernelRep
  -> XiAllMinorGeThreeContigCertificates
  -> XiContigToFullPFBridge
```

via:

```text
xiContigToFullPFBridge_of_kernelRep_and_geThree
```

The sharper RH-closing bundled target is now:

```text
KernelContigToPFGeThreeTheorem
```

It asks for:

1. Pólya kernel representation with positive kernel moments;
2. all contiguous kernel Toeplitz determinants;
3. arbitrary-minor certificates only for sizes `k >= 3`.

Lean verifies:

```text
KernelContigToPFGeThreeTheorem -> XiToeplitzTotalPositive
KernelContigToPFGeThreeTheorem -> RiemannHypothesis
```

via:

```text
xiToeplitzTotalPositive_of_kernelContigToPFGeThree
riemannHypothesis_of_kernelContigToPFGeThree
```

The `k >= 3` frontier has now been split into the first concrete unsolved rung
and the remaining tail:

```text
XiMinorThreeContigCertificates
XiAllMinorGeFourContigCertificates
```

Lean verifies:

```text
XiMinorThreeContigCertificates
  -> XiAllMinorGeFourContigCertificates
  -> XiAllMinorGeThreeContigCertificates
```

via:

```text
xiAllMinorGeThree_of_three_and_geFour
```

and therefore verifies the sharper bridge:

```text
XiMomentKernelRep
  -> XiMinorThreeContigCertificates
  -> XiAllMinorGeFourContigCertificates
  -> XiContigToFullPFBridge
```

via:

```text
xiContigToFullPFBridge_of_kernelRep_three_and_geFour
```

The newest RH-closing bundle is:

```text
KernelContigToPFThreeAndGeFourTheorem
```

Lean verifies:

```text
KernelContigToPFThreeAndGeFourTheorem -> XiToeplitzTotalPositive
KernelContigToPFThreeAndGeFourTheorem -> RiemannHypothesis
```

via:

```text
xiToeplitzTotalPositive_of_kernelContigToPFThreeAndGeFour
riemannHypothesis_of_kernelContigToPFThreeAndGeFour
```

The `3 x 3` rung is now split by support:

```text
XiMinorThreeFullSupportFromContig
XiMinorThreeMixedSupportCertificates
```

The full-support condition handles the genuinely dense `3 x 3` determinant
where every selected Toeplitz entry lies inside lower-triangular support.  The
mixed-support condition covers patterns with no zero row/column but not full
support; these likely need sparse expansion, block-triangular, planar-network,
or Cauchy-Binet certificates.

Lean verifies:

```text
XiMinorThreeFullSupportFromContig
  -> XiMinorThreeMixedSupportCertificates
  -> XiMinorThreeContigCertificates
```

via:

```text
xiMinorThreeContigCertificates_of_full_and_mixed
```

and verifies the sharper PF/RH route:

```text
XiMomentKernelRep
  -> XiMinorThreeFullSupportFromContig
  -> XiMinorThreeMixedSupportCertificates
  -> XiAllMinorGeFourContigCertificates
  -> XiContigToFullPFBridge
```

via:

```text
xiContigToFullPFBridge_of_kernelRep_threeFullMixed_and_geFour
```

The newest RH-closing bundle is:

```text
KernelContigToPFThreeSupportSplitTheorem
```

Lean verifies:

```text
KernelContigToPFThreeSupportSplitTheorem -> XiToeplitzTotalPositive
KernelContigToPFThreeSupportSplitTheorem -> RiemannHypothesis
```

via:

```text
xiToeplitzTotalPositive_of_kernelContigToPFThreeSupportSplit
riemannHypothesis_of_kernelContigToPFThreeSupportSplit
```

The active loop target is now to attack these two `3 x 3` conditions separately,
starting with `XiMinorThreeMixedSupportCertificates` if sparse support
classification is easier, or `XiMinorThreeFullSupportFromContig` if the
determinant inequality can be reduced to a higher-order Monge/log-concavity
condition.  The tail condition `XiAllMinorGeFour...` keeps the full RH route
honest while the first remaining `3 x 3` support class is attacked.

The sparse mixed-support condition has now been sharpened to the exact monotone
support band:

```text
XiMinorThreeBandedMixedSupportCertificates
```

For strictly monotone rows and columns, mixed support with no zero row or zero
column is equivalent to the band inequalities:

```text
cols 0 <= rows 0
rows 0 < cols 2
cols 2 <= rows 2
```

Lean verifies:

```text
XiMinorThreeBandedMixedSupportCertificates
  -> XiMinorThreeMixedSupportCertificates
```

via:

```text
xiMinorThreeMixedSupportCertificates_of_banded
```

and therefore verifies the sharper PF/RH route:

```text
XiMomentKernelRep
  -> XiMinorThreeFullSupportFromContig
  -> XiMinorThreeBandedMixedSupportCertificates
  -> XiAllMinorGeFourContigCertificates
  -> XiContigToFullPFBridge
```

via:

```text
xiContigToFullPFBridge_of_kernelRep_threeFullBandedMixed_and_geFour
```

The newest RH-closing bundle is:

```text
KernelContigToPFThreeBandedSupportTheorem
```

Lean verifies:

```text
KernelContigToPFThreeBandedSupportTheorem -> XiToeplitzTotalPositive
KernelContigToPFThreeBandedSupportTheorem -> RiemannHypothesis
```

via:

```text
xiToeplitzTotalPositive_of_kernelContigToPFThreeBandedSupport
riemannHypothesis_of_kernelContigToPFThreeBandedSupport
```

The active sparse target is now the banded determinant/certificate condition.
This is a smaller object than arbitrary mixed support and should be attacked by
expanding the determinant along the forced zero pattern or by constructing a
planar-network/Cauchy-Binet certificate for exactly that band.

The banded certificate condition has now been reduced to a raw determinant
inequality:

```text
XiMinorThreeBandedDetInequalityFromContig
```

It states determinant nonnegativity for every monotone `3 x 3` pattern with:

```text
cols 0 <= rows 0
rows 0 < cols 2
cols 2 <= rows 2
```

Lean verifies:

```text
XiMinorThreeBandedDetInequalityFromContig
  -> XiMinorThreeBandedMixedSupportCertificates
```

via:

```text
xiMinorThreeBandedMixedSupportCertificates_of_detInequality
```

and therefore verifies the sharper PF/RH route:

```text
XiMomentKernelRep
  -> XiMinorThreeFullSupportFromContig
  -> XiMinorThreeBandedDetInequalityFromContig
  -> XiAllMinorGeFourContigCertificates
  -> XiContigToFullPFBridge
```

via:

```text
xiContigToFullPFBridge_of_kernelRep_threeFullBandedDet_and_geFour
```

The newest RH-closing bundle is:

```text
KernelContigToPFThreeBandedDetTheorem
```

Lean verifies:

```text
KernelContigToPFThreeBandedDetTheorem -> XiToeplitzTotalPositive
KernelContigToPFThreeBandedDetTheorem -> RiemannHypothesis
```

via:

```text
xiToeplitzTotalPositive_of_kernelContigToPFThreeBandedDet
riemannHypothesis_of_kernelContigToPFThreeBandedDet
```

The next sparse move is to expand this determinant using
`Matrix.det_fin_three`, rewrite the forced upper-right entry as zero, and name
the resulting moment inequality.

That determinant expansion is now named:

```text
XiMinorThreeBandedExpandedInequalityFromContig
```

It is the four-term sparse expression:

```text
T00 * (T11 * T22 - T12 * T21)
  - T01 * (T10 * T22 - T12 * T20)
```

where `Tab = XiToeplitzEntry (rows a) (cols b)` and the forced entry
`T02 = 0` has been eliminated.  Lean verifies:

```text
XiMinorThreeBandedExpandedInequalityFromContig
  -> XiMinorThreeBandedDetInequalityFromContig
```

via:

```text
xiMinorThreeBandedDetInequality_of_expanded
```

and therefore verifies the sharper PF/RH route:

```text
XiMomentKernelRep
  -> XiMinorThreeFullSupportFromContig
  -> XiMinorThreeBandedExpandedInequalityFromContig
  -> XiAllMinorGeFourContigCertificates
  -> XiContigToFullPFBridge
```

via:

```text
xiContigToFullPFBridge_of_kernelRep_threeFullBandedExpanded_and_geFour
```

The newest RH-closing bundle is:

```text
KernelContigToPFThreeBandedExpandedTheorem
```

Lean verifies:

```text
KernelContigToPFThreeBandedExpandedTheorem -> XiToeplitzTotalPositive
KernelContigToPFThreeBandedExpandedTheorem -> RiemannHypothesis
```

via:

```text
xiToeplitzTotalPositive_of_kernelContigToPFThreeBandedExpanded
riemannHypothesis_of_kernelContigToPFThreeBandedExpanded
```

The moment-index rewrite needs one more support split.  The band condition
does not guarantee all six surviving `Tab` terms are supported; `T01` or `T12`
may still be zero.  The valid dense subcase is now named:

```text
XiMinorThreeBandedMiddleMomentInequalityFromContig
```

It adds the middle-support assumptions:

```text
cols 1 <= rows 0
cols 2 <= rows 1
```

and rewrites every surviving `Tab` into an explicit `XiMomentCoeff` gap.  Lean
verifies this rewrite on the middle-supported band:

```text
xiMinorThreeBandedExpandedInequality_of_middleMoment
```

The remaining band edge cases are kept honest as a separate target:

```text
XiMinorThreeBandedEdgeCaseCertificates
```

Lean verifies:

```text
XiMinorThreeBandedMiddleMomentInequalityFromContig
  -> XiMinorThreeBandedEdgeCaseCertificates
  -> XiMinorThreeBandedExpandedInequalityFromContig
```

via:

```text
xiMinorThreeBandedExpandedInequality_of_middleMoment_and_edgeCases
```

and therefore verifies the sharper PF/RH route:

```text
XiMomentKernelRep
  -> XiMinorThreeFullSupportFromContig
  -> XiMinorThreeBandedMiddleMomentInequalityFromContig
  -> XiMinorThreeBandedEdgeCaseCertificates
  -> XiAllMinorGeFourContigCertificates
  -> XiContigToFullPFBridge
```

via:

```text
xiContigToFullPFBridge_of_kernelRep_threeFullMiddleMoment_and_edgeCases_geFour
```

The newest RH-closing bundle is:

```text
KernelContigToPFThreeMiddleMomentTheorem
```

Lean verifies:

```text
KernelContigToPFThreeMiddleMomentTheorem -> XiToeplitzTotalPositive
KernelContigToPFThreeMiddleMomentTheorem -> RiemannHypothesis
```

via:

```text
xiToeplitzTotalPositive_of_kernelContigToPFThreeMiddleMoment
riemannHypothesis_of_kernelContigToPFThreeMiddleMoment
```

The next loop should either prove the middle-supported moment inequality from
higher-order Monge/TP structure, or decompose the remaining band edge cases
where `T01 = 0` or `T12 = 0`.

The band edge cases are now split into the two concrete missing-entry targets:

```text
XiMinorThreeBandedT01ZeroInequalityFromContig
XiMinorThreeBandedT12ZeroInequalityFromContig
```

They cover:

```text
T01 = 0  <=>  rows 0 < cols 1
T12 = 0  <=>  rows 1 < cols 2
```

Lean verifies:

```text
XiMinorThreeBandedMiddleMomentInequalityFromContig
  -> XiMinorThreeBandedT01ZeroInequalityFromContig
  -> XiMinorThreeBandedT12ZeroInequalityFromContig
  -> XiMinorThreeBandedExpandedInequalityFromContig
```

via:

```text
xiMinorThreeBandedExpandedInequality_of_middleMoment_and_zeroEdges
```

and packages the two zero-edge targets into the older edge-case bridge via:

```text
xiMinorThreeBandedEdgeCaseCertificates_of_zeroEdges
```

The sharper PF/RH route is now:

```text
XiMomentKernelRep
  -> XiMinorThreeFullSupportFromContig
  -> XiMinorThreeBandedMiddleMomentInequalityFromContig
  -> XiMinorThreeBandedT01ZeroInequalityFromContig
  -> XiMinorThreeBandedT12ZeroInequalityFromContig
  -> XiAllMinorGeFourContigCertificates
  -> XiContigToFullPFBridge
```

via:

```text
xiContigToFullPFBridge_of_kernelRep_threeFullMiddleMoment_zeroEdges_geFour
```

The newest RH-closing bundle is:

```text
KernelContigToPFThreeZeroEdgesTheorem
```

Lean verifies:

```text
KernelContigToPFThreeZeroEdgesTheorem -> XiToeplitzTotalPositive
KernelContigToPFThreeZeroEdgesTheorem -> RiemannHypothesis
```

via:

```text
xiToeplitzTotalPositive_of_kernelContigToPFThreeZeroEdges
riemannHypothesis_of_kernelContigToPFThreeZeroEdges
```

The next sparse loop should expand each zero-edge determinant.  In the `T01=0`
case the expression loses the second large term.  In the `T12=0` case both
negative inner products involving `T12` vanish, leaving a simpler two-product
difference.

Those simplified zero-edge targets are now named:

```text
XiMinorThreeBandedT01ZeroSimplifiedFromContig
XiMinorThreeBandedT12ZeroSimplifiedFromContig
```

Lean verifies:

```text
XiMinorThreeBandedT01ZeroSimplifiedFromContig
  -> XiMinorThreeBandedT01ZeroInequalityFromContig
XiMinorThreeBandedT12ZeroSimplifiedFromContig
  -> XiMinorThreeBandedT12ZeroInequalityFromContig
```

via:

```text
xiMinorThreeBandedT01ZeroInequality_of_simplified
xiMinorThreeBandedT12ZeroInequality_of_simplified
```

The sharper RH route is now:

```text
XiMomentKernelRep
  -> XiMinorThreeFullSupportFromContig
  -> XiMinorThreeBandedMiddleMomentInequalityFromContig
  -> XiMinorThreeBandedT01ZeroSimplifiedFromContig
  -> XiMinorThreeBandedT12ZeroSimplifiedFromContig
  -> XiAllMinorGeFourContigCertificates
  -> XiContigToFullPFBridge
```

via:

```text
xiContigToFullPFBridge_of_kernelRep_threeFullMiddleMoment_simplifiedZeroEdges_geFour
```

The newest RH-closing bundle is:

```text
KernelContigToPFThreeSimplifiedZeroEdgesTheorem
```

Lean verifies:

```text
KernelContigToPFThreeSimplifiedZeroEdgesTheorem -> XiToeplitzTotalPositive
KernelContigToPFThreeSimplifiedZeroEdgesTheorem -> RiemannHypothesis
```

via:

```text
xiToeplitzTotalPositive_of_kernelContigToPFThreeSimplifiedZeroEdges
riemannHypothesis_of_kernelContigToPFThreeSimplifiedZeroEdges
```

The simplified zero-edge targets have now been reduced one more step.  In the
`T01 = 0` case, contiguous `1 x 1` positivity gives nonnegativity of `T00`, so
it is enough to prove the remaining lower-right `2 x 2` bracket.  In the
`T12 = 0` case, contiguous `1 x 1` positivity gives nonnegativity of `T22`, so
it is enough to prove the remaining upper-left `2 x 2` bracket.

Those bracket targets are now named:

```text
XiMinorThreeBandedT01ZeroBracketFromContig
XiMinorThreeBandedT12ZeroBracketFromContig
```

Lean verifies:

```text
XiMinorThreeBandedT01ZeroBracketFromContig
  -> XiMinorThreeBandedT01ZeroSimplifiedFromContig
XiMinorThreeBandedT12ZeroBracketFromContig
  -> XiMinorThreeBandedT12ZeroSimplifiedFromContig
```

via:

```text
xiMinorThreeBandedT01ZeroSimplified_of_bracket
xiMinorThreeBandedT12ZeroSimplified_of_bracket
```

The sharpest RH route currently checked in Lean is:

```text
XiMomentKernelRep
  -> XiMinorThreeFullSupportFromContig
  -> XiMinorThreeBandedMiddleMomentInequalityFromContig
  -> XiMinorThreeBandedT01ZeroBracketFromContig
  -> XiMinorThreeBandedT12ZeroBracketFromContig
  -> XiAllMinorGeFourContigCertificates
  -> XiContigToFullPFBridge
```

via:

```text
xiContigToFullPFBridge_of_kernelRep_threeFullMiddleMoment_bracketZeroEdges_geFour
```

The newest RH-closing bundle is:

```text
KernelContigToPFThreeBracketZeroEdgesTheorem
```

Lean verifies:

```text
KernelContigToPFThreeBracketZeroEdgesTheorem -> XiToeplitzTotalPositive
KernelContigToPFThreeBracketZeroEdgesTheorem -> RiemannHypothesis
```

via:

```text
xiToeplitzTotalPositive_of_kernelContigToPFThreeBracketZeroEdges
riemannHypothesis_of_kernelContigToPFThreeBracketZeroEdges
```

These two bracket targets are now closed by the existing `2 x 2` route.  The
`T12 = 0` bracket is directly the upper-left full-support `2 x 2` minor.  The
`T01 = 0` bracket splits into three support cases: a vanished first row, a
nonnegative diagonal product, or a lower-right full-support `2 x 2` minor.

Lean verifies:

```text
XiMinorTwoFullSupportFromContig
  -> XiMinorThreeBandedT01ZeroBracketFromContig
XiMinorTwoFullSupportFromContig
  -> XiMinorThreeBandedT12ZeroBracketFromContig
```

via:

```text
xiMinorThreeBandedT01ZeroBracket_of_twoFullSupport
xiMinorThreeBandedT12ZeroBracket_of_twoFullSupport
```

Since `XiMomentKernelRep` already implies `XiMinorTwoFullSupportFromContig`,
Lean also verifies:

```text
XiMomentKernelRep
  -> XiMinorThreeBandedT01ZeroBracketFromContig
XiMomentKernelRep
  -> XiMinorThreeBandedT12ZeroBracketFromContig
```

via:

```text
xiMinorThreeBandedT01ZeroBracket_of_kernelRep
xiMinorThreeBandedT12ZeroBracket_of_kernelRep
```

The sharpest RH route currently checked in Lean is therefore:

```text
XiMomentKernelRep
  -> XiMinorThreeFullSupportFromContig
  -> XiMinorThreeBandedMiddleMomentInequalityFromContig
  -> XiAllMinorGeFourContigCertificates
  -> XiContigToFullPFBridge
```

via:

```text
xiContigToFullPFBridge_of_kernelRep_threeFullMiddleMoment_geFour
```

The newest RH-closing bundle is:

```text
KernelContigToPFThreeKernelZeroEdgesTheorem
```

Lean verifies:

```text
KernelContigToPFThreeKernelZeroEdgesTheorem -> XiToeplitzTotalPositive
KernelContigToPFThreeKernelZeroEdgesTheorem -> RiemannHypothesis
```

via:

```text
xiToeplitzTotalPositive_of_kernelContigToPFThreeKernelZeroEdges
riemannHypothesis_of_kernelContigToPFThreeKernelZeroEdges
```

The next loop should now focus on the remaining true payloads:

1. prove `XiMinorThreeFullSupportFromContig`;
2. prove `XiMinorThreeBandedMiddleMomentInequalityFromContig`;
3. prove or recursively reduce `XiAllMinorGeFourContigCertificates`.

The middle-supported moment inequality has now been sharpened to a compound
ratio condition.  The raw middle expression has the form:

```text
A * B - C * D >= 0
```

where `B` and `D` are adjacent `2 x 2` moment brackets.  Instead of treating
this as an opaque `3 x 3` expansion, the next named condition asks for the
cross-product inequality:

```text
C * D <= A * B
```

This is now named:

```text
XiMinorThreeBandedMiddleCompoundRatioFromContig
```

Lean verifies:

```text
XiMinorThreeBandedMiddleCompoundRatioFromContig
  -> XiMinorThreeBandedMiddleMomentInequalityFromContig
```

via:

```text
xiMinorThreeBandedMiddleMoment_of_compoundRatio
```

The sharpest RH route currently checked in Lean is now:

```text
XiMomentKernelRep
  -> XiMinorThreeFullSupportFromContig
  -> XiMinorThreeBandedMiddleCompoundRatioFromContig
  -> XiAllMinorGeFourContigCertificates
  -> XiContigToFullPFBridge
```

The newest RH-closing bundle is:

```text
KernelContigToPFThreeCompoundRatioTheorem
```

Lean verifies:

```text
KernelContigToPFThreeCompoundRatioTheorem -> XiToeplitzTotalPositive
KernelContigToPFThreeCompoundRatioTheorem -> RiemannHypothesis
```

via:

```text
xiToeplitzTotalPositive_of_kernelContigToPFThreeCompoundRatio
riemannHypothesis_of_kernelContigToPFThreeCompoundRatio
```

The next loop should try to prove this compound-ratio condition using total
positivity of the second compound matrix, a planar-network interpretation of
adjacent `2 x 2` brackets, or a higher-order Monge inequality for the moment
sequence.

The full-support `3 x 3` payload has also been rewritten into moment-index
form.  Under full support, every Toeplitz entry is exactly:

```text
XiToeplitzEntry (rows a) (cols b)
  = XiMomentCoeff (rows a - cols b)
```

So the cleaner full-support target is now:

```text
XiMinorThreeFullSupportMomentFromContig
```

Lean verifies:

```text
XiMinorThreeFullSupportMomentFromContig
  -> XiMinorThreeFullSupportFromContig
```

via:

```text
xiMinorThreeFullSupportFromContig_of_moment
```

The sharpest RH route currently checked in Lean is therefore:

```text
XiMomentKernelRep
  -> XiMinorThreeFullSupportMomentFromContig
  -> XiMinorThreeBandedMiddleCompoundRatioFromContig
  -> XiAllMinorGeFourContigCertificates
  -> XiContigToFullPFBridge
```

The newest RH-closing bundle is:

```text
KernelContigToPFThreeMomentCompoundRatioTheorem
```

Lean verifies:

```text
KernelContigToPFThreeMomentCompoundRatioTheorem -> XiToeplitzTotalPositive
KernelContigToPFThreeMomentCompoundRatioTheorem -> RiemannHypothesis
```

via:

```text
xiToeplitzTotalPositive_of_kernelContigToPFThreeMomentCompoundRatio
riemannHypothesis_of_kernelContigToPFThreeMomentCompoundRatio
```

The next loop should attack the two explicit moment-index `3 x 3` payloads
together, either as total positivity of the second compound sequence, a
Lorentzian/Hodge inequality, or a planar-network determinant statement.  The
remaining tail remains `XiAllMinorGeFourContigCertificates`.

Those two explicit `3 x 3` moment payloads are now packaged as one named
condition:

```text
XiMinorThreeMomentPayloadFromContig
```

It is exactly:

```text
XiMinorThreeFullSupportMomentFromContig
  and XiMinorThreeBandedMiddleCompoundRatioFromContig
```

Lean verifies the projections:

```text
XiMinorThreeMomentPayloadFromContig
  -> XiMinorThreeFullSupportMomentFromContig
XiMinorThreeMomentPayloadFromContig
  -> XiMinorThreeBandedMiddleCompoundRatioFromContig
```

via:

```text
xiMinorThreeFullSupportMoment_of_momentPayload
xiMinorThreeBandedMiddleCompoundRatio_of_momentPayload
```

The sharpest RH route currently checked in Lean is now:

```text
XiMomentKernelRep
  -> XiMinorThreeMomentPayloadFromContig
  -> XiAllMinorGeFourContigCertificates
  -> XiContigToFullPFBridge
```

The newest RH-closing bundle is:

```text
KernelContigToPFThreeMomentPayloadTheorem
```

Lean verifies:

```text
KernelContigToPFThreeMomentPayloadTheorem -> XiToeplitzTotalPositive
KernelContigToPFThreeMomentPayloadTheorem -> RiemannHypothesis
```

via:

```text
xiToeplitzTotalPositive_of_kernelContigToPFThreeMomentPayload
riemannHypothesis_of_kernelContigToPFThreeMomentPayload
```

The next loop should either prove `XiMinorThreeMomentPayloadFromContig` from a
single second-compound/Lorentzian/Hodge model, or recursively reduce the
remaining `XiAllMinorGeFourContigCertificates` tail in the same certificate
style.

The remaining `k >= 4` tail has now been split into the first concrete tail
rung and the next tail:

```text
XiMinorFourContigCertificates
XiAllMinorGeFiveContigCertificates
```

Lean verifies:

```text
XiMinorFourContigCertificates
  -> XiAllMinorGeFiveContigCertificates
  -> XiAllMinorGeFourContigCertificates
```

via:

```text
xiAllMinorGeFour_of_four_and_geFive
```

The sharpest RH route currently checked in Lean is now:

```text
XiMomentKernelRep
  -> XiMinorThreeMomentPayloadFromContig
  -> XiMinorFourContigCertificates
  -> XiAllMinorGeFiveContigCertificates
  -> XiContigToFullPFBridge
```

The newest RH-closing bundle is:

```text
KernelContigToPFThreeMomentPayloadFourAndGeFiveTheorem
```

Lean verifies:

```text
KernelContigToPFThreeMomentPayloadFourAndGeFiveTheorem -> XiToeplitzTotalPositive
KernelContigToPFThreeMomentPayloadFourAndGeFiveTheorem -> RiemannHypothesis
```

via:

```text
xiToeplitzTotalPositive_of_kernelContigToPFThreeMomentPayloadFourAndGeFive
riemannHypothesis_of_kernelContigToPFThreeMomentPayloadFourAndGeFive
```

The next loop can now either attack the unified `3 x 3` moment payload or
start the same support/certificate decomposition for the concrete `4 x 4` rung.

The `4 x 4` rung has now been split by support, matching the earlier `3 x 3`
strategy:

```text
XiMinorFourFullSupportFromContig
XiMinorFourMixedSupportCertificates
```

Zero-row and zero-column cases are already handled by the arbitrary-size
zero-support certificate families.  Lean verifies:

```text
XiMinorFourFullSupportFromContig
  -> XiMinorFourMixedSupportCertificates
  -> XiMinorFourContigCertificates
```

via:

```text
xiMinorFourContigCertificates_of_full_and_mixed
```

The sharpest RH route currently checked in Lean is now:

```text
XiMomentKernelRep
  -> XiMinorThreeMomentPayloadFromContig
  -> XiMinorFourFullSupportFromContig
  -> XiMinorFourMixedSupportCertificates
  -> XiAllMinorGeFiveContigCertificates
  -> XiContigToFullPFBridge
```

The newest RH-closing bundle is:

```text
KernelContigToPFThreeMomentPayloadFourSupportSplitTheorem
```

Lean verifies:

```text
KernelContigToPFThreeMomentPayloadFourSupportSplitTheorem -> XiToeplitzTotalPositive
KernelContigToPFThreeMomentPayloadFourSupportSplitTheorem -> RiemannHypothesis
```

via:

```text
xiToeplitzTotalPositive_of_kernelContigToPFThreeMomentPayloadFourSupportSplit
riemannHypothesis_of_kernelContigToPFThreeMomentPayloadFourSupportSplit
```

The next loop should either rewrite `XiMinorFourFullSupportFromContig` into
moment-index form, or classify `XiMinorFourMixedSupportCertificates` into
smaller sparse support patterns.

The full-support `4 x 4` target has now been rewritten into moment-index form:

```text
XiMinorFourFullSupportMomentFromContig
```

Under full support, Lean rewrites the whole `4 x 4` Toeplitz-entry matrix to
the moment matrix using matrix extensionality rather than expanding the
determinant.  Lean verifies:

```text
XiMinorFourFullSupportMomentFromContig
  -> XiMinorFourFullSupportFromContig
```

via:

```text
xiMinorFourFullSupportFromContig_of_moment
```

The sharpest RH route currently checked in Lean is now:

```text
XiMomentKernelRep
  -> XiMinorThreeMomentPayloadFromContig
  -> XiMinorFourFullSupportMomentFromContig
  -> XiMinorFourMixedSupportCertificates
  -> XiAllMinorGeFiveContigCertificates
  -> XiContigToFullPFBridge
```

The newest RH-closing bundle is:

```text
KernelContigToPFThreeMomentPayloadFourMomentSupportSplitTheorem
```

Lean verifies:

```text
KernelContigToPFThreeMomentPayloadFourMomentSupportSplitTheorem -> XiToeplitzTotalPositive
KernelContigToPFThreeMomentPayloadFourMomentSupportSplitTheorem -> RiemannHypothesis
```

via:

```text
xiToeplitzTotalPositive_of_kernelContigToPFThreeMomentPayloadFourMomentSupportSplit
riemannHypothesis_of_kernelContigToPFThreeMomentPayloadFourMomentSupportSplit
```

The next loop should classify `XiMinorFourMixedSupportCertificates` into
smaller sparse support patterns, or look for a single compound/Lorentzian model
that proves both the `3 x 3` moment payload and the `4 x 4` full-support moment
target.

The `3 x 3` moment payload and the full-support `4 x 4` moment target are now
packaged as one low-rank moment condition:

```text
XiLowRankMomentPayloadFromContig
```

It is exactly:

```text
XiMinorThreeMomentPayloadFromContig
  and XiMinorFourFullSupportMomentFromContig
```

Lean verifies the projections:

```text
XiLowRankMomentPayloadFromContig
  -> XiMinorThreeMomentPayloadFromContig
XiLowRankMomentPayloadFromContig
  -> XiMinorFourFullSupportMomentFromContig
```

via:

```text
xiMinorThreeMomentPayload_of_lowRankMomentPayload
xiMinorFourFullSupportMoment_of_lowRankMomentPayload
```

The sharpest RH route currently checked in Lean is now:

```text
XiMomentKernelRep
  -> XiLowRankMomentPayloadFromContig
  -> XiMinorFourMixedSupportCertificates
  -> XiAllMinorGeFiveContigCertificates
  -> XiContigToFullPFBridge
```

The newest RH-closing bundle is:

```text
KernelContigToPFLowRankMomentFourMixedTheorem
```

Lean verifies:

```text
KernelContigToPFLowRankMomentFourMixedTheorem -> XiToeplitzTotalPositive
KernelContigToPFLowRankMomentFourMixedTheorem -> RiemannHypothesis
```

via:

```text
xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourMixed
riemannHypothesis_of_kernelContigToPFLowRankMomentFourMixed
```

The next loop should classify `XiMinorFourMixedSupportCertificates` into
sparse `4 x 4` support classes, or prove `XiLowRankMomentPayloadFromContig`
from a single total-positivity/Hodge/Lorentzian model.

The broad `4 x 4` mixed-support target has now been sharpened to the first
monotone support envelope:

```text
XiMinorFourBandedMixedSupportCertificates
```

For strictly monotone `4 x 4` row and column patterns, no zero row, no zero
column, and not-full support force:

```text
cols 0 <= rows 0
rows 0 < cols 3
cols 3 <= rows 3
```

Lean verifies:

```text
XiMinorFourBandedMixedSupportCertificates
  -> XiMinorFourMixedSupportCertificates
```

via:

```text
xiMinorFourMixedSupportCertificates_of_banded
```

The sharpest RH route currently checked in Lean is now:

```text
XiMomentKernelRep
  -> XiLowRankMomentPayloadFromContig
  -> XiMinorFourBandedMixedSupportCertificates
  -> XiAllMinorGeFiveContigCertificates
  -> XiContigToFullPFBridge
```

The newest RH-closing bundle is:

```text
KernelContigToPFLowRankMomentFourBandedMixedTheorem
```

Lean verifies:

```text
KernelContigToPFLowRankMomentFourBandedMixedTheorem -> XiToeplitzTotalPositive
KernelContigToPFLowRankMomentFourBandedMixedTheorem -> RiemannHypothesis
```

via:

```text
xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedMixed
riemannHypothesis_of_kernelContigToPFLowRankMomentFourBandedMixed
```

The next loop should decompose this banded `4 x 4` envelope further by the
middle support pattern, analogous to the earlier `3 x 3` banded determinant
split.

That envelope has now been converted to determinant form:

```text
XiMinorFourBandedDetInequalityFromContig
```

For strictly monotone `4 x 4` row and column patterns, it asks for the single
finite determinant inequality:

```text
cols 0 <= rows 0
rows 0 < cols 3
cols 3 <= rows 3
XiContigToeplitzTotalPositive
  -> det (fun a b => XiToeplitzEntry (rows a) (cols b)) >= 0
```

Lean verifies:

```text
XiMinorFourBandedDetInequalityFromContig
  -> XiMinorFourBandedMixedSupportCertificates
```

via:

```text
xiMinorFourBandedMixedSupportCertificates_of_detInequality
```

The sharpest RH route currently checked in Lean is now:

```text
XiMomentKernelRep
  -> XiLowRankMomentPayloadFromContig
  -> XiMinorFourBandedDetInequalityFromContig
  -> XiAllMinorGeFiveContigCertificates
  -> XiContigToFullPFBridge
```

The newest RH-closing bundle is:

```text
KernelContigToPFLowRankMomentFourBandedDetTheorem
```

Lean verifies:

```text
KernelContigToPFLowRankMomentFourBandedDetTheorem -> XiToeplitzTotalPositive
KernelContigToPFLowRankMomentFourBandedDetTheorem -> RiemannHypothesis
```

via:

```text
xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedDet
riemannHypothesis_of_kernelContigToPFLowRankMomentFourBandedDet
```

The next loop should expand this `4 x 4` banded determinant along the forced
zero upper-right entry, then split the remaining cases by the middle support
pattern, exactly as the `3 x 3` route split into middle-supported and zero-edge
targets.

The forced upper-right zero has now been internalized as a structured
determinant target:

```text
XiMinorFourBandedUpperRightZeroDetInequalityFromContig
```

It replaces the `(0, 3)` entry of the `4 x 4` determinant matrix by `0`, using
the band assumption:

```text
rows 0 < cols 3
```

Lean verifies:

```text
XiMinorFourBandedUpperRightZeroDetInequalityFromContig
  -> XiMinorFourBandedDetInequalityFromContig
```

via:

```text
xiMinorFourBandedDetInequality_of_upperRightZero
```

The sharpest RH route currently checked in Lean is now:

```text
XiMomentKernelRep
  -> XiLowRankMomentPayloadFromContig
  -> XiMinorFourBandedUpperRightZeroDetInequalityFromContig
  -> XiAllMinorGeFiveContigCertificates
  -> XiContigToFullPFBridge
```

The newest RH-closing bundle is:

```text
KernelContigToPFLowRankMomentFourBandedUpperRightZeroTheorem
```

Lean verifies:

```text
KernelContigToPFLowRankMomentFourBandedUpperRightZeroTheorem -> XiToeplitzTotalPositive
KernelContigToPFLowRankMomentFourBandedUpperRightZeroTheorem -> RiemannHypothesis
```

via:

```text
xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedUpperRightZero
riemannHypothesis_of_kernelContigToPFLowRankMomentFourBandedUpperRightZero
```

The next loop should express this upper-right-zero determinant as a row-zero
cofactor expansion into three signed `3 x 3` determinant targets.  That is the
right entry point for the elliptic-curve / combinatorial / Euclidean and
non-Euclidean geometry ideas: they should be tested as mechanisms for proving
those `3 x 3` cofactor inequalities, not as vague global replacements for the
checked PF chain.

The upper-right-zero determinant has now been converted to row-zero cofactor
form:

```text
XiMinorFourBandedRowZeroCofactorInequalityFromContig
```

It asks for the Laplacian row-zero expansion of the structured `4 x 4` matrix:

```text
sum j : Fin 4,
  (-1)^j * A 0 j * det (A with row 0 and column j removed) >= 0
```

where:

```text
A a b =
  if a = 0 and b = 3 then 0
  else XiToeplitzEntry (rows a) (cols b)
```

Lean verifies:

```text
XiMinorFourBandedRowZeroCofactorInequalityFromContig
  -> XiMinorFourBandedUpperRightZeroDetInequalityFromContig
```

via:

```text
xiMinorFourBandedUpperRightZero_of_rowZeroCofactor
```

The sharpest RH route currently checked in Lean is now:

```text
XiMomentKernelRep
  -> XiLowRankMomentPayloadFromContig
  -> XiMinorFourBandedRowZeroCofactorInequalityFromContig
  -> XiAllMinorGeFiveContigCertificates
  -> XiContigToFullPFBridge
```

The newest RH-closing bundle is:

```text
KernelContigToPFLowRankMomentFourBandedRowZeroCofactorTheorem
```

Lean verifies:

```text
KernelContigToPFLowRankMomentFourBandedRowZeroCofactorTheorem -> XiToeplitzTotalPositive
KernelContigToPFLowRankMomentFourBandedRowZeroCofactorTheorem -> RiemannHypothesis
```

via:

```text
xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedRowZeroCofactor
riemannHypothesis_of_kernelContigToPFLowRankMomentFourBandedRowZeroCofactor
```

The next loop should remove the formally zero `j = 3` cofactor term and name
the surviving three-cofactor inequality.  After that, split each `3 x 3`
cofactor by support type and test the combinatorial/geometric ideas against
those finite subtargets.

The formally zero cofactor term has now been removed:

```text
XiMinorFourBandedThreeCofactorInequalityFromContig
```

It names the three surviving row-zero cofactors:

```text
A 0 0 * det(A without row 0, col 0)
  - A 0 1 * det(A without row 0, col 1)
  + A 0 2 * det(A without row 0, col 2)
  >= 0
```

where:

```text
A a b =
  if a = 0 and b = 3 then 0
  else XiToeplitzEntry (rows a) (cols b)
```

Lean verifies:

```text
XiMinorFourBandedThreeCofactorInequalityFromContig
  -> XiMinorFourBandedRowZeroCofactorInequalityFromContig
```

via:

```text
xiMinorFourBandedRowZeroCofactor_of_threeCofactor
```

The sharpest RH route currently checked in Lean is now:

```text
XiMomentKernelRep
  -> XiLowRankMomentPayloadFromContig
  -> XiMinorFourBandedThreeCofactorInequalityFromContig
  -> XiAllMinorGeFiveContigCertificates
  -> XiContigToFullPFBridge
```

The newest RH-closing bundle is:

```text
KernelContigToPFLowRankMomentFourBandedThreeCofactorTheorem
```

Lean verifies:

```text
KernelContigToPFLowRankMomentFourBandedThreeCofactorTheorem -> XiToeplitzTotalPositive
KernelContigToPFLowRankMomentFourBandedThreeCofactorTheorem -> RiemannHypothesis
```

via:

```text
xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedThreeCofactor
riemannHypothesis_of_kernelContigToPFLowRankMomentFourBandedThreeCofactor
```

The next loop should isolate the three `3 x 3` cofactor matrices as named
objects or predicates, then classify each cofactor by support.  This is where
the existing `3 x 3` banded/moment machinery can be reused, and where any
elliptic-curve, combinatorial, Euclidean, or non-Euclidean geometry idea must
produce a concrete inequality for one of these named finite cofactors.

The three `3 x 3` cofactor matrices have now been named:

```text
XiMinorFourBandedCofactorMatrix rows cols j
```

This is the structured ambient `4 x 4` matrix with row `0` and column `j`
removed, after inserting the forced upper-right zero.  The corresponding
frontier is:

```text
XiMinorFourBandedNamedCofactorInequalityFromContig
```

Lean verifies:

```text
XiMinorFourBandedNamedCofactorInequalityFromContig
  -> XiMinorFourBandedThreeCofactorInequalityFromContig
```

via:

```text
xiMinorFourBandedThreeCofactor_of_namedCofactor
```

The sharpest RH route currently checked in Lean is now:

```text
XiMomentKernelRep
  -> XiLowRankMomentPayloadFromContig
  -> XiMinorFourBandedNamedCofactorInequalityFromContig
  -> XiAllMinorGeFiveContigCertificates
  -> XiContigToFullPFBridge
```

The newest RH-closing bundle is:

```text
KernelContigToPFLowRankMomentFourBandedNamedCofactorTheorem
```

Lean verifies:

```text
KernelContigToPFLowRankMomentFourBandedNamedCofactorTheorem -> XiToeplitzTotalPositive
KernelContigToPFLowRankMomentFourBandedNamedCofactorTheorem -> RiemannHypothesis
```

via:

```text
xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedNamedCofactor
riemannHypothesis_of_kernelContigToPFLowRankMomentFourBandedNamedCofactor
```

The next loop should define support predicates for
`XiMinorFourBandedCofactorMatrix rows cols 0`,
`XiMinorFourBandedCofactorMatrix rows cols 1`, and
`XiMinorFourBandedCofactorMatrix rows cols 2`, then connect those predicates
to the existing `3 x 3` full-support and banded mixed-support determinant
machinery.

The cofactor row and column selectors are now named:

```text
XiMinorFourBandedCofactorRows rows
XiMinorFourBandedCofactorCols cols j
```

and the first support predicates are now available:

```text
XiMinorFourBandedCofactorFullSupport rows cols j
XiMinorFourBandedCofactorBandedSupport rows cols j
XiMinorFourBandedCofactorSupportClass rows cols j
```

Lean verifies the structural identity:

```text
XiMinorFourBandedCofactorMatrix rows cols j
  =
Matrix.of (fun a b =>
  XiToeplitzEntry
    (XiMinorFourBandedCofactorRows rows a)
    (XiMinorFourBandedCofactorCols cols j b))
```

via:

```text
xiMinorFourBandedCofactorMatrix_eq_toeplitz
```

The corresponding row/column-selector frontier is:

```text
XiMinorFourBandedCofactorRowColInequalityFromContig
```

Lean verifies:

```text
XiMinorFourBandedCofactorRowColInequalityFromContig
  -> XiMinorFourBandedNamedCofactorInequalityFromContig
```

via:

```text
xiMinorFourBandedNamedCofactor_of_rowCol
```

The sharpest RH route currently checked in Lean is now:

```text
XiMomentKernelRep
  -> XiLowRankMomentPayloadFromContig
  -> XiMinorFourBandedCofactorRowColInequalityFromContig
  -> XiAllMinorGeFiveContigCertificates
  -> XiContigToFullPFBridge
```

The newest RH-closing bundle is:

```text
KernelContigToPFLowRankMomentFourBandedCofactorRowColTheorem
```

Lean verifies:

```text
KernelContigToPFLowRankMomentFourBandedCofactorRowColTheorem -> XiToeplitzTotalPositive
KernelContigToPFLowRankMomentFourBandedCofactorRowColTheorem -> RiemannHypothesis
```

via:

```text
xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedCofactorRowCol
riemannHypothesis_of_kernelContigToPFLowRankMomentFourBandedCofactorRowCol
```

Important honesty note: the current `4 x 4` band assumptions do not by
themselves force every cofactor into the first two classes
`FullSupport ∨ BandedSupport`.  The next loop should add zero-row and
zero-column cofactor support classes, then prove a total support-class split
for cofactors `j = 0, 1, 2`.

Zero-row and zero-column cofactor support classes have now been added:

```text
XiMinorFourBandedCofactorZeroRowSupport rows cols j
XiMinorFourBandedCofactorZeroColumnSupport rows cols j
```

The cofactor support-class predicate is now:

```text
XiMinorFourBandedCofactorSupportClass rows cols j
  =
ZeroRowSupport
  or ZeroColumnSupport
  or FullSupport
  or BandedSupport
```

The corresponding support-split frontier is:

```text
XiMinorFourBandedCofactorSupportSplitInequalityFromContig
```

The finite support-classification payload is now named:

```text
XiMinorFourBandedCofactorSupportClassesFromBand
```

It says that, under strict monotonicity and the `4 x 4` band assumptions, the
three surviving cofactors are classified:

```text
XiMinorFourBandedCofactorSupportClass rows cols 0
XiMinorFourBandedCofactorSupportClass rows cols 1
XiMinorFourBandedCofactorSupportClass rows cols 2
```

Lean verifies:

```text
XiMinorFourBandedCofactorSupportSplitInequalityFromContig
  and XiMinorFourBandedCofactorSupportClassesFromBand
  -> XiMinorFourBandedCofactorRowColInequalityFromContig
```

via:

```text
xiMinorFourBandedCofactorRowCol_of_supportSplit
```

The sharpest RH route currently checked in Lean is now:

```text
XiMomentKernelRep
  -> XiLowRankMomentPayloadFromContig
  -> XiMinorFourBandedCofactorSupportSplitInequalityFromContig
  -> XiMinorFourBandedCofactorSupportClassesFromBand
  -> XiAllMinorGeFiveContigCertificates
  -> XiContigToFullPFBridge
```

The newest RH-closing bundle is:

```text
KernelContigToPFLowRankMomentFourBandedCofactorSupportSplitTheorem
```

Lean verifies:

```text
KernelContigToPFLowRankMomentFourBandedCofactorSupportSplitTheorem -> XiToeplitzTotalPositive
KernelContigToPFLowRankMomentFourBandedCofactorSupportSplitTheorem -> RiemannHypothesis
```

via:

```text
xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedCofactorSupportSplit
riemannHypothesis_of_kernelContigToPFLowRankMomentFourBandedCofactorSupportSplit
```

The next loop should prove the finite support classification payload:

```text
XiMinorFourBandedCofactorSupportClassesFromBand
```

for cofactors `j = 0, 1, 2` from strict monotonicity and the `4 x 4` band
assumptions, then split
`XiMinorFourBandedCofactorSupportSplitInequalityFromContig` by the four
support classes.

The combined support-classification payload has now been split into three
cofactor-specific targets:

```text
XiMinorFourBandedCofactorJ0SupportClassFromBand
XiMinorFourBandedCofactorJ1SupportClassFromBand
XiMinorFourBandedCofactorJ2SupportClassFromBand
```

Lean verifies:

```text
XiMinorFourBandedCofactorJ0SupportClassFromBand
  -> XiMinorFourBandedCofactorJ1SupportClassFromBand
  -> XiMinorFourBandedCofactorJ2SupportClassFromBand
  -> XiMinorFourBandedCofactorSupportClassesFromBand
```

via:

```text
xiMinorFourBandedCofactorSupportClasses_of_j012
```

The sharpest RH route currently checked in Lean is now:

```text
XiMomentKernelRep
  -> XiLowRankMomentPayloadFromContig
  -> XiMinorFourBandedCofactorSupportSplitInequalityFromContig
  -> XiMinorFourBandedCofactorJ0SupportClassFromBand
  -> XiMinorFourBandedCofactorJ1SupportClassFromBand
  -> XiMinorFourBandedCofactorJ2SupportClassFromBand
  -> XiAllMinorGeFiveContigCertificates
  -> XiContigToFullPFBridge
```

The newest RH-closing bundle is:

```text
KernelContigToPFLowRankMomentFourBandedCofactorJ012Theorem
```

Lean verifies:

```text
KernelContigToPFLowRankMomentFourBandedCofactorJ012Theorem -> XiToeplitzTotalPositive
KernelContigToPFLowRankMomentFourBandedCofactorJ012Theorem -> RiemannHypothesis
```

via:

```text
xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedCofactorJ012
riemannHypothesis_of_kernelContigToPFLowRankMomentFourBandedCofactorJ012
```

The next loop should attack `XiMinorFourBandedCofactorJ0SupportClassFromBand`
first.  It is the most accessible deleted-column case because the cofactor
columns are the original columns `1, 2, 3`, while the cofactor rows are
original rows `1, 2, 3`.

The `j = 0` cofactor classification is now proved:

```text
xiMinorFourBandedCofactorJ0SupportClass_fromBand
```

Lean proves this by a finite support split.  For the deleted-column `j = 0`
cofactor, the rows are original rows `1, 2, 3` and the columns are original
columns `1, 2, 3`.  The proof uses:

```text
cols 3 <= rows 3
```

plus strict monotonicity.  Either:

```text
rows 1 < cols 1
```

so the cofactor has a zero row; or:

```text
cols 1 <= rows 1 and rows 1 < cols 3
```

so the cofactor is banded; or:

```text
cols 3 <= rows 1
```

so the cofactor is full-support.

The sharpest RH route currently checked in Lean is now:

```text
XiMomentKernelRep
  -> XiLowRankMomentPayloadFromContig
  -> XiMinorFourBandedCofactorSupportSplitInequalityFromContig
  -> XiMinorFourBandedCofactorJ1SupportClassFromBand
  -> XiMinorFourBandedCofactorJ2SupportClassFromBand
  -> XiAllMinorGeFiveContigCertificates
  -> XiContigToFullPFBridge
```

The newest RH-closing bundle is:

```text
KernelContigToPFLowRankMomentFourBandedCofactorJ12Theorem
```

Lean verifies:

```text
KernelContigToPFLowRankMomentFourBandedCofactorJ12Theorem -> XiToeplitzTotalPositive
KernelContigToPFLowRankMomentFourBandedCofactorJ12Theorem -> RiemannHypothesis
```

via:

```text
xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedCofactorJ12
riemannHypothesis_of_kernelContigToPFLowRankMomentFourBandedCofactorJ12
```

The next loop should attack `XiMinorFourBandedCofactorJ1SupportClassFromBand`.
This is subtler than `j = 0` because the deleted column is the original middle
column, so the cofactor columns are original columns `0, 2, 3`.

The `j = 1` cofactor classification is now proved:

```text
xiMinorFourBandedCofactorJ1SupportClass_fromBand
```

For the deleted-column `j = 1` cofactor, the rows are original rows `1, 2, 3`
and the columns are original columns `0, 2, 3`.  Lean proves the class split
from:

```text
cols 0 <= rows 0 < rows 1
cols 3 <= rows 3
```

plus strict monotonicity.  Either:

```text
rows 1 < cols 3
```

so the cofactor is banded; or:

```text
cols 3 <= rows 1
```

so the cofactor is full-support.

The `j = 2` cofactor classification is now proved:

```text
xiMinorFourBandedCofactorJ2SupportClass_fromBand
  : XiMinorFourBandedCofactorJ2SupportClassFromBand
```

For the deleted-column `j = 2` cofactor, the rows are original rows `1, 2, 3`
and the columns are original columns `0, 1, 3`.  The proof again uses only
strict monotonicity and the outer band assumptions:

```text
cols 0 <= rows 0 < rows 1
```

gives the left band edge for the cofactor.  If:

```text
rows 1 < cols 3
```

then the cofactor is banded.  Otherwise:

```text
cols 3 <= rows 1
```

and monotonicity forces every selected cofactor column to lie weakly left of
every selected cofactor row, so the cofactor is full-support.

Therefore the sharpest RH route currently checked in Lean is now:

```text
XiMomentKernelRep
  -> XiLowRankMomentPayloadFromContig
  -> XiMinorFourBandedCofactorSupportSplitInequalityFromContig
  -> XiAllMinorGeFiveContigCertificates
  -> XiContigToFullPFBridge
```

The newest RH-closing bundle is:

```text
KernelContigToPFLowRankMomentFourBandedCofactorSupportSplitOnlyTheorem
```

Lean verifies:

```text
KernelContigToPFLowRankMomentFourBandedCofactorSupportSplitOnlyTheorem -> XiToeplitzTotalPositive
KernelContigToPFLowRankMomentFourBandedCofactorSupportSplitOnlyTheorem -> RiemannHypothesis
```

via:

```text
xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedCofactorSupportSplitOnly
riemannHypothesis_of_kernelContigToPFLowRankMomentFourBandedCofactorSupportSplitOnly
```

That support-split target has now been converted into an explicit finite
support-kind table:

```text
XiMinorFourBandedCofactorSupportKind
XiMinorFourBandedCofactorSupportKindHolds
XiMinorFourBandedCofactorSupportCaseTableInequalityFromContig
```

The four support kinds are:

```text
zeroRow
zeroColumn
full
banded
```

Lean verifies:

```text
XiMinorFourBandedCofactorSupportCaseTableInequalityFromContig
  -> XiMinorFourBandedCofactorSupportSplitInequalityFromContig
```

via:

```text
xiMinorFourBandedCofactorSupportSplit_of_caseTable
```

The sharpest RH route currently checked in Lean is now:

```text
XiMomentKernelRep
  -> XiLowRankMomentPayloadFromContig
  -> XiMinorFourBandedCofactorSupportCaseTableInequalityFromContig
  -> XiAllMinorGeFiveContigCertificates
  -> XiContigToFullPFBridge
```

The newest RH-closing bundle is:

```text
KernelContigToPFLowRankMomentFourBandedCofactorCaseTableTheorem
```

Lean verifies:

```text
KernelContigToPFLowRankMomentFourBandedCofactorCaseTableTheorem -> XiToeplitzTotalPositive
KernelContigToPFLowRankMomentFourBandedCofactorCaseTableTheorem -> RiemannHypothesis
```

via:

```text
xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedCofactorCaseTable
riemannHypothesis_of_kernelContigToPFLowRankMomentFourBandedCofactorCaseTable
```

The next loop should attack the case table one support-kind triple at a time.
There are `4^3 = 64` formal triples, but many should collapse immediately:

- any cofactor with `zeroRow` or `zeroColumn` should reduce that determinant to
  zero;
- `full` cofactors should reduce to ordinary contiguous-kernel positivity;
- `banded` cofactors carry the real sparse `3 x 3` inequality.

This is now the right place to test elliptic-curve, combinatorial, Euclidean,
and non-Euclidean geometry ideas: each idea must prove one named case-table
family or one reusable determinant lemma for `full`/`banded` cofactors, not make
a global RH claim.

The first reusable case-table reductions are now proved:

```text
xiMinorFourBandedCofactorDet_eq_zero_of_zeroRowSupport
xiMinorFourBandedCofactorDet_eq_zero_of_zeroColumnSupport
```

They say that if any selected `3 x 3` cofactor has a zero row or zero column
support pattern, then that cofactor determinant is exactly `0`.  These lemmas
do not by themselves prove the signed three-cofactor inequality, but they
remove determinant terms inside any case-table row involving `zeroRow` or
`zeroColumn`.  The next useful proof step is to define a reduced case-family
where the zero cofactors have already been erased from:

```text
A00 * det C0 - A01 * det C1 + A02 * det C2
```

The all-zero-kind rows have now been discharged by a reduced case-table bridge:

```text
XiMinorFourBandedCofactorSupportKindActive
XiMinorFourBandedCofactorNonzeroCaseTableInequalityFromContig
xiMinorFourBandedCofactorCaseTable_of_nonzeroCaseTable
```

Here active means that at least one of the three cofactors has support kind
`full` or `banded`.  If no cofactor is active, then every cofactor is
`zeroRow` or `zeroColumn`, so all three cofactor determinants vanish and the
signed expression is automatically `0`.

The sharpest RH route currently checked in Lean is now:

```text
XiMomentKernelRep
  -> XiLowRankMomentPayloadFromContig
  -> XiMinorFourBandedCofactorNonzeroCaseTableInequalityFromContig
  -> XiAllMinorGeFiveContigCertificates
  -> XiContigToFullPFBridge
```

The newest RH-closing bundle is:

```text
KernelContigToPFLowRankMomentFourBandedCofactorNonzeroCaseTableTheorem
```

Lean verifies:

```text
KernelContigToPFLowRankMomentFourBandedCofactorNonzeroCaseTableTheorem -> XiToeplitzTotalPositive
KernelContigToPFLowRankMomentFourBandedCofactorNonzeroCaseTableTheorem -> RiemannHypothesis
```

via:

```text
xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedCofactorNonzeroCaseTable
riemannHypothesis_of_kernelContigToPFLowRankMomentFourBandedCofactorNonzeroCaseTable
```

That split is now named:

```text
XiMinorFourBandedCofactorExactlyOneActive
XiMinorFourBandedCofactorAtLeastTwoActive
XiMinorFourBandedCofactorOneSurvivorCaseTableInequalityFromContig
XiMinorFourBandedCofactorMultiSurvivorCaseTableInequalityFromContig
xiMinorFourBandedCofactorNonzeroCaseTable_of_survivorSplit
```

Lean verifies that the one-survivor and multi-survivor tables together imply
the reduced nonzero-survivor table.

The sharpest RH route currently checked in Lean is now:

```text
XiMomentKernelRep
  -> XiLowRankMomentPayloadFromContig
  -> XiMinorFourBandedCofactorOneSurvivorCaseTableInequalityFromContig
  -> XiMinorFourBandedCofactorMultiSurvivorCaseTableInequalityFromContig
  -> XiAllMinorGeFiveContigCertificates
  -> XiContigToFullPFBridge
```

The newest RH-closing bundle is:

```text
KernelContigToPFLowRankMomentFourBandedCofactorSurvivorSplitTheorem
```

Lean verifies:

```text
KernelContigToPFLowRankMomentFourBandedCofactorSurvivorSplitTheorem -> XiToeplitzTotalPositive
KernelContigToPFLowRankMomentFourBandedCofactorSurvivorSplitTheorem -> RiemannHypothesis
```

via:

```text
xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedCofactorSurvivorSplit
riemannHypothesis_of_kernelContigToPFLowRankMomentFourBandedCofactorSurvivorSplit
```

The one-survivor target has now been split by the position of the unique active
cofactor:

```text
XiMinorFourBandedCofactorOneSurvivorJ0InequalityFromContig
XiMinorFourBandedCofactorOneSurvivorJ1InequalityFromContig
XiMinorFourBandedCofactorOneSurvivorJ2InequalityFromContig
xiMinorFourBandedCofactorOneSurvivorCaseTable_of_j012
```

The `j = 0` and `j = 2` survivors have positive signs in the cofactor
expansion.  The `j = 1` survivor is the signed-negative case and must be treated
separately; it may be impossible except under additional structural restrictions
that force the active middle cofactor determinant to vanish or the coefficient
to vanish.

The sharpest RH route currently checked in Lean is now:

```text
XiMomentKernelRep
  -> XiLowRankMomentPayloadFromContig
  -> XiMinorFourBandedCofactorOneSurvivorJ0InequalityFromContig
  -> XiMinorFourBandedCofactorOneSurvivorJ1InequalityFromContig
  -> XiMinorFourBandedCofactorOneSurvivorJ2InequalityFromContig
  -> XiMinorFourBandedCofactorMultiSurvivorCaseTableInequalityFromContig
  -> XiAllMinorGeFiveContigCertificates
  -> XiContigToFullPFBridge
```

The newest RH-closing bundle is:

```text
KernelContigToPFLowRankMomentFourBandedCofactorOneSurvivorPositionTheorem
```

Lean verifies:

```text
KernelContigToPFLowRankMomentFourBandedCofactorOneSurvivorPositionTheorem -> XiToeplitzTotalPositive
KernelContigToPFLowRankMomentFourBandedCofactorOneSurvivorPositionTheorem -> RiemannHypothesis
```

via:

```text
xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedCofactorOneSurvivorPosition
riemannHypothesis_of_kernelContigToPFLowRankMomentFourBandedCofactorOneSurvivorPosition
```

The positive-sign one-survivor rows are now bundled:

```text
XiMinorFourBandedCofactorPositiveOneSurvivorInequalityFromContig
xiMinorFourBandedCofactorOneSurvivorCaseTable_of_positive_and_j1
```

This payload is exactly the `j = 0` and `j = 2` one-survivor pair.  The
signed-negative `j = 1` one-survivor target remains explicit.

The sharpest RH route currently checked in Lean is now:

```text
XiMomentKernelRep
  -> XiLowRankMomentPayloadFromContig
  -> XiMinorFourBandedCofactorPositiveOneSurvivorInequalityFromContig
  -> XiMinorFourBandedCofactorOneSurvivorJ1InequalityFromContig
  -> XiMinorFourBandedCofactorMultiSurvivorCaseTableInequalityFromContig
  -> XiAllMinorGeFiveContigCertificates
  -> XiContigToFullPFBridge
```

The newest RH-closing bundle is:

```text
KernelContigToPFLowRankMomentFourBandedCofactorPositiveOneSurvivorTheorem
```

Lean verifies:

```text
KernelContigToPFLowRankMomentFourBandedCofactorPositiveOneSurvivorTheorem -> XiToeplitzTotalPositive
KernelContigToPFLowRankMomentFourBandedCofactorPositiveOneSurvivorTheorem -> RiemannHypothesis
```

via:

```text
xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedCofactorPositiveOneSurvivor
riemannHypothesis_of_kernelContigToPFLowRankMomentFourBandedCofactorPositiveOneSurvivor
riemannHypothesis_of_kernelContigToPFCofactorPositiveFull
riemannHypothesis_of_kernelContigToPFCofactorPositiveFullDet
riemannHypothesis_of_kernelContigToPFCofactorThreeFull
riemannHypothesis_of_kernelContigToPFCofactorThreeFullBanded
riemannHypothesis_of_kernelContigToPFCofactorJ1Nonpos
riemannHypothesis_of_kernelContigToPFCofactorJ1SupportSplit
riemannHypothesis_of_kernelContigToPFCofactorJ1FullMoment
riemannHypothesis_of_kernelContigToPFCofactorJ1FullMomentZero
```

The positive-side one-survivor payload has now been split by support type:

```text
XiMinorFourBandedCofactorOneSurvivorJ0FullInequalityFromContig
XiMinorFourBandedCofactorOneSurvivorJ0BandedInequalityFromContig
XiMinorFourBandedCofactorOneSurvivorJ2FullInequalityFromContig
XiMinorFourBandedCofactorOneSurvivorJ2BandedInequalityFromContig
XiMinorFourBandedCofactorPositiveFullOneSurvivorInequalityFromContig
XiMinorFourBandedCofactorPositiveFullDetFromContig
XiMinorFourBandedCofactorPositiveBandedOneSurvivorInequalityFromContig
XiMinorFourBandedCofactorOneSurvivorJ1NonposDetFromContig
XiMinorFourBandedCofactorOneSurvivorJ1FullNonposDetFromContig
XiMinorFourBandedCofactorOneSurvivorJ1FullMomentNonposDetFromContig
XiMinorFourBandedCofactorOneSurvivorJ1FullMomentZeroDetFromContig
XiJ1FullSupportImpossibleFromSupport
XiMinorFourBandedCofactorOneSurvivorJ1BandedNonposDetFromContig
XiMinorFourBandedCofactorOneSurvivorJ1BandedExpandedNonposFromContig
XiMinorFourBandedCofactorOneSurvivorJ1BandedProductDominanceFromContig
XiMinorFourBandedCofactorOneSurvivorJ1BandedBracketSignsFromContig
XiMinorFourBandedCofactorOneSurvivorJ1BandedLeftBracketNonposFromContig
XiMinorFourBandedCofactorOneSurvivorJ1BandedRightBracketNonnegFromContig
XiMinorFourBandedCofactorOneSurvivorJ1BandedSplitBracketsFromContig
XiMinorFourBandedCofactorOneSurvivorJ1BandedTopSupportedSplitBracketsFromContig
XiMinorFourBandedCofactorOneSurvivorJ1BandedTopSupportedMomentBracketsFromContig
XiJ1TopSupportedImpossibleFromSupport
XiMinorFourBandedCofactorOneSurvivorJ1BandedTopUnsupportedSplitBracketsFromContig
XiMinorFourBandedCofactorOneSurvivorJ1BandedTopUnsupportedMiddleSupportedBracketsFromContig
XiJ1TopUnsupportedMiddleSupportedBracketsFromContig
XiJ1TopUnsupportedMiddleSupportedMomentProductFromContig
XiJ1TopUnsupportedMiddleSupportedImpossibleFromSupport
XiMinorFourBandedCofactorOneSurvivorJ1BandedTopSupportSplitBracketsFromContig
XiMinorFourBandedCofactorOneSurvivorJ1SupportNonposDetFromContig
XiMinorFourBandedCofactorReducedMultiKindTriple
XiMinorFourBandedCofactorMultiSurvivorKindReductionFromSupport
XiMinorFourBandedCofactorMultiSurvivorPair01KindReductionFromSupport
XiMinorFourBandedCofactorMultiSurvivorPair02KindReductionFromSupport
XiMinorFourBandedCofactorMultiSurvivorPair12KindReductionFromSupport
XiMinorFourBandedCofactorMultiSurvivorPairKindReductionFromSupport
XiMinorFourBandedCofactorMultiSurvivorPair12FullFullLeftFullFromSupport
XiMinorFourBandedCofactorMultiSurvivorPair12FullBandedImpossibleFromSupport
XiMinorFourBandedCofactorMultiSurvivorPair12BandedFullImpossibleFromSupport
XiMinorFourBandedCofactorMultiSurvivorPair12BandedBandedLeftReducedFromSupport
XiMinorFourBandedCofactorMultiSurvivorPair12KindCasesFromSupport
XiMinorFourBandedCofactorMultiSurvivorPair12CasesKindReductionFromSupport
XiMinorFourBandedCofactorMultiSurvivorPair01Pair02KindReductionFromSupport
XiMinorFourBandedCofactorMultiSurvivorPair02FullFullMiddleFullFromSupport
XiMinorFourBandedCofactorMultiSurvivorPair02FullBandedImpossibleFromSupport
XiMinorFourBandedCofactorMultiSurvivorPair02BandedFullImpossibleFromSupport
XiMinorFourBandedCofactorMultiSurvivorPair02BandedBandedMiddleBandedFromSupport
XiMinorFourBandedCofactorMultiSurvivorPair02KindCasesFromSupport
XiMinorFourBandedCofactorMultiSurvivorPair01KindOnlyReductionFromSupport
XiMinorFourBandedCofactorMultiSurvivorPair01FullFullRightFullFromSupport
XiMinorFourBandedCofactorMultiSurvivorPair01FullBandedImpossibleFromSupport
XiMinorFourBandedCofactorMultiSurvivorPair01BandedFullImpossibleFromSupport
XiMinorFourBandedCofactorMultiSurvivorPair01BandedBandedRightBandedFromSupport
XiMinorFourBandedCofactorMultiSurvivorPair01KindCasesFromSupport
XiMinorFourBandedCofactorReducedMultiSurvivorCaseTableInequalityFromContig
XiMinorFourBandedCofactorMultiSupportDominanceFromContig
XiMinorFourBandedCofactorMiddleDominance
XiMinorFourBandedCofactorMiddleDominanceSideBound
XiMinorFourBandedCofactorMiddleDominanceSideNonnegative
XiMinorFourBandedCofactorSideDetNonnegative
XiMinorFourBandedCofactorSideDetLeftNonnegative
XiMinorFourBandedCofactorSideDetRightNonnegative
XiMinorFourBandedCofactorMiddleDominanceMiddleUpperBound
XiMinorFourBandedCofactorMiddleDetNonpositive
XiMinorFourBandedCofactorMiddleFullDetNonpositiveFromContig
XiMinorFourBandedCofactorMiddleFullDetZeroFromContig
XiMinorFourBandedCofactorMiddleFullMomentZeroFromContig
XiMinorFourBandedCofactorMiddleBandedDetNonpositiveFromContig
XiMinorFourBandedCofactorMiddleBandedExpandedNonpositiveFromContig
XiMinorFourBandedCofactorMiddleBandedProductDominanceFromContig
XiMinorFourBandedCofactorMiddleBandedBracketSignsFromContig
XiMinorFourBandedCofactorMiddleBandedLeftBracketNonpositiveFromContig
XiMinorFourBandedCofactorMiddleBandedRightBracketNonnegativeFromContig
XiMinorFourBandedCofactorMiddleBandedSplitBracketsFromContig
XiMinorFourBandedCofactorMiddleBandedTopSupportedSplitBracketsFromContig
XiMinorFourBandedCofactorMiddleBandedTopSupportedMomentBracketsFromContig
XiMinorFourBandedCofactorMiddleBandedTopUnsupportedSplitBracketsFromContig
XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedBracketsFromContig
XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedMomentProductFromContig
XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedLeftProductNonpositiveFromContig
XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedRightProductNonnegativeFromContig
XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedSplitProductsFromContig
XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedLeftProductFromContig
XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedLeftMomentZeroFromContig
XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedImpossibleFromSupport
XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedGapCollapseFromContext
XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedOriginalGapCollapseFromContext
XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedInactiveSideSupportFromContext
XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedRightInactiveSideSupportFromContext
XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedRightActiveExcludedFromContext
XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedRightBandedExcludedFromContext
XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedBranchImpossibleFromContext
XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleColumnUnsupportedFromContext
XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleColumnNoStraddleFromContext
XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleColumnStraddleImpossibleFromContext
XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleColumnStraddleLeftProductNonpositiveFromContig
XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleColumnStraddleLeftBracketNonpositiveFromContig
XiMinorFourBandedCofactorMiddleBandedTopSupportSplitBracketsFromContig
XiMinorFourBandedCofactorMiddleDetSupportSplitNonpositiveFromContig
XiMinorFourBandedCofactorMiddleDetFullZeroBandedNonpositiveFromContig
XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedNonpositiveFromContig
XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedExpandedFromContig
XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedProductFromContig
XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedBracketSignsFromContig
XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedSplitBracketsFromContig
XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopSupportSplitBracketsFromContig
XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopSupportedMomentFromContig
XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedFromContig
XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedMomentProductFromContig
XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedSplitProductsFromContig
XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedLeftProductFromContig
XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedLeftMomentZeroFromContig
XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedImpossibleFromSupport
XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedGapCollapseFromContext
XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedOriginalGapCollapseFromContext
XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedInactiveSideSupportFromContext
XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightInactiveSideSupportFromContext
XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightActiveExcludedFromContext
XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightBandedExcludedFromContext
XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedBranchImpossibleFromContext
XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnUnsupportedFromContext
XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnNoStraddleFromContext
XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleImpossibleFromContext
XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftProductFromContig
XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftBracketFromContig
XiMinorFourBandedCofactorMiddleDominanceFromContig
XiMinorFourBandedCofactorMiddleDominanceSideBoundFromContig
XiMinorFourBandedCofactorMiddleDominanceSideNonnegativeFromContig
XiMinorFourBandedCofactorSideDetNonnegativeFromContig
XiMinorFourBandedCofactorSideDetLeftNonnegativeFromContig
XiMinorFourBandedCofactorSideDetRightNonnegativeFromContig
XiMinorFourBandedCofactorMiddleDominanceMiddleUpperBoundFromContig
XiMinorFourBandedCofactorMiddleDetNonpositiveFromContig
XiMinorFourBandedCofactorMiddleDominanceSeparatedBoundsFromContig
XiMinorFourBandedCofactorMiddleDominanceDetSideAndMiddleFromContig
XiMinorFourBandedCofactorSideDetLeftRightNonnegativeFromContig
XiMinorFourBandedCofactorSideDetLeftRightSupportFromContig
XiMinorFourBandedCofactorSideDetLeftRightSupportClassFromContig
XiMinorFourBandedCofactorMiddleDominanceSplitSideDetAndMiddleFromContig
XiMinorFourBandedCofactorMiddleDominanceSupportSideAndMiddleFromContig
XiMinorFourBandedCofactorMiddleDominanceSupportClassSideAndMiddleFromContig
XiMinorFourBandedCofactorMultiRowGeometryDominanceFromContig
XiMinorFourBandedCofactorMultiFullFullFullFromContig
XiMinorFourBandedCofactorMultiFullFullFullDominanceFromContig
XiMinorFourBandedCofactorMultiBandedBandedBandedFromContig
XiMinorFourBandedCofactorMultiBandedBandedBandedDominanceFromContig
XiMinorFourBandedCofactorMultiZeroRowBandedBandedFromContig
XiMinorFourBandedCofactorMultiZeroRowBandedBandedTwoTermFromContig
XiMinorFourBandedCofactorMultiZeroRowBandedBandedDominanceFromContig
XiMinorFourBandedCofactorReducedMultiRowsFromContig
XiMinorFourBandedCofactorReducedMultiRowsTwoTermFromContig
XiMinorFourBandedCofactorReducedMultiSparseRowsTwoTermFromContig
XiMinorFourBandedCofactorReducedMultiSparseDominanceRowsTwoTermFromContig
XiMinorFourBandedCofactorReducedMultiSparseDominanceRowsDominanceFromContig
XiMinorFourBandedCofactorReducedMultiRowsFullSparseTwoTermFromContig
XiMinorFourBandedCofactorReducedMultiRowsFullDominanceSparseTwoTermFromContig
XiMinorFourBandedCofactorReducedMultiRowsFullDominanceSparseDominanceTwoTermFromContig
XiMinorFourBandedCofactorReducedMultiRowsAllDominanceFromContig
XiMinorFourBandedCofactorReducedMultiRowsUniformDominanceFromContig
XiMinorFourBandedCofactorReducedMultiRowsRowGeometryDominanceFromContig
xiMinorFourBandedCofactorPositiveOneSurvivor_of_full_banded
xiMinorFourBandedCofactorPositiveOneSurvivor_of_fullBundle_banded
xiMinorFourBandedCofactorPositiveFullOneSurvivor_of_det
xiMinorFourBandedCofactorPositiveFullDet_of_threeFull
xiMinorFourBandedCofactorPositiveBandedOneSurvivor_of_threeBandedDet
xiMinorFourBandedCofactorOneSurvivorJ1_of_nonposDet
xiMinorFourBandedCofactorOneSurvivorJ1NonposDet_of_supportSplit
xiMinorFourBandedCofactorOneSurvivorJ1FullNonposDet_of_moment
xiJ1FullSupportImpossible_of_support
xiMinorFourBandedCofactorOneSurvivorJ1FullMomentZeroDet_of_impossible
xiMinorFourBandedCofactorOneSurvivorJ1FullMomentZeroDet_of_support
xiMinorFourBandedCofactorOneSurvivorJ1FullMomentNonposDet_of_zero
xiMinorFourBandedCofactorOneSurvivorJ1BandedTopSupportedSplitBrackets_of_moment
xiJ1TopSupportedImpossible_of_support
xiJ1TopSupportedSplitBrackets_of_impossible
xiJ1TopSupportedSplitBrackets_of_support
xiJ1TopUnsupportedMiddleSupportedBrackets_of_momentProduct
xiJ1TopUnsupportedMiddleSupportedImpossible_of_support
xiJ1TopUnsupportedMiddleSupportedBrackets_of_impossible
xiJ1TopUnsupportedMiddleSupportedBrackets_of_support
xiMinorFourBandedCofactorOneSurvivorJ1BandedTopUnsupportedSplitBrackets_of_middleSupported
xiMinorFourBandedCofactorOneSurvivorJ1BandedTopUnsupportedSplitBrackets_of_support
xiMinorFourBandedCofactorOneSurvivorJ1BandedSplitBrackets_of_topSupportSplit
xiMinorFourBandedCofactorOneSurvivorJ1BandedBracketSigns_of_split
xiMinorFourBandedCofactorOneSurvivorJ1BandedProductDominance_of_bracketSigns
xiMinorFourBandedCofactorOneSurvivorJ1BandedExpandedNonpos_of_productDominance
xiMinorFourBandedCofactorOneSurvivorJ1BandedNonposDet_of_expanded
xiMinorFourBandedCofactorMultiSurvivorPair12FullFullLeftFull_of_support
xiMinorFourBandedCofactorMultiSurvivorPair12FullBandedImpossible_of_support
xiMinorFourBandedCofactorMultiSurvivorPair12BandedFullImpossible_of_support
xiMinorFourBandedCofactorMultiSurvivorPair12BandedBandedLeftReduced_of_support
xiMinorFourBandedCofactorMultiSurvivorPair12KindCases_of_support
xiMinorFourBandedCofactorMultiSurvivorPair12CasesKindReduction_of_pair01_pair02
xiMinorFourBandedCofactorMultiSurvivorPair02FullFullMiddleFull_of_support
xiMinorFourBandedCofactorMultiSurvivorPair02FullBandedImpossible_of_support
xiMinorFourBandedCofactorMultiSurvivorPair02BandedFullImpossible_of_support
xiMinorFourBandedCofactorMultiSurvivorPair02BandedBandedMiddleBanded_of_support
xiMinorFourBandedCofactorMultiSurvivorPair02KindCases_of_support
xiMinorFourBandedCofactorMultiSurvivorPair02KindReduction_of_cases
xiMinorFourBandedCofactorMultiSurvivorPair01Pair02KindReduction_of_pair01
xiMinorFourBandedCofactorMultiSurvivorPair01FullFullRightFull_of_support
xiMinorFourBandedCofactorMultiSurvivorPair01FullBandedImpossible_of_support
xiMinorFourBandedCofactorMultiSurvivorPair01BandedFullImpossible_of_support
xiMinorFourBandedCofactorMultiSurvivorPair01BandedBandedRightBanded_of_support
xiMinorFourBandedCofactorMultiSurvivorPair01KindCases_of_support
xiMinorFourBandedCofactorMultiSurvivorPair01KindReduction_of_cases
xiMinorFourBandedCofactorMultiSurvivorPair01KindOnlyReduction_of_support
xiMinorFourBandedCofactorMultiSurvivorPair12KindReduction_of_cases
xiMinorFourBandedCofactorMultiSurvivorPairKindReduction_of_pair12Cases
xiMinorFourBandedCofactorMultiSurvivorKindReduction_of_pair
xiMinorFourBandedCofactorMultiFullFullFull_of_dominance
xiMinorFourBandedCofactorMultiZeroRowBandedBanded_of_twoTerm
xiMinorFourBandedCofactorReducedMultiRowsFullSparseTwoTerm_of_dominance
xiMinorFourBandedCofactorReducedMultiRowsTwoTerm_of_fullSparse
xiMinorFourBandedCofactorReducedMultiRows_of_twoTerm
xiMinorFourBandedCofactorReducedMultiSurvivor_of_rows
xiMinorFourBandedCofactorMultiSurvivorCaseTable_of_reduced
```

The sharpest RH route currently checked in Lean is now:

```text
XiMomentKernelRep
  -> XiLowRankMomentPayloadFromContig
  -> XiMinorThreeFullSupportFromContig
  -> XiMinorThreeBandedDetInequalityFromContig
  -> XiMinorFourBandedCofactorPositiveFullDetFromContig
  -> XiMinorFourBandedCofactorPositiveFullOneSurvivorInequalityFromContig
  -> XiMinorFourBandedCofactorPositiveBandedOneSurvivorInequalityFromContig
  -> XiJ1FullSupportImpossibleFromSupport
  -> XiMinorFourBandedCofactorOneSurvivorJ1FullMomentZeroDetFromContig
  -> XiMinorFourBandedCofactorOneSurvivorJ1FullMomentNonposDetFromContig
  -> XiMinorFourBandedCofactorOneSurvivorJ1FullNonposDetFromContig
  -> XiJ1TopSupportedImpossibleFromSupport
  -> XiMinorFourBandedCofactorOneSurvivorJ1BandedTopSupportedSplitBracketsFromContig
  -> XiJ1TopUnsupportedMiddleSupportedImpossibleFromSupport
  -> XiMinorFourBandedCofactorOneSurvivorJ1BandedTopUnsupportedSplitBracketsFromContig
  -> XiMinorFourBandedCofactorOneSurvivorJ1BandedTopSupportSplitBracketsFromContig
  -> XiMinorFourBandedCofactorOneSurvivorJ1BandedLeftBracketNonposFromContig
  -> XiMinorFourBandedCofactorOneSurvivorJ1BandedRightBracketNonnegFromContig
  -> XiMinorFourBandedCofactorOneSurvivorJ1BandedSplitBracketsFromContig
  -> XiMinorFourBandedCofactorOneSurvivorJ1BandedBracketSignsFromContig
  -> XiMinorFourBandedCofactorOneSurvivorJ1BandedProductDominanceFromContig
  -> XiMinorFourBandedCofactorOneSurvivorJ1BandedExpandedNonposFromContig
  -> XiMinorFourBandedCofactorOneSurvivorJ1BandedNonposDetFromContig
  -> XiMinorFourBandedCofactorOneSurvivorJ1SupportNonposDetFromContig
  -> XiMinorFourBandedCofactorOneSurvivorJ1NonposDetFromContig
  -> XiMinorFourBandedCofactorOneSurvivorJ1InequalityFromContig
  -> XiMinorFourBandedCofactorMultiSurvivorCaseTableInequalityFromContig
  -> XiAllMinorGeFiveContigCertificates
  -> XiContigToFullPFBridge
```

The newest RH-closing bundle is:

```text
KernelContigToPFLowRankMomentFourBandedCofactorPositiveOneSurvivorSupportTheorem
KernelContigToPFLowRankMomentFourBandedCofactorPositiveFullTheorem
KernelContigToPFLowRankMomentFourBandedCofactorPositiveFullDetTheorem
KernelContigToPFLowRankMomentFourBandedCofactorThreeFullTheorem
KernelContigToPFLowRankMomentFourBandedCofactorThreeFullBandedTheorem
KernelContigToPFLowRankMomentFourBandedCofactorJ1NonposTheorem
KernelContigToPFLowRankMomentFourBandedCofactorJ1SupportSplitTheorem
KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentTheorem
KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroTheorem
KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedExpandedTheorem
KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedProductTheorem
KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedSignsTheorem
KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedSplitTheorem
KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedTopSupportTheorem
KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedTopMomentTheorem
KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedTopMomentMiddleTheorem
KernelContigToPFJ1TopMomentMiddleProductTheorem
KernelContigToPFJ1TopMomentSupportTheorem
KernelContigToPFJ1SupportTheorem
KernelContigToPFJ1StructuralSupportTheorem
KernelContigToPFJ1StructuralReducedMultiTheorem
KernelContigToPFJ1StructuralReducedRowsTheorem
KernelContigToPFJ1StructuralReducedRowsTwoTermTheorem
KernelContigToPFJ1StructuralReducedRowsTwoTermPairTheorem
KernelContigToPFJ1StructuralReducedRowsTwoTermPair12CasesTheorem
KernelContigToPFJ1StructuralReducedRowsTwoTermPair01Pair02Theorem
KernelContigToPFJ1StructuralReducedRowsTwoTermPair01Theorem
KernelContigToPFJ1StructuralReducedRowsTwoTermSupportFreeTheorem
KernelContigToPFJ1StructuralReducedRowsFullSparseTwoTermTheorem
KernelContigToPFJ1StructuralReducedRowsFullDominanceSparseTwoTermTheorem
KernelContigToPFJ1StructuralReducedRowsFullDominanceSparseDominanceTwoTermTheorem
KernelContigToPFJ1StructuralReducedRowsAllDominanceTheorem
KernelContigToPFJ1StructuralReducedRowsUniformDominanceTheorem
KernelContigToPFJ1StructuralReducedRowsRowGeometryDominanceTheorem
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceTheorem
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceSideBoundTheorem
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceSeparatedBoundsTheorem
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceDetSideAndMiddleTheorem
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceSplitSideDetAndMiddleTheorem
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceSupportSideAndMiddleTheorem
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceSupportClassSideAndMiddleTheorem
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleOnlyTheorem
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetSignTheorem
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetSupportSplitTheorem
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullZeroBandedTheorem
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTheorem
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedExpandedTheorem
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedProductTheorem
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedBracketSignsTheorem
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedSplitBracketsTheorem
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopSupportSplitBracketsTheorem
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopSupportedMomentTheorem
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedTheorem
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedMomentProductTheorem
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedSplitProductsTheorem
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedLeftProductTheorem
xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedRightProductNonnegative_of_momentNonnegative
xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedSplitProducts_of_leftProduct
xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedSplitProducts_of_leftProduct
kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedSplitProducts_of_leftProduct
xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedLeftProduct
riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedLeftProduct
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedLeftMomentZeroTheorem
xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedLeftProduct_of_leftMomentZero
xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedLeftProduct_of_leftMomentZero
kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedLeftProduct_of_leftMomentZero
xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedLeftMomentZero
riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedLeftMomentZero
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedImpossibleTheorem
xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedLeftMomentZero_of_impossible
xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedLeftMomentZero_of_impossible
kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedLeftMomentZero_of_impossible
xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedImpossible
riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedImpossible
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedGapCollapseTheorem
xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedImpossible_of_gapCollapse
xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedImpossible_of_gapCollapse
kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedImpossible_of_gapCollapse
xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedGapCollapse
riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedGapCollapse
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedOriginalGapCollapseTheorem
xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedGapCollapse_of_originalGapCollapse
xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedGapCollapse_of_originalGapCollapse
kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedGapCollapse_of_originalGapCollapse
xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedOriginalGapCollapse
riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedOriginalGapCollapse
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedInactiveSideSupportTheorem
xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedImpossible_of_inactiveSideSupport
xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedImpossible_of_inactiveSideSupport
kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedImpossible_of_inactiveSideSupport
xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedInactiveSideSupport
riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedInactiveSideSupport
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightInactiveSideSupportTheorem
xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedImpossible_of_rightInactiveSideSupport
xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedImpossible_of_rightInactiveSideSupport
kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedImpossible_of_rightInactiveSideSupport
xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightInactiveSideSupport
riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightInactiveSideSupport
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightActiveExcludedTheorem
xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedRightInactiveSideSupport_of_rightActiveExcluded
xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightInactiveSideSupport_of_rightActiveExcluded
kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightInactiveSideSupport_of_rightActiveExcluded
xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightActiveExcluded
riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightActiveExcluded
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightBandedExcludedTheorem
xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedRightFullExcluded
xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedRightActiveExcluded_of_rightBandedExcluded
xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightActiveExcluded_of_rightBandedExcluded
kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightActiveExcluded_of_rightBandedExcluded
xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightBandedExcluded
riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightBandedExcluded
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedBranchImpossibleTheorem
xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedRightBanded_of_middleBanded
xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedRightBandedExcluded_of_branchImpossible
xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightBandedExcluded_of_branchImpossible
kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightBandedExcluded_of_branchImpossible
xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedBranchImpossible
riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedBranchImpossible
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnUnsupportedTheorem
xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedBranchImpossible_of_middleColumnUnsupported
xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedBranchImpossible_of_middleColumnUnsupported
kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedBranchImpossible_of_middleColumnUnsupported
xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnUnsupported
riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnUnsupported
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnNoStraddleTheorem
xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleColumnUnsupported_of_noStraddle
xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnUnsupported_of_noStraddle
kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnUnsupported_of_noStraddle
xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnNoStraddle
riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnNoStraddle
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleImpossibleTheorem
xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleColumnNoStraddle_of_straddleImpossible
xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnNoStraddle_of_straddleImpossible
kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnNoStraddle_of_straddleImpossible
xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleImpossible
riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleImpossible
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftProductTheorem
xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleColumnStraddleImpossible_of_leftProduct
kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleImpossible_of_leftProduct
xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftProduct
riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftProduct
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftBracketTheorem
xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleColumnStraddleLeftProduct_of_leftBracket
xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftProduct_of_leftBracket
kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftProduct_of_leftBracket
xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftBracket
riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftBracket
```

Lean verifies:

```text
KernelContigToPFLowRankMomentFourBandedCofactorPositiveOneSurvivorSupportTheorem -> XiToeplitzTotalPositive
KernelContigToPFLowRankMomentFourBandedCofactorPositiveOneSurvivorSupportTheorem -> RiemannHypothesis
KernelContigToPFLowRankMomentFourBandedCofactorPositiveFullTheorem -> XiToeplitzTotalPositive
KernelContigToPFLowRankMomentFourBandedCofactorPositiveFullTheorem -> RiemannHypothesis
KernelContigToPFLowRankMomentFourBandedCofactorPositiveFullDetTheorem -> XiToeplitzTotalPositive
KernelContigToPFLowRankMomentFourBandedCofactorPositiveFullDetTheorem -> RiemannHypothesis
KernelContigToPFLowRankMomentFourBandedCofactorThreeFullTheorem -> XiToeplitzTotalPositive
KernelContigToPFLowRankMomentFourBandedCofactorThreeFullTheorem -> RiemannHypothesis
KernelContigToPFLowRankMomentFourBandedCofactorThreeFullBandedTheorem -> XiToeplitzTotalPositive
KernelContigToPFLowRankMomentFourBandedCofactorThreeFullBandedTheorem -> RiemannHypothesis
KernelContigToPFLowRankMomentFourBandedCofactorJ1NonposTheorem -> XiToeplitzTotalPositive
KernelContigToPFLowRankMomentFourBandedCofactorJ1NonposTheorem -> RiemannHypothesis
KernelContigToPFLowRankMomentFourBandedCofactorJ1SupportSplitTheorem -> XiToeplitzTotalPositive
KernelContigToPFLowRankMomentFourBandedCofactorJ1SupportSplitTheorem -> RiemannHypothesis
KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentTheorem -> XiToeplitzTotalPositive
KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentTheorem -> RiemannHypothesis
KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroTheorem -> XiToeplitzTotalPositive
KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroTheorem -> RiemannHypothesis
KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedExpandedTheorem -> XiToeplitzTotalPositive
KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedExpandedTheorem -> RiemannHypothesis
KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedProductTheorem -> XiToeplitzTotalPositive
KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedProductTheorem -> RiemannHypothesis
KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedSignsTheorem -> XiToeplitzTotalPositive
KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedSignsTheorem -> RiemannHypothesis
KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedSplitTheorem -> XiToeplitzTotalPositive
KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedSplitTheorem -> RiemannHypothesis
KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedTopSupportTheorem -> XiToeplitzTotalPositive
KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedTopSupportTheorem -> RiemannHypothesis
KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedTopMomentTheorem -> XiToeplitzTotalPositive
KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedTopMomentTheorem -> RiemannHypothesis
KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedTopMomentMiddleTheorem -> XiToeplitzTotalPositive
KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedTopMomentMiddleTheorem -> RiemannHypothesis
KernelContigToPFJ1TopMomentMiddleProductTheorem -> XiToeplitzTotalPositive
KernelContigToPFJ1TopMomentMiddleProductTheorem -> RiemannHypothesis
KernelContigToPFJ1TopMomentSupportTheorem -> XiToeplitzTotalPositive
KernelContigToPFJ1TopMomentSupportTheorem -> RiemannHypothesis
KernelContigToPFJ1SupportTheorem -> XiToeplitzTotalPositive
KernelContigToPFJ1SupportTheorem -> RiemannHypothesis
KernelContigToPFJ1StructuralSupportTheorem -> XiToeplitzTotalPositive
KernelContigToPFJ1StructuralSupportTheorem -> RiemannHypothesis
KernelContigToPFJ1StructuralReducedMultiTheorem -> XiToeplitzTotalPositive
KernelContigToPFJ1StructuralReducedMultiTheorem -> RiemannHypothesis
KernelContigToPFJ1StructuralReducedRowsTheorem -> XiToeplitzTotalPositive
KernelContigToPFJ1StructuralReducedRowsTheorem -> RiemannHypothesis
KernelContigToPFJ1StructuralReducedRowsTwoTermTheorem -> XiToeplitzTotalPositive
KernelContigToPFJ1StructuralReducedRowsTwoTermTheorem -> RiemannHypothesis
KernelContigToPFJ1StructuralReducedRowsTwoTermPairTheorem -> XiToeplitzTotalPositive
KernelContigToPFJ1StructuralReducedRowsTwoTermPairTheorem -> RiemannHypothesis
KernelContigToPFJ1StructuralReducedRowsTwoTermPair12CasesTheorem -> XiToeplitzTotalPositive
KernelContigToPFJ1StructuralReducedRowsTwoTermPair12CasesTheorem -> RiemannHypothesis
KernelContigToPFJ1StructuralReducedRowsTwoTermPair01Pair02Theorem -> XiToeplitzTotalPositive
KernelContigToPFJ1StructuralReducedRowsTwoTermPair01Pair02Theorem -> RiemannHypothesis
KernelContigToPFJ1StructuralReducedRowsTwoTermPair01Theorem -> XiToeplitzTotalPositive
KernelContigToPFJ1StructuralReducedRowsTwoTermPair01Theorem -> RiemannHypothesis
KernelContigToPFJ1StructuralReducedRowsTwoTermSupportFreeTheorem -> XiToeplitzTotalPositive
KernelContigToPFJ1StructuralReducedRowsTwoTermSupportFreeTheorem -> RiemannHypothesis
KernelContigToPFJ1StructuralReducedRowsFullSparseTwoTermTheorem -> XiToeplitzTotalPositive
KernelContigToPFJ1StructuralReducedRowsFullSparseTwoTermTheorem -> RiemannHypothesis
KernelContigToPFJ1StructuralReducedRowsFullDominanceSparseTwoTermTheorem -> XiToeplitzTotalPositive
KernelContigToPFJ1StructuralReducedRowsFullDominanceSparseTwoTermTheorem -> RiemannHypothesis
KernelContigToPFJ1StructuralReducedRowsFullDominanceSparseDominanceTwoTermTheorem -> XiToeplitzTotalPositive
KernelContigToPFJ1StructuralReducedRowsFullDominanceSparseDominanceTwoTermTheorem -> RiemannHypothesis
KernelContigToPFJ1StructuralReducedRowsAllDominanceTheorem -> XiToeplitzTotalPositive
KernelContigToPFJ1StructuralReducedRowsAllDominanceTheorem -> RiemannHypothesis
KernelContigToPFJ1StructuralReducedRowsUniformDominanceTheorem -> XiToeplitzTotalPositive
KernelContigToPFJ1StructuralReducedRowsUniformDominanceTheorem -> RiemannHypothesis
KernelContigToPFJ1StructuralReducedRowsRowGeometryDominanceTheorem -> XiToeplitzTotalPositive
KernelContigToPFJ1StructuralReducedRowsRowGeometryDominanceTheorem -> RiemannHypothesis
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceTheorem -> XiToeplitzTotalPositive
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceTheorem -> RiemannHypothesis
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceSideBoundTheorem -> XiToeplitzTotalPositive
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceSideBoundTheorem -> RiemannHypothesis
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceSeparatedBoundsTheorem -> XiToeplitzTotalPositive
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceSeparatedBoundsTheorem -> RiemannHypothesis
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceDetSideAndMiddleTheorem -> XiToeplitzTotalPositive
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceDetSideAndMiddleTheorem -> RiemannHypothesis
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceSplitSideDetAndMiddleTheorem -> XiToeplitzTotalPositive
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceSplitSideDetAndMiddleTheorem -> RiemannHypothesis
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceSupportSideAndMiddleTheorem -> XiToeplitzTotalPositive
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceSupportSideAndMiddleTheorem -> RiemannHypothesis
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceSupportClassSideAndMiddleTheorem -> XiToeplitzTotalPositive
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceSupportClassSideAndMiddleTheorem -> RiemannHypothesis
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleOnlyTheorem -> XiToeplitzTotalPositive
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleOnlyTheorem -> RiemannHypothesis
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetSignTheorem -> XiToeplitzTotalPositive
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetSignTheorem -> RiemannHypothesis
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetSupportSplitTheorem -> XiToeplitzTotalPositive
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetSupportSplitTheorem -> RiemannHypothesis
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullZeroBandedTheorem -> XiToeplitzTotalPositive
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullZeroBandedTheorem -> RiemannHypothesis
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTheorem -> XiToeplitzTotalPositive
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTheorem -> RiemannHypothesis
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedExpandedTheorem -> XiToeplitzTotalPositive
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedExpandedTheorem -> RiemannHypothesis
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedProductTheorem -> XiToeplitzTotalPositive
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedProductTheorem -> RiemannHypothesis
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedBracketSignsTheorem -> XiToeplitzTotalPositive
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedBracketSignsTheorem -> RiemannHypothesis
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedSplitBracketsTheorem -> XiToeplitzTotalPositive
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedSplitBracketsTheorem -> RiemannHypothesis
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopSupportSplitBracketsTheorem -> XiToeplitzTotalPositive
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopSupportSplitBracketsTheorem -> RiemannHypothesis
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopSupportedMomentTheorem -> XiToeplitzTotalPositive
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopSupportedMomentTheorem -> RiemannHypothesis
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedTheorem -> XiToeplitzTotalPositive
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedTheorem -> RiemannHypothesis
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedMomentProductTheorem -> XiToeplitzTotalPositive
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedMomentProductTheorem -> RiemannHypothesis
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedSplitProductsTheorem -> XiToeplitzTotalPositive
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedSplitProductsTheorem -> RiemannHypothesis
```

via:

```text
xiToeplitzTotalPositive_of_kernelContigToPFCofactorPositiveSupport
riemannHypothesis_of_kernelContigToPFCofactorPositiveSupport
xiToeplitzTotalPositive_of_kernelContigToPFCofactorPositiveFull
riemannHypothesis_of_kernelContigToPFCofactorPositiveFull
xiToeplitzTotalPositive_of_kernelContigToPFCofactorPositiveFullDet
riemannHypothesis_of_kernelContigToPFCofactorPositiveFullDet
xiToeplitzTotalPositive_of_kernelContigToPFCofactorThreeFull
riemannHypothesis_of_kernelContigToPFCofactorThreeFull
xiToeplitzTotalPositive_of_kernelContigToPFCofactorThreeFullBanded
riemannHypothesis_of_kernelContigToPFCofactorThreeFullBanded
xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1Nonpos
riemannHypothesis_of_kernelContigToPFCofactorJ1Nonpos
xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1SupportSplit
riemannHypothesis_of_kernelContigToPFCofactorJ1SupportSplit
xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1FullMoment
riemannHypothesis_of_kernelContigToPFCofactorJ1FullMoment
xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1FullMomentZero
riemannHypothesis_of_kernelContigToPFCofactorJ1FullMomentZero
xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1BandedExpanded
riemannHypothesis_of_kernelContigToPFCofactorJ1BandedExpanded
xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1BandedProduct
riemannHypothesis_of_kernelContigToPFCofactorJ1BandedProduct
xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1BandedSigns
riemannHypothesis_of_kernelContigToPFCofactorJ1BandedSigns
xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1BandedSplit
riemannHypothesis_of_kernelContigToPFCofactorJ1BandedSplit
xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1BandedTopSupport
riemannHypothesis_of_kernelContigToPFCofactorJ1BandedTopSupport
xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1BandedTopMoment
riemannHypothesis_of_kernelContigToPFCofactorJ1BandedTopMoment
xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1BandedTopMomentMiddle
riemannHypothesis_of_kernelContigToPFCofactorJ1BandedTopMomentMiddle
xiToeplitzTotalPositive_of_kernelContigToPFJ1TopMomentMiddleProduct
riemannHypothesis_of_kernelContigToPFJ1TopMomentMiddleProduct
xiToeplitzTotalPositive_of_kernelContigToPFJ1TopMomentSupport
riemannHypothesis_of_kernelContigToPFJ1TopMomentSupport
xiToeplitzTotalPositive_of_kernelContigToPFJ1Support
riemannHypothesis_of_kernelContigToPFJ1Support
xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralSupport
riemannHypothesis_of_kernelContigToPFJ1StructuralSupport
xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedMulti
riemannHypothesis_of_kernelContigToPFJ1StructuralReducedMulti
xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRows
riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRows
xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsTwoTerm
riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsTwoTerm
kernelContigToPFJ1StructuralReducedRowsTwoTerm_of_pair
xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsTwoTermPair
riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsTwoTermPair
kernelContigToPFJ1StructuralReducedRowsTwoTermPair_of_pair12Cases
xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsTwoTermPair12Cases
riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsTwoTermPair12Cases
kernelContigToPFJ1StructuralReducedRowsTwoTermPair12Cases_of_pair01_pair02
xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsTwoTermPair01Pair02
riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsTwoTermPair01Pair02
kernelContigToPFJ1StructuralReducedRowsTwoTermPair01Pair02_of_pair01
xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsTwoTermPair01
riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsTwoTermPair01
kernelContigToPFJ1StructuralReducedRowsTwoTermPair01_of_supportFree
xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsTwoTermSupportFree
riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsTwoTermSupportFree
kernelContigToPFJ1StructuralReducedRowsTwoTermSupportFree_of_fullSparse
xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsFullSparseTwoTerm
riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsFullSparseTwoTerm
kernelContigToPFJ1StructuralReducedRowsFullSparseTwoTerm_of_fullDominance
xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsFullDominanceSparseTwoTerm
riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsFullDominanceSparseTwoTerm
xiMinorFourBandedCofactorMiddleDominanceSideBound_of_parts
xiMinorFourBandedCofactorMiddleDominanceSideBound_of_separatedBounds
xiMinorFourBandedCofactorMiddleDominance_of_sideBound
xiMinorFourBandedCofactorMiddleDominance_of_sideBoundFromContig
xiMinorFourBandedCofactorMultiRowGeometryDominance_of_middleDominance
xiMinorFourBandedCofactorMultiSupportDominance_of_rowGeometryDominance
xiMinorFourBandedCofactorMultiFullFullFullDominance_of_supportDominance
xiMinorFourBandedCofactorMultiBandedBandedBandedDominance_of_supportDominance
xiMinorFourBandedCofactorMultiZeroRowBandedBandedDominance_of_supportDominance
xiMinorFourBandedCofactorMultiBandedBandedBanded_of_dominance
xiMinorFourBandedCofactorMultiZeroRowBandedBandedTwoTerm_of_dominance
xiMinorFourBandedCofactorReducedMultiSparseRowsTwoTerm_of_dominance
xiMinorFourBandedCofactorReducedMultiSparseDominanceRowsTwoTerm_of_zeroDominance
xiMinorFourBandedCofactorReducedMultiRowsFullDominanceSparseTwoTerm_of_sparseDominance
xiMinorFourBandedCofactorReducedMultiRowsFullDominanceSparseDominanceTwoTerm_of_allDominance
xiMinorFourBandedCofactorReducedMultiRowsAllDominance_of_uniformDominance
kernelContigToPFJ1StructuralReducedRowsFullDominanceSparseTwoTerm_of_sparseDominance
xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsFullDominanceSparseDominanceTwoTerm
riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsFullDominanceSparseDominanceTwoTerm
kernelContigToPFJ1StructuralReducedRowsFullDominanceSparseDominanceTwoTerm_of_allDominance
xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsAllDominance
riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsAllDominance
kernelContigToPFJ1StructuralReducedRowsAllDominance_of_uniformDominance
xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsUniformDominance
riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsUniformDominance
kernelContigToPFJ1StructuralReducedRowsUniformDominance_of_rowGeometryDominance
xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsRowGeometryDominance
riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsRowGeometryDominance
kernelContigToPFJ1StructuralReducedRowsRowGeometryDominance_of_middleDominance
xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominance
riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominance
kernelContigToPFJ1StructuralReducedRowsMiddleDominance_of_sideBound
xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceSideBound
riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceSideBound
kernelContigToPFJ1StructuralReducedRowsMiddleDominanceSideBound_of_separatedBounds
xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceSeparatedBounds
riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceSeparatedBounds
kernelContigToPFJ1StructuralReducedRowsMiddleDominanceSeparatedBounds_of_sideDet
xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceDetSideAndMiddle
riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceDetSideAndMiddle
xiMinorFourBandedCofactorSideDetNonnegative_of_leftRight
xiMinorFourBandedCofactorMiddleDominanceDetSideAndMiddle_of_splitSideDet
kernelContigToPFJ1StructuralReducedRowsMiddleDominanceDetSideAndMiddle_of_splitSideDet
xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceSplitSideDetAndMiddle
riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceSplitSideDetAndMiddle
xiMinorFourBandedCofactorSideDetLeftRightNonnegative_of_support
xiMinorFourBandedCofactorMiddleDominanceSplitSideDetAndMiddle_of_support
kernelContigToPFJ1StructuralReducedRowsMiddleDominanceSplitSideDetAndMiddle_of_supportSide
xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceSupportSideAndMiddle
riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceSupportSideAndMiddle
xiMinorFourBandedCofactorSideDetLeftRightSupportClass_fromBand
xiMinorFourBandedCofactorSideDetLeftRightNonnegative_of_supportClass
xiMinorFourBandedCofactorMiddleDominanceSplitSideDetAndMiddle_of_supportClass
xiMinorFourBandedCofactorMiddleDominanceSupportClassSideAndMiddle_of_middle
kernelContigToPFJ1StructuralReducedRowsMiddleDominanceSplitSideDetAndMiddle_of_supportClassSide
kernelContigToPFJ1StructuralReducedRowsMiddleDominanceSupportClassSideAndMiddle_of_middleOnly
xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceSupportClassSideAndMiddle
riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceSupportClassSideAndMiddle
xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleOnly
riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleOnly
xiMinorFourBandedCofactorMiddleDominanceMiddleUpperBound_of_middleDetNonpositive
kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleOnly_of_middleDetSign
xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetSign
riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetSign
xiMinorFourBandedCofactorMiddleDetNonpositive_of_supportSplit
kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetSign_of_supportSplit
xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetSupportSplit
riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetSupportSplit
xiMinorFourBandedCofactorMiddleDetSupportSplit_of_fullZero
kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetSupportSplit_of_fullZero
xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullZeroBanded
riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullZeroBanded
xiMinorFourBandedCofactorMiddleFullDetZero_of_moment
xiMinorFourBandedCofactorMiddleDetFullZeroBandedNonpositive_of_moment
kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullZeroBanded_of_moment
xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBanded
riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBanded
xiMinorFourBandedCofactorMiddleBandedDetNonpositive_of_expanded
xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedNonpositive_of_expanded
kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBanded_of_expanded
xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedExpanded
riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedExpanded
xiMinorFourBandedCofactorMiddleBandedProductDominance_of_bracketSigns
xiMinorFourBandedCofactorMiddleBandedExpandedNonpositive_of_productDominance
xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedExpanded_of_product
xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedProduct_of_bracketSigns
kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedExpanded_of_product
kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedProduct_of_bracketSigns
xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedProduct
riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedProduct
xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedBracketSigns
riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedBracketSigns
xiMinorFourBandedCofactorMiddleBandedBracketSigns_of_split
xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedBracketSigns_of_split
kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedBracketSigns_of_split
xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedSplitBrackets
riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedSplitBrackets
xiMinorFourBandedCofactorMiddleBandedSplitBrackets_of_topSupportSplit
xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedSplitBrackets_of_topSupportSplit
kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedSplitBrackets_of_topSupportSplit
xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopSupportSplitBrackets
riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopSupportSplitBrackets
xiMinorFourBandedCofactorMiddleBandedTopSupportedSplitBrackets_of_moment
xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopSupportSplitBrackets_of_topSupportedMoment
kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopSupportSplitBrackets_of_topSupportedMoment
xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopSupportedMoment
riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopSupportedMoment
xiMinorFourBandedCofactorMiddleBandedTopUnsupportedSplitBrackets_of_middleSupported
xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopSupportedMoment_of_middleSupported
kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopSupportedMoment_of_middleSupported
xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupported
riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupported
xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedBrackets_of_momentProduct
xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupported_of_momentProduct
kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupported_of_momentProduct
xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedMomentProduct
riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedMomentProduct
xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedMomentProduct_of_splitProducts
xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedMomentProduct_of_splitProducts
kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedMomentProduct_of_splitProducts
xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedSplitProducts
riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedSplitProducts
```

The positive full-support side survivor has now been reduced to the existing
`3 x 3` full-support certificate:

```text
XiMinorThreeFullSupportFromContig
  -> XiMinorFourBandedCofactorPositiveFullDetFromContig
```

via:

```text
xiMinorFourBandedCofactorPositiveFullDet_of_threeFull
```

The positive banded side survivors have now been reduced to the existing
`3 x 3` banded determinant target:

```text
XiMinorThreeBandedDetInequalityFromContig
  -> XiMinorFourBandedCofactorPositiveBandedOneSurvivorInequalityFromContig
```

via:

```text
xiMinorFourBandedCofactorPositiveBandedOneSurvivor_of_threeBandedDet
```

The signed-negative `j = 1` one-survivor case has now been reduced to an
explicit determinant-sign obstruction:

```text
XiMinorFourBandedCofactorOneSurvivorJ1NonposDetFromContig
  -> XiMinorFourBandedCofactorOneSurvivorJ1InequalityFromContig
```

via:

```text
xiMinorFourBandedCofactorOneSurvivorJ1_of_nonposDet
```

That determinant-sign obstruction has now been split by the active middle
cofactor support kind:

```text
XiMinorFourBandedCofactorOneSurvivorJ1FullNonposDetFromContig
XiMinorFourBandedCofactorOneSurvivorJ1BandedNonposDetFromContig
  -> XiMinorFourBandedCofactorOneSurvivorJ1NonposDetFromContig
```

via:

```text
xiMinorFourBandedCofactorOneSurvivorJ1NonposDet_of_supportSplit
```

The full-support middle determinant-sign obstruction has now been rewritten in
moment-index form:

```text
XiMinorFourBandedCofactorOneSurvivorJ1FullMomentNonposDetFromContig
  -> XiMinorFourBandedCofactorOneSurvivorJ1FullNonposDetFromContig
```

via:

```text
xiMinorFourBandedCofactorOneSurvivorJ1FullNonposDet_of_moment
```

The moment-index full-support obstruction has now been sharpened to a
zero-determinant target, and that target is now discharged by support
bookkeeping alone.  The inactive `j = 2` side cofactor cannot coexist with full
support of the middle `j = 1` cofactor and the global lower-right support.

```text
XiJ1FullSupportImpossibleFromSupport
  -> XiMinorFourBandedCofactorOneSurvivorJ1FullMomentZeroDetFromContig
  -> XiMinorFourBandedCofactorOneSurvivorJ1FullMomentNonposDetFromContig
```

via:

```text
xiJ1FullSupportImpossible_of_support
xiMinorFourBandedCofactorOneSurvivorJ1FullMomentZeroDet_of_impossible
xiMinorFourBandedCofactorOneSurvivorJ1FullMomentZeroDet_of_support
xiMinorFourBandedCofactorOneSurvivorJ1FullMomentNonposDet_of_zero
```

The banded middle determinant obstruction has also been expanded along the
forced sparse entry:

```text
XiMinorFourBandedCofactorOneSurvivorJ1BandedExpandedNonposFromContig
  -> XiMinorFourBandedCofactorOneSurvivorJ1BandedNonposDetFromContig
```

via:

```text
xiMinorFourBandedCofactorOneSurvivorJ1BandedNonposDet_of_expanded
```

The expanded obstruction has now been sharpened to a product-dominance target:

```text
XiMinorFourBandedCofactorOneSurvivorJ1BandedProductDominanceFromContig
  -> XiMinorFourBandedCofactorOneSurvivorJ1BandedExpandedNonposFromContig
```

via:

```text
xiMinorFourBandedCofactorOneSurvivorJ1BandedExpandedNonpos_of_productDominance
```

The product-dominance target has now been split into two signed `2 x 2`
brackets:

```text
XiMinorFourBandedCofactorOneSurvivorJ1BandedBracketSignsFromContig
  -> XiMinorFourBandedCofactorOneSurvivorJ1BandedProductDominanceFromContig
```

via:

```text
xiMinorFourBandedCofactorOneSurvivorJ1BandedProductDominance_of_bracketSigns
```

Those two signed brackets have now been split into separate named targets:

```text
XiMinorFourBandedCofactorOneSurvivorJ1BandedLeftBracketNonposFromContig
XiMinorFourBandedCofactorOneSurvivorJ1BandedRightBracketNonnegFromContig
  -> XiMinorFourBandedCofactorOneSurvivorJ1BandedSplitBracketsFromContig
  -> XiMinorFourBandedCofactorOneSurvivorJ1BandedBracketSignsFromContig
```

via:

```text
xiMinorFourBandedCofactorOneSurvivorJ1BandedBracketSigns_of_split
```

The split bracket target has now been decomposed by whether the top row of the
two `2 x 2` brackets supports the far-right cofactor column:

```text
XiMinorFourBandedCofactorOneSurvivorJ1BandedTopSupportedSplitBracketsFromContig
XiMinorFourBandedCofactorOneSurvivorJ1BandedTopUnsupportedSplitBracketsFromContig
  -> XiMinorFourBandedCofactorOneSurvivorJ1BandedTopSupportSplitBracketsFromContig
  -> XiMinorFourBandedCofactorOneSurvivorJ1BandedSplitBracketsFromContig
```

via:

```text
xiMinorFourBandedCofactorOneSurvivorJ1BandedSplitBrackets_of_topSupportSplit
```

The top-supported branch was previously rewritten into moment-gap form, but
the support bookkeeping is stronger: that branch cannot occur under the
inactive side-cofactor hypotheses.  The inactive `j = 2` side cofactor
contradicts the banded `j = 1` support pattern once the far-right cofactor
column is supported in the first bracket row.

```text
XiJ1TopSupportedImpossibleFromSupport
  -> XiMinorFourBandedCofactorOneSurvivorJ1BandedTopSupportedSplitBracketsFromContig
```

via:

```text
xiJ1TopSupportedImpossible_of_support
xiJ1TopSupportedSplitBrackets_of_impossible
xiJ1TopSupportedSplitBrackets_of_support
```

The top-unsupported branch has also been reduced to its middle-supported
subcase.  If the middle cofactor column is unsupported in the first bracket row,
the needed signs follow from forced zero entries and entry nonnegativity:

```text
XiMinorFourBandedCofactorOneSurvivorJ1BandedTopUnsupportedMiddleSupportedBracketsFromContig
  -> XiMinorFourBandedCofactorOneSurvivorJ1BandedTopUnsupportedSplitBracketsFromContig
```

via:

```text
xiMinorFourBandedCofactorOneSurvivorJ1BandedTopUnsupportedSplitBrackets_of_middleSupported
```

The middle-supported top-unsupported subcase was first exposed as a
moment-product obstruction, but the support bookkeeping is stronger: that
configuration cannot occur.  The inactive `j = 2` side cofactor contradicts the
banded `j = 1` support pattern and the global lower-right support.

```text
XiJ1TopUnsupportedMiddleSupportedImpossibleFromSupport
  -> XiJ1TopUnsupportedMiddleSupportedBracketsFromContig
  -> XiMinorFourBandedCofactorOneSurvivorJ1BandedTopUnsupportedMiddleSupportedBracketsFromContig
  -> XiMinorFourBandedCofactorOneSurvivorJ1BandedTopUnsupportedSplitBracketsFromContig
```

via:

```text
xiJ1TopUnsupportedMiddleSupportedImpossible_of_support
xiJ1TopUnsupportedMiddleSupportedBrackets_of_impossible
xiJ1TopUnsupportedMiddleSupportedBrackets_of_support
xiMinorFourBandedCofactorOneSurvivorJ1BandedTopUnsupportedSplitBrackets_of_support
```

The multi-survivor table is now split into a support-kind classification target
and a reduced table.  The reduced table only has to cover three kind triples:

```text
(full, full, full)
(banded, banded, banded)
(zeroRow, banded, banded)
```

The bridge is checked:

```text
support bookkeeping
  -> XiMinorFourBandedCofactorMultiSurvivorPair12KindCasesFromSupport

support bookkeeping
  -> XiMinorFourBandedCofactorMultiSurvivorPair02KindCasesFromSupport

support bookkeeping
  -> XiMinorFourBandedCofactorMultiSurvivorPair01KindCasesFromSupport

support bookkeeping
  -> XiMinorFourBandedCofactorMultiSurvivorPair01KindOnlyReductionFromSupport

XiMinorFourBandedCofactorMultiSurvivorPair01KindOnlyReductionFromSupport
  -> XiMinorFourBandedCofactorMultiSurvivorPair01Pair02KindReductionFromSupport

XiMinorFourBandedCofactorMultiSurvivorPair01Pair02KindReductionFromSupport
  -> XiMinorFourBandedCofactorMultiSurvivorPair12CasesKindReductionFromSupport

XiMinorFourBandedCofactorMultiSurvivorPair12KindCasesFromSupport
  -> XiMinorFourBandedCofactorMultiSurvivorPair12KindReductionFromSupport

XiMinorFourBandedCofactorMultiSurvivorPair12CasesKindReductionFromSupport
  -> XiMinorFourBandedCofactorMultiSurvivorPairKindReductionFromSupport

XiMinorFourBandedCofactorMultiSurvivorPairKindReductionFromSupport
  -> XiMinorFourBandedCofactorMultiSurvivorKindReductionFromSupport

XiMinorFourBandedCofactorReducedMultiRowsTwoTermFromContig
XiMinorFourBandedCofactorReducedMultiRowsFullSparseTwoTermFromContig
  -> XiMinorFourBandedCofactorReducedMultiRowsTwoTermFromContig

XiMinorFourBandedCofactorReducedMultiRowsFullDominanceSparseTwoTermFromContig
  -> XiMinorFourBandedCofactorReducedMultiRowsFullSparseTwoTermFromContig

XiMinorFourBandedCofactorReducedMultiSparseDominanceRowsTwoTermFromContig
  -> XiMinorFourBandedCofactorReducedMultiSparseRowsTwoTermFromContig

XiMinorFourBandedCofactorReducedMultiSparseDominanceRowsDominanceFromContig
  -> XiMinorFourBandedCofactorReducedMultiSparseDominanceRowsTwoTermFromContig

XiMinorFourBandedCofactorReducedMultiRowsFullDominanceSparseDominanceTwoTermFromContig
  -> XiMinorFourBandedCofactorReducedMultiRowsFullDominanceSparseTwoTermFromContig

XiMinorFourBandedCofactorReducedMultiRowsAllDominanceFromContig
  -> XiMinorFourBandedCofactorReducedMultiRowsFullDominanceSparseDominanceTwoTermFromContig

XiMinorFourBandedCofactorReducedMultiRowsUniformDominanceFromContig
  -> XiMinorFourBandedCofactorReducedMultiRowsAllDominanceFromContig

XiMinorFourBandedCofactorReducedMultiRowsRowGeometryDominanceFromContig
  -> XiMinorFourBandedCofactorReducedMultiRowsUniformDominanceFromContig

XiMinorFourBandedCofactorMiddleDominanceFromContig
  -> XiMinorFourBandedCofactorReducedMultiRowsRowGeometryDominanceFromContig

XiMinorFourBandedCofactorMiddleDominanceSideBoundFromContig
  -> XiMinorFourBandedCofactorMiddleDominanceFromContig

XiMinorFourBandedCofactorMiddleDominanceSeparatedBoundsFromContig
  -> XiMinorFourBandedCofactorMiddleDominanceSideBoundFromContig

XiMinorFourBandedCofactorReducedMultiRowsTwoTermFromContig
  -> XiMinorFourBandedCofactorReducedMultiRowsFromContig

XiMinorFourBandedCofactorReducedMultiRowsFromContig
  -> XiMinorFourBandedCofactorReducedMultiSurvivorCaseTableInequalityFromContig

XiMinorFourBandedCofactorMultiSurvivorKindReductionFromSupport
XiMinorFourBandedCofactorReducedMultiSurvivorCaseTableInequalityFromContig
  -> XiMinorFourBandedCofactorMultiSurvivorCaseTableInequalityFromContig
```

via:

```text
xiMinorFourBandedCofactorMultiSurvivorPair12FullFullLeftFull_of_support
xiMinorFourBandedCofactorMultiSurvivorPair12FullBandedImpossible_of_support
xiMinorFourBandedCofactorMultiSurvivorPair12BandedFullImpossible_of_support
xiMinorFourBandedCofactorMultiSurvivorPair12BandedBandedLeftReduced_of_support
xiMinorFourBandedCofactorMultiSurvivorPair12KindCases_of_support
xiMinorFourBandedCofactorMultiSurvivorPair12CasesKindReduction_of_pair01_pair02
xiMinorFourBandedCofactorMultiSurvivorPair02FullFullMiddleFull_of_support
xiMinorFourBandedCofactorMultiSurvivorPair02FullBandedImpossible_of_support
xiMinorFourBandedCofactorMultiSurvivorPair02BandedFullImpossible_of_support
xiMinorFourBandedCofactorMultiSurvivorPair02BandedBandedMiddleBanded_of_support
xiMinorFourBandedCofactorMultiSurvivorPair02KindCases_of_support
xiMinorFourBandedCofactorMultiSurvivorPair02KindReduction_of_cases
xiMinorFourBandedCofactorMultiSurvivorPair01Pair02KindReduction_of_pair01
xiMinorFourBandedCofactorMultiSurvivorPair01FullFullRightFull_of_support
xiMinorFourBandedCofactorMultiSurvivorPair01FullBandedImpossible_of_support
xiMinorFourBandedCofactorMultiSurvivorPair01BandedFullImpossible_of_support
xiMinorFourBandedCofactorMultiSurvivorPair01BandedBandedRightBanded_of_support
xiMinorFourBandedCofactorMultiSurvivorPair01KindCases_of_support
xiMinorFourBandedCofactorMultiSurvivorPair01KindReduction_of_cases
xiMinorFourBandedCofactorMultiSurvivorPair01KindOnlyReduction_of_support
xiMinorFourBandedCofactorMultiSurvivorPair12KindReduction_of_cases
xiMinorFourBandedCofactorMultiSurvivorPairKindReduction_of_pair12Cases
xiMinorFourBandedCofactorMultiSurvivorKindReduction_of_pair
xiMinorFourBandedCofactorMultiZeroRowBandedBanded_of_twoTerm
xiMinorFourBandedCofactorMiddleDominanceSideBound_of_parts
xiMinorFourBandedCofactorMiddleDominanceSideBound_of_separatedBounds
xiMinorFourBandedCofactorMiddleDominance_of_sideBound
xiMinorFourBandedCofactorMiddleDominance_of_sideBoundFromContig
xiMinorFourBandedCofactorMultiRowGeometryDominance_of_middleDominance
xiMinorFourBandedCofactorMultiSupportDominance_of_rowGeometryDominance
xiMinorFourBandedCofactorMultiFullFullFullDominance_of_supportDominance
xiMinorFourBandedCofactorMultiBandedBandedBandedDominance_of_supportDominance
xiMinorFourBandedCofactorMultiZeroRowBandedBandedDominance_of_supportDominance
xiMinorFourBandedCofactorMultiFullFullFull_of_dominance
xiMinorFourBandedCofactorMultiBandedBandedBanded_of_dominance
xiMinorFourBandedCofactorMultiZeroRowBandedBandedTwoTerm_of_dominance
xiMinorFourBandedCofactorReducedMultiSparseRowsTwoTerm_of_dominance
xiMinorFourBandedCofactorReducedMultiSparseDominanceRowsTwoTerm_of_zeroDominance
xiMinorFourBandedCofactorReducedMultiRowsFullDominanceSparseTwoTerm_of_sparseDominance
xiMinorFourBandedCofactorReducedMultiRowsFullDominanceSparseDominanceTwoTerm_of_allDominance
xiMinorFourBandedCofactorReducedMultiRowsAllDominance_of_uniformDominance
xiMinorFourBandedCofactorReducedMultiRowsUniformDominance_of_rowGeometryDominance
xiMinorFourBandedCofactorReducedMultiRowsFullSparseTwoTerm_of_dominance
xiMinorFourBandedCofactorReducedMultiRowsTwoTerm_of_fullSparse
xiMinorFourBandedCofactorReducedMultiRows_of_twoTerm
xiMinorFourBandedCofactorReducedMultiSurvivor_of_rows
xiMinorFourBandedCofactorMultiSurvivorCaseTable_of_reduced
```

The sharpest RH-closing bundle now has no multi-survivor support-kind
classification assumption: pair-`01`, pair-`02`, pair-`12`, and all
signed-negative `j = 1` one-survivor support cases are discharged by support
bookkeeping.  The all-full row is reduced to the exact middle-cofactor
dominance inequality, while the sparse two-term row package remains explicit:

```text
KernelContigToPFJ1StructuralReducedRowsFullDominanceSparseTwoTermTheorem
  -> XiToeplitzTotalPositive
  -> RiemannHypothesis
```

After the sparse-dominance split, the sharper RH-closing bundle is:

```text
KernelContigToPFJ1StructuralReducedRowsFullDominanceSparseDominanceTwoTermTheorem
  -> XiToeplitzTotalPositive
  -> RiemannHypothesis
```

After converting the zero-row two-term row into dominance form, the sharper
RH-closing bundle is:

```text
KernelContigToPFJ1StructuralReducedRowsAllDominanceTheorem
  -> XiToeplitzTotalPositive
  -> RiemannHypothesis
```

After unifying the row dominance shape across support classes, the sharper
RH-closing bundle is:

```text
KernelContigToPFJ1StructuralReducedRowsUniformDominanceTheorem
  -> XiToeplitzTotalPositive
  -> RiemannHypothesis
```

After dropping the support predicates from the dominance statement, the
sharper RH-closing bundle is:

```text
KernelContigToPFJ1StructuralReducedRowsRowGeometryDominanceTheorem
  -> XiToeplitzTotalPositive
  -> RiemannHypothesis
```

After naming the bare middle-cofactor inequality, the sharper RH-closing bundle
is:

```text
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceTheorem
  -> XiToeplitzTotalPositive
  -> RiemannHypothesis
```

After splitting the inequality into side nonnegativity plus a middle-term
upper bound, the sharper RH-closing bundle is:

```text
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceSideBoundTheorem
  -> XiToeplitzTotalPositive
  -> RiemannHypothesis
```

After separating the entry-sign part of side nonnegativity from the side
cofactor determinants, the sharper RH-closing bundle is:

```text
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceDetSideAndMiddleTheorem
  -> XiToeplitzTotalPositive
  -> RiemannHypothesis
```

Lean now verifies that contiguous total positivity supplies the nonnegative
entry factors in the side terms.  The next useful proof step is therefore to
attack the determinant-side and middle estimates directly:

```text
XiMinorFourBandedCofactorSideDetNonnegativeFromContig
XiMinorFourBandedCofactorMiddleDominanceMiddleUpperBoundFromContig
```

After splitting the two side cofactors, the sharpest RH-closing bundle is now:

```text
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceSplitSideDetAndMiddleTheorem
  -> XiToeplitzTotalPositive
  -> RiemannHypothesis
```

The current determinant-side frontier is:

```text
XiMinorFourBandedCofactorSideDetLeftNonnegativeFromContig
XiMinorFourBandedCofactorSideDetRightNonnegativeFromContig
XiMinorFourBandedCofactorMiddleDominanceMiddleUpperBoundFromContig
```

Lean now verifies that the two side determinant signs follow from the existing
`3 x 3` full-support and banded determinant inputs once the side cofactors are
classified as full or banded.  The sharpest RH-closing bundle is therefore:

```text
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceSupportSideAndMiddleTheorem
  -> XiToeplitzTotalPositive
  -> RiemannHypothesis
```

The current reduced frontier is:

```text
XiMinorFourBandedCofactorSideDetLeftRightSupportFromContig
XiMinorFourBandedCofactorMiddleDominanceMiddleUpperBoundFromContig
```

The full-or-banded side-support frontier was too strong: zero-row and
zero-column side cofactors are possible, and they have determinant zero.  Lean
now verifies the broader side support-class route:

```text
XiMinorFourBandedCofactorSideDetLeftRightSupportClassFromContig
  -> XiMinorFourBandedCofactorSideDetLeftRightNonnegativeFromContig
```

The side support-class condition itself is proved from the existing
`j = 0` and `j = 2` support-class lemmas.  Therefore the sharpest RH-closing
bundle is now:

```text
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleOnlyTheorem
  -> XiToeplitzTotalPositive
  -> RiemannHypothesis
```

The current frontier is reduced to a single named estimate:

```text
XiMinorFourBandedCofactorMiddleDominanceMiddleUpperBoundFromContig
```

The middle upper-bound estimate is now reduced to the sign of the middle
cofactor determinant.  Lean verifies that if the middle `C1` determinant is
nonpositive, then the middle term is nonpositive while the side terms are
nonnegative by the already-proved support-class route.  The sharpest
RH-closing bundle is now:

```text
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetSignTheorem
  -> XiToeplitzTotalPositive
  -> RiemannHypothesis
```

The current frontier is:

```text
XiMinorFourBandedCofactorMiddleDetNonpositiveFromContig
```

The middle determinant sign condition is now split by the already-proved
support classification of the `j = 1` cofactor.  Zero-row and zero-column cases
give determinant zero, so only full-support and banded-support active cases
remain.  The sharpest RH-closing bundle is now:

```text
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetSupportSplitTheorem
  -> XiToeplitzTotalPositive
  -> RiemannHypothesis
```

The current frontier is:

```text
XiMinorFourBandedCofactorMiddleFullDetNonpositiveFromContig
XiMinorFourBandedCofactorMiddleBandedDetNonpositiveFromContig
```

The full-support branch has now been sharpened into moment coordinates, the
top-supported banded branch has been rewritten into moment-gap coordinates, and
the remaining top-unsupported/middle-supported branch has been split into two
moment-product sign conditions, the right product sign has now been discharged
by moment nonnegativity from contiguous `1 x 1` positivity, and the left
product sign has been sharpened to vanishing of one of its two moment factors.
In the full-support case, every Toeplitz entry in
the middle cofactor rewrites to `XiMomentCoeff (row - col)`.  In the banded
case, the support inequality `rows[1] < cols[3]` kills the top-right entry of
the `3 x 3` middle cofactor; product dominance implies the sparse expansion,
bracket signs imply product dominance using contiguous `1 x 1` nonnegativity
of the two top-row Toeplitz prefactors, the left/right split separates the two
bracket claims, the top-support split isolates the fully supported moment-gap
branch from the zero-entry branch, full top support rewrites all six bracket
entries to moment coefficients, if the middle column is also unsupported in the
top row the remaining signs follow from two forced zeros plus entry
nonnegativity, and in the remaining middle-supported subcase the far-right top
entry is zero so both brackets reduce to signed moment products.  The final
split separates the left product nonpositivity from the right product
nonnegativity; the right product is now automatic, the left product was reduced
to a moment-vanishing target, and the branch-exclusion step is now expressed as
support-context recovery.  The right-side full-support case is automatically
excluded: it would force `cols 3 <= rows 1`, while the middle banded support
condition gives `rows 1 < cols 3`.  The right-side banded case is not a
separate geometric accident: it is forced by the same three inequalities as the
middle banded support condition.  The branch-collapse target has now been
sharpened to a native Toeplitz bracket obstruction inside the straddle branch.
In the interval `cols 2 <= rows 1 < cols 3`, the upper-right bracket entry is
zero, so the left bracket reduces to the left moment product.  Since the two
left-product factors are strictly positive from the kernel representation, a
nonpositive left bracket collapses the branch.  The straddle bracket target is
also now connected back to the older top-unsupported/middle-supported bracket
package: `xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleColumnStraddleLeftBracket_of_middleSupported`
restricts that broader package to the straddle subcase, and
`xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftBracket_of_middleSupported`
lifts the same restriction to the support-split package, while
`kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftBracket_of_middleSupported`
promotes the restriction to the theorem-target level.  This is a reintegration
link, not a discharge of the bracket target.  The older straddle left-product
target and the native left-bracket target are now formally interchangeable in
this top-unsupported branch.  The reverse bridge is
`xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleColumnStraddleLeftBracket_of_leftProduct`;
`xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftBracket_of_leftProduct`
lifts it to the support-split package, and
`kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftBracket_of_leftProduct`
lifts it to the theorem-target level.  This equivalence uses the already proved
structural zero of the upper-right entry; it does not prove either sign target
from contiguity.  A subsequent consistency check rejects this route as an RH
frontier: the concrete selectors `rows = (0, 2, 4, 6)` and
`cols = (0, 1, 2, 5)` satisfy all top-unsupported straddle hypotheses, while
the kernel representation makes both left-product factors strictly positive.
Lean now records the contradiction in
`not_xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleColumnStraddleLeftProduct_of_positive_and_contig`,
and lifts it to both theorem bundles through
`kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftProduct_false`
and
`kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftBracket_false`.
The following implication remains logically derivable, but its source bundle is
uninhabited and therefore must not be treated as a viable RH-closing target:

```text
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftBracketTheorem
  -> XiToeplitzTotalPositive
  -> RiemannHypothesis
```

The honest route returns to the last cancellation-aware bundle:

```text
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleOnlyTheorem
  -> XiToeplitzTotalPositive
  -> RiemannHypothesis
```

The current frontier is again the single middle-term upper bound, which permits
cancellation against the two side cofactors instead of demanding the false sign
of the middle cofactor by itself:

```text
XiMinorFourBandedCofactorMiddleDominanceMiddleUpperBoundFromContig
```

The middle upper bound is now split at the only sign boundary that preserves
the required cancellation.  When `det C1 <= 0`, contiguous `1 x 1` positivity
and the already-proved side support-class determinant signs make the bound
automatic.  Therefore the only genuinely new case is `0 < det C1`, named:

```text
XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetCancellationFromContig
```

Lean verifies both directions under the existing `3 x 3` theorem fields:

```text
xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetCancellation_of_middleUpperBound
xiMinorFourBandedCofactorMiddleDominanceMiddleUpperBound_of_positiveMiddleDetCancellation
```

The current nonvacuous RH-closing bundle is:

```text
KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetCancellationTheorem
  -> KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleOnlyTheorem
  -> XiToeplitzTotalPositive
  -> RiemannHypothesis
```

This is an exact branch reduction, not a proof of the cancellation estimate.
It removes the automatically controlled nonpositive-middle branch and leaves
the weighted positive-cofactor comparison as the active frontier.  Any next
condensation, Plucker, planar-network, or compound-minor condition must imply
this named positive-branch estimate without forcing `det C1 <= 0`.

A fixed-pivot Dodgson reduction is not yet honest here because contiguous total
positivity is non-strict: the central `2 x 2` pivot may vanish.  The next exact,
division-free condition instead allocates the positive weighted middle cofactor
between the two side terms:

```text
XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetSideAllocationFromContig
```

It asks for nonnegative `leftShare` and `rightShare` with

```text
leftShare + rightShare = A01 * det C1
leftShare  <= A00 * det C0
rightShare <= A02 * det C2
```

Lean verifies that allocation implies cancellation by addition, and conversely
constructs an allocation from cancellation using the existing nonnegative side
terms: fill the left side with the whole middle term when possible; otherwise
fill it to capacity and send the exact remainder to the right.  Thus the two
conditions are equivalent under the existing theorem fields:

```text
xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetCancellation_of_sideAllocation
xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetSideAllocation_of_cancellation
```

The active verified chain is now:

```text
KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetSideAllocationTheorem
  -> KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetCancellationTheorem
  -> KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleOnlyTheorem
  -> XiToeplitzTotalPositive
  -> RiemannHypothesis
```

The remaining frontier is to construct these two shares from mathematical
structure rather than from the desired inequality.  This is the appropriate
interface for a planar-network path injection, a compound-minor flow, or a
support-stratified condensation argument that handles zero pivots explicitly.

A stronger, concrete compound-minor route now plugs into that allocation
interface.  In the positive-middle branch write:

```text
M = A01 * det C1
L = A00 * det C0
R = A02 * det C2
```

The named geometric-mean condition is:

```text
XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetGeometricMeanFromContig
```

and asks for `M^2 <= L * R`.  Since the existing side route proves
`0 <= L` and `0 <= R`, Lean verifies
`M^2 <= L * R <= (L + R)^2`, hence `M <= L + R`.  This supplies the
side-allocation target without any division or pivot nonvanishing hypothesis:

```text
XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetGeometricMeanFromContig
  -> XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetSideAllocationFromContig
  -> XiToeplitzTotalPositive
  -> RiemannHypothesis
```

The verified Lean bridges are
`xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetCancellation_of_geometricMean`
and
`xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetSideAllocation_of_geometricMean`.
At the theorem-target level,
`KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetGeometricMeanTheorem`
feeds the side-allocation bundle through
`kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetSideAllocation_of_geometricMean`.

This is a stronger candidate condition, not a proved consequence of contiguous
positivity.  Its mathematical attraction is that it separates into a
compound-minor product comparison, a plausible target for Cauchy-Binet,
Lorentzian, or planar-network methods, while retaining all zero-pivot cases.

The geometric-mean candidate now has a still more structured factorization:

```text
XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetFactorizedLogConvexityFromContig
```

In the positive-middle branch it asks simultaneously for:

```text
A01^2      <= A00 * A02
(det C1)^2 <= det C0 * det C2
```

Multiplication gives the geometric-mean condition exactly.  Lean verifies this
in `xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetGeometricMean_of_factorizedLogConvexity` and lifts it through
`KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetFactorizedLogConvexityTheorem`.
The theorem-target adapter is
`kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetGeometricMean_of_factorizedLogConvexity`.

```text
FactorizedLogConvexityTheorem
  -> GeometricMeanTheorem
  -> SideAllocationTheorem
  -> XiToeplitzTotalPositive
  -> RiemannHypothesis
```

This is also a stronger candidate, not an established Xi theorem.  It isolates
two familiar directions: log-convexity of the top-row Toeplitz factors and
log-convexity of the maximal cofactor-minor sequence.  On the supported part
of the row, the first becomes a signed Xi moment inequality.  The second is the
new compound-matrix question that a Cauchy-Binet, Lorentzian, or planar-network
construction would need to settle.

The global geometric-mean and factorized routes are too rigid in one support
class: when `rows 0 < cols 2`, the right top-row Toeplitz entry is structurally
zero, so a positive middle cofactor cannot be absorbed by a product involving
that right side.  The correct support-aware payload is now:

```text
XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightSupportSplitFromContig
```

It pairs two different conditions:

```text
rows 0 < cols 2  -> left dominance: M <= L
cols 2 <= rows 0 -> geometric mean: M^2 <= L * R
```

Lean verifies that this support split implies the positive-middle cancellation
condition in
`xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetCancellation_of_topRightSupportSplit`.
The theorem target
`KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightSupportSplitTheorem`
then feeds the existing chain through
`kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetCancellation_of_topRightSupportSplit`:

```text
TopRightSupportSplitTheorem
  -> PositiveMiddleDetCancellationTheorem
  -> XiToeplitzTotalPositive
  -> RiemannHypothesis
```

This is the current support-compatible compound-minor frontier.  The remaining
mathematics is a one-sided cofactor dominance proof in the top-right-zero
branch and a geometric-mean or factorized compound-minor proof in the
top-right-supported branch.

The top-right-zero branch now has a final automatic split.  If
`rows 0 < cols 1`, then `A01 = 0`, so its left dominance inequality follows
from the already verified nonnegative left side.  Therefore the only active
left interval is:

```text
cols 1 <= rows 0 < cols 2
```

The reduced payload is
`XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightThreeWaySplitFromContig`:

```text
cols 1 <= rows 0 < cols 2 -> M <= L
cols 2 <= rows 0          -> M^2 <= L * R
```

Lean verifies the automatic `A01 = 0` branch through
`xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightUnsupportedLeftDominance_of_middleSupported`,
and then derives the previous two-way split with
`xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightSupportSplit_of_threeWay`.
At the theorem-target level,
`KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightThreeWaySplitTheorem`
feeds the chain through
`kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightSupportSplit_of_threeWay`:

```text
TopRightThreeWaySplitTheorem
  -> TopRightSupportSplitTheorem
  -> PositiveMiddleDetCancellationTheorem
  -> XiToeplitzTotalPositive
  -> RiemannHypothesis
```

This is the current minimal support-aware frontier: prove a left cofactor
dominance relation only in the middle-supported/top-right-zero interval, and
prove a compound-minor geometric mean relation where the top-right side is
supported.

On the remaining left interval the two top-row entries are both supported, so
the left dominance condition is now rewritten in moment/cofactor coordinates:

```text
XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightUnsupportedMiddleSupportedMomentCofactorRatioFromContig

XiMomentCoeff(rows 0 - cols 1) * det C1
  <= XiMomentCoeff(rows 0 - cols 0) * det C0
```

This is a division-free compound-ratio condition between adjacent cofactor
minors and explicit signed Xi moments.  Lean verifies that it is exactly the
entry-level left-dominance condition on this interval through
`xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightUnsupportedMiddleSupportedLeftDominance_of_momentCofactorRatio`.
The combined moment payload produces the preceding three-way support payload
through
`xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightThreeWaySplit_of_momentCofactorRatio`.

The combined payload is
`XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightMomentCofactorRatioThreeWaySplitFromContig`:

```text
moment/cofactor ratio on cols 1 <= rows 0 < cols 2
geometric mean on cols 2 <= rows 0
```

At the theorem-target level,
`KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightMomentCofactorRatioThreeWaySplitTheorem`
feeds the preceding support target through
`kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightThreeWaySplit_of_momentCofactorRatio`.

```text
MomentCofactorRatioThreeWaySplitTheorem
  -> TopRightThreeWaySplitTheorem
  -> TopRightSupportSplitTheorem
  -> XiToeplitzTotalPositive
  -> RiemannHypothesis
```

The division-free form also has a quotient-normalized presentation:
`XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightUnsupportedMiddleSupportedNormalizedMomentCofactorRatioFromContig`:

```text
0 < det C0
det C1 / det C0
  <= XiMomentCoeff(rows 0 - cols 0) /
       XiMomentCoeff(rows 0 - cols 1)
```

It is imposed only on the same active interval
`cols 1 <= rows 0 < cols 2`, and only when `det C1 > 0`. Contiguous total
positivity alone does not establish this condition. Under the already-required
positive kernel representation, however, it is equivalent to the division-free
cross-product condition: the latter forces `det C0 > 0` because its left side
is strictly positive.

Lean verifies the exact implication from this normalized condition to the
division-free cross-product condition using positive denominators:

```text
xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightUnsupportedMiddleSupportedMomentCofactorRatio_of_normalized
xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightUnsupportedMiddleSupportedNormalizedMomentCofactorRatio_of_momentCofactorRatio

XiMomentCoeffPositive
  + NormalizedMomentCofactorRatio
  <-> MomentCofactorRatio
```

The matching three-way equivalence is formalized by
`xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightMomentCofactorRatioThreeWaySplit_of_normalized`
and
`xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightNormalizedMomentCofactorRatioThreeWaySplit_of_momentCofactorRatio`.

The moment denominators are positive by the already formalized Polya positive
kernel representation. The combined normalized payload is
`XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightNormalizedMomentCofactorRatioThreeWaySplitFromContig`, with the same supported
geometric-mean branch. Its theorem target is
`KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightNormalizedMomentCofactorRatioThreeWaySplitTheorem`. Lean verifies
target-level conversion in both directions:

```text
NormalizedMomentCofactorRatioThreeWaySplitTheorem
  <-> MomentCofactorRatioThreeWaySplitTheorem
```

The normalized presentation feeds the existing PF/RH route through
`kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightMomentCofactorRatioThreeWaySplit_of_normalizedMomentCofactorRatio`,
`xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightNormalizedMomentCofactorRatioThreeWaySplit`,
and
`riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightNormalizedMomentCofactorRatioThreeWaySplit`.
The converse target conversion is
`kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightNormalizedMomentCofactorRatioThreeWaySplit_of_momentCofactorRatio`.

The active left-side mathematical target is therefore a cofactor-ratio
monotonicity statement in these explicit moment coordinates, not an arbitrary
unsigned determinant inequality.

A new concrete sufficient condition records the exact form of derivation that
a Cauchy-Binet or planar-network proof would need to provide. The reusable
certificate predicate `XiContigMinorPositivePolynomial x` requires an identity

```text
x = sum_i c_i * product_j Delta(k_ij, m_ij)
```

where every `c_i` is a natural number and every `Delta(k,m)` is a contiguous
Toeplitz minor. It is deliberately subtraction-free: contiguous positivity
makes every summand nonnegative, so Lean proves
`xiContigMinorPositivePolynomial_nonneg` without any division or strict-pivot
assumption.

For the active branch the certified quantity is exactly

```text
XiMomentCoeff(rows 0 - cols 0) * det C0
  - XiMomentCoeff(rows 0 - cols 1) * det C1.
```

The named condition
`XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightUnsupportedMiddleSupportedPositivePolynomialCertificateFromContig`
asks for this certificate only when `cols 1 <= rows 0 < cols 2` and
`det C1 > 0`. Lean verifies that it implies the active cofactor-ratio target
through
`xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightUnsupportedMiddleSupportedMomentCofactorRatio_of_positivePolynomialCertificate`.

This is an unproved, stronger derivation route, not a claim that contiguous
positivity automatically supplies such an identity. It has independent
mathematical content: coefficients must be natural and every factor must be a
specified contiguous minor, excluding a disguised use of the desired
inequality as a coefficient.

Bundling this left certificate with the already-needed supported geometric
branch gives
`XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightPositivePolynomialCertificateThreeWaySplitFromContig`.
At theorem-target level,
`KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightPositivePolynomialCertificateThreeWaySplitTheorem`
feeds the checked chain:

```text
PositivePolynomialCertificateThreeWaySplitTheorem
  -> MomentCofactorRatioThreeWaySplitTheorem
  -> TopRightThreeWaySplitTheorem
  -> TopRightSupportSplitTheorem
  -> XiToeplitzTotalPositive
  -> RiemannHypothesis
```

via
`kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightMomentCofactorRatioThreeWaySplit_of_positivePolynomialCertificate`,
`xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightPositivePolynomialCertificateThreeWaySplit`,
and
`riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightPositivePolynomialCertificateThreeWaySplit`.

The certificate program has now discharged its first nontrivial active family.
For consecutive selectors

```text
rows i = q + 1 + i
cols j = q + j
```

the active top row has the required support pattern, and the exact Laplace
identity is

```text
XiMomentCoeff(rows 0 - cols 0) * det C0
  - XiMomentCoeff(rows 0 - cols 1) * det C1
  = XiToeplitzContigMinor 4 1.
```

The right side is already nonnegative from the contiguous ladder. Lean proves
the unshifted identity as the one-term certificate
`xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightUnsupportedMiddleSupportedPositivePolynomialCertificate_contiguousSeed`,
using the finite Laplace identity
`matrix_det_eq_cofactorLeftDifference_of_topRightTwoZero`,
and proves common-translation invariance through
`xiToeplitzEntry_add_left` and
`xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightUnsupportedMiddleSupportedPositivePolynomialCertificate_contiguousShiftedSeed`.
The corresponding direct inequality is also checked by
`xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightUnsupportedMiddleSupportedMomentCofactorRatio_contiguousShiftedSeed`.

This does not cover arbitrary strictly monotone active selectors. It isolates
the next finite problem precisely: extend the one-term consecutive certificate
to row or column gap profiles, likely by a positive expansion into several
contiguous minors rather than a single determinant identity.

## Initial-Column Reduction

The arbitrary-minor upgrade can be reduced further using a classical
lower-triangular criterion. Cryer, *Some properties of totally positive
matrices* (1976), Theorem 4, states that a nonsingular lower-triangular matrix
is totally nonnegative exactly when all of its minors formed from consecutive
initial columns are nonnegative. For Xi Toeplitz truncations, the diagonal is
`XiMomentCoeff 0 > 0` under the Pólya kernel representation, so every finite
lower-triangular truncation is nonsingular.

The new Lean condition is
`XiInitialColumnMinorTotalPositive`:

```text
for every k and strictly increasing rows r:
  det [XiToeplitzEntry(r_i, j)]_(0 <= i,j < k) >= 0.
```

Only the rows are arbitrary; the columns are the fixed initial interval
`0, ..., k - 1`. The Xi-specific lift now has the named form
`XiContigToInitialColumnMinorBridge`:

```text
XiContigToeplitzTotalPositive
  -> XiInitialColumnMinorTotalPositive.
```

The orders `k = 0, 1, 2` are now closed in this route. Order zero is the empty
determinant, order one follows from contiguous `1 x 1` positivity, and the
Pólya kernel representation already proves every arbitrary `2 x 2` Toeplitz
minor through the verified ratio-Monge/full-support certificate route. The
initial-column specialization is formalized as
`XiInitialColumnMinorTwoFromContig` and
`xiInitialColumnMinorTwoFromContig_of_kernelRep`.

Accordingly the only Xi-specific lift left is
`XiInitialColumnMinorGeThreeFromContig`:

```text
for every k >= 3 and strictly increasing rows r:
  XiContigToeplitzTotalPositive
    -> det [XiToeplitzEntry(r_i, j)]_(0 <= i,j < k) >= 0.
```

Lean verifies that the order-two base and this `k >= 3` condition reconstruct
the full initial-column lift through
`xiContigToInitialColumnMinorBridge_of_two_and_geThree`, and packages the
kernel-backed specialization in
`xiContigToInitialColumnMinorBridge_of_kernelRep_and_geThree`.

The order-three interface itself is now isolated as
`XiInitialColumnMinorThreeFromContig`. It follows from the existing global
`3 x 3` certificate family through
`xiInitialColumnMinorThreeFromContig_of_threeCertificates`. In particular,
the already named full-support and banded determinant frontiers supply it via
`xiInitialColumnMinorThreeFromContig_of_full_and_bandedDet`.

After this order-three input is supplied, the remaining initial-column lift is
`XiInitialColumnMinorGeFourFromContig`:

```text
for every k >= 4 and strictly increasing rows r:
  XiContigToeplitzTotalPositive
    -> det [XiToeplitzEntry(r_i, j)]_(0 <= i,j < k) >= 0.
```

Lean verifies the exact assembly step in
`xiContigToInitialColumnMinorBridge_of_two_three_and_geFour` and its
kernel-backed form
`xiContigToInitialColumnMinorBridge_of_kernelRep_three_and_geFour`.

The finite-dimensional criterion is kept separate as the explicit contract
`XiInitialColumnMinorToFullPFBridge`; it has not been assumed or formalized as
a theorem in this repository. Lean verifies the composition
`xiContigToFullPFBridge_of_initialColumn` once those two inputs and moment
positivity are supplied.

The resulting theorem target is
`KernelContigToPFInitialColumnTheorem`:

```text
KernelContigToPFInitialColumnTheorem
  -> XiToeplitzTotalPositive
  -> RiemannHypothesis.
```

via
`xiToeplitzTotalPositive_of_kernelContigToPFInitialColumn` and
`riemannHypothesis_of_kernelContigToPFInitialColumn`.

The sharper RH-closing bundle is now
`KernelContigToPFInitialColumnGeThreeTheorem`:

```text
InitialColumnGeThreeTheorem
  -> InitialColumnTheorem
  -> XiToeplitzTotalPositive
  -> RiemannHypothesis.
```

The checked adapters are
`kernelContigToPFInitialColumn_of_geThree`,
`xiToeplitzTotalPositive_of_kernelContigToPFInitialColumnGeThree`, and
`riemannHypothesis_of_kernelContigToPFInitialColumnGeThree`.

The further reduced bundle is
`KernelContigToPFInitialColumnGeFourTheorem`:

```text
InitialColumnGeFourTheorem
  -> InitialColumnGeThreeTheorem
  -> InitialColumnTheorem
  -> XiToeplitzTotalPositive
  -> RiemannHypothesis.
```

Its verified adapters are
`kernelContigToPFInitialColumnGeThree_of_geFour`,
`xiToeplitzTotalPositive_of_kernelContigToPFInitialColumnGeFour`, and
`riemannHypothesis_of_kernelContigToPFInitialColumnGeFour`.

This changes the proof search materially. Instead of proving arbitrary
row-and-column minors directly, first prove the contiguous-to-initial-column
lift for arbitrary row gaps of order at least four, while separately attacking
the known full-support/banded order-three frontiers. The consecutive seed above
is its gap-free base case; the next cases have nonconsecutive rows but still
fixed initial columns.

The previous top-unsupported straddle-left-product,
straddle-impossibility, no-straddle, middle-column-unsupported,
top-unsupported/middle-supported bracket-restriction, branch-impossibility,
right-banded-exclusion, right-active-exclusion, right-inactive-side-support,
inactive-side-support, original gap-collapse, cofactor gap-collapse,
impossible-branch, left-moment-zero, left-product, split-products, and
moment-product bundles remain verified as intermediates:

```text
KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftBracketTheorem
  <- KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedTheorem

KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftProductTheorem
  <-> KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftBracketTheorem
  -> False

KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftProductTheorem
  -> False

KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleImpossibleTheorem
  -> XiToeplitzTotalPositive
  -> RiemannHypothesis

KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnNoStraddleTheorem
  -> XiToeplitzTotalPositive
  -> RiemannHypothesis

KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnUnsupportedTheorem
  -> XiToeplitzTotalPositive
  -> RiemannHypothesis

KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedBranchImpossibleTheorem
  -> XiToeplitzTotalPositive
  -> RiemannHypothesis

KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightBandedExcludedTheorem
  -> XiToeplitzTotalPositive
  -> RiemannHypothesis

KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightActiveExcludedTheorem
  -> XiToeplitzTotalPositive
  -> RiemannHypothesis

KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightInactiveSideSupportTheorem
  -> XiToeplitzTotalPositive
  -> RiemannHypothesis

KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedInactiveSideSupportTheorem
  -> XiToeplitzTotalPositive
  -> RiemannHypothesis

KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedOriginalGapCollapseTheorem
  -> XiToeplitzTotalPositive
  -> RiemannHypothesis

KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedGapCollapseTheorem
  -> XiToeplitzTotalPositive
  -> RiemannHypothesis

KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedImpossibleTheorem
  -> XiToeplitzTotalPositive
  -> RiemannHypothesis

KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedLeftMomentZeroTheorem
  -> XiToeplitzTotalPositive
  -> RiemannHypothesis

KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedLeftProductTheorem
  -> XiToeplitzTotalPositive
  -> RiemannHypothesis

KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedSplitProductsTheorem
  -> XiToeplitzTotalPositive
  -> RiemannHypothesis

KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedMomentProductTheorem
  -> XiToeplitzTotalPositive
  -> RiemannHypothesis
```

The hard algebraic rows are still the cancellation combinations:

```text
A00 * det C0 - A01 * det C1 + A02 * det C2
```

where cancellation between a positive side cofactor and the middle cofactor is
unavoidable.

With classical scaffolding, Lean now verifies:

```text
KernelContigToPFTheorem -> RiemannHypothesis
```

So this is a complete RH route if the two mathematical payloads are proved:

1. every contiguous kernel Toeplitz determinant is nonnegative;
2. contiguous positivity upgrades to full arbitrary-minor PF for this xi
   sequence.

## Level 3: Full arbitrary-minor PF positivity

Lean target:

- `CrossFieldPFWitness`
- `xiToeplitzTotalPositive_of_crossFieldPFWitness`
- `riemannHypothesis_of_crossFieldPFWitness`

Mathematical meaning:

Any successful route must prove the full arbitrary-minor Pólya-frequency
condition for the signed xi coefficients:

```text
XiToeplitzTotalPositive
```

Given the classical scaffolding already isolated in `ClassicalToeplitzScaffolding`
(Edrei-ASW, Laguerre-Polya closure, Polya-Jensen, and the classical RH-to-PF
converse), Lean verifies:

```text
CrossFieldPFWitness -> RiemannHypothesis
```

This is the current honest success condition for fully solving RH inside this
program.

## Best next mathematical push

The most promising route is still combinatorics:

1. Try to realize the factorial-weighted moment sequence
   `M n / (2n)!` as a coefficient sequence of a Lorentzian or strongly
   log-concave object.
2. Upgrade the order-3 determinant to all contiguous determinants using a
   lattice-path or planar network model.
3. Prove `XiArbitraryMinorReductionToContig`, equivalently
   `XiContigToFullPFBridge`, the xi-specific theorem that upgrades contiguous
   minors to arbitrary Toeplitz minors.

The third step is the likely RH-hard wall.  It is now named precisely rather
than hidden inside broad language like "use combinatorics" or "use geometry."
