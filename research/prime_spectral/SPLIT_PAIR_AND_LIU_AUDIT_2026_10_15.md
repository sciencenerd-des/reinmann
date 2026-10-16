# Split-pair minors, small-offset calibration and Liu replay — 15 October 2026

All work is confined to `codex/xi-eigenvector-reduction`. The original checkout was left unchanged. No commit, merge, publication or external message is part of this research round.

## DH: the targeted column fails at rank 664

The cached 32,768-bit ordinary coefficients resolve every shift-44 member at ranks 521–677: 521–663 positive and 664–677 negative. Direct 44×44 determinants check 520, 521, 663, 664 and 677. Together with PF435 and the earlier grid, 664 is the first negative rank **in the shift-44 column**. The first negative minor over all shifts or arbitrary minors is not located.

A fresh 32,768-bit conjugate Dirichlet-L jet calculation supplies all 1,451 ordinary coefficients through index 1450; all 721 shared enclosures overlap the previous four-Hurwitz-jet evaluation. The targeted column is **negative at every rank 664–1099**, then positive at every rank 1100–1400, with no unresolved divisor. A higher-precision determinant replay checks all 880 new-column signs and direct determinants at both band boundaries. Both coefficient paths share FLINT/Arb.

A separate AI reviewer repeated the initial column at 33,024 bits and checked the direct determinants. The split-pair theorem in the paper gives infinite sign changes: 43 inner simple folded real zeros and the next conjugate pair give two dominant complementary Schur terms. Every factor in the residue/Vandermonde leading constant is nonzero. The leading phase is approximately 3.07878714769 and the rank oscillation scale is 872.66973123454. The strict folded-modulus ordering uses gamma²+b², not gamma alone. The asymptotic phase is diagnostic; finite signs are certified by interval determinants.

This is the classical Widom/Schur mechanism, with a written Cauchy remainder extension to the entire reciprocal. No novelty claim is made for the underlying finite-pole asymptotic. Neighboring modulus gaps alone are not used as a quantitative bound on finite-rank corrections.

## A small-offset point, without a limiting law

An exact rational mixture of the conductor-13 label-2 and label-6 controls has lowest off-line zero near 0.53+31.4336216845i. Its complete atlas through 160 contains 123 upper-half-plane zeros, with a separate higher-precision contour/local replay. The exact mixture parameter was fixed before window trials. It is a mixture, not a single character-label control.

The unchanged seven-control fit predicted C=34.5767528427 before the new trials. A degree-192 exact rational witness is negative at C=593/16=37.0625, with quotient about -7.37956e-18. This gives r≈0.5698713, 7.19% above the forecast and within the previous 16–20% leave-one-out errors. Degree 256 already detects negativity at C=37. A positive degree-192 section there therefore supplies no full-support lower bound.

This does **not** settle b→0: one finite-offset support upper bound cannot establish or exclude divergent detection cost, and other off-line pairs remain. The lowest quartet dominates the negative finite-atlas terms, but the finite total differs materially from the geometric quotient; no negligible infinite tail is asserted. The seven-point regression is not refitted.

Bounded additional conductor/label searches are selectors only. A zero found by Newton search and a local disk is not necessarily the lowest off-line zero; completeness requires the full atlas. No absence theorem follows from a selector's null result. The bounded searches completed without a qualifying lowest-observed-offset candidate in [0.02,0.05].

## Liu's frozen release

Both frozen certificates passed source/matrix/residual replay. A uses FULL_RETAINED_VERIFY and its finalizer at L=1, C=e²; B uses clean FULL_REBUILD and a second FAST_VERIFY at L=17/16. All original archive members remained unchanged. The Windows-oriented preflight required a byte-identical private zipped standard-library layout on macOS, without an audit bypass or code patch. See [the detailed audit](LIU_FROZEN_RELEASE_AUDIT_2026_10_15.md) and `liu_audit.json`.

This completes the requested computational replay. It does not supply a new arithmetic implementation, human peer review, formalization of the analytic dependencies or RH proof.

## Verification and stopped work

Three split-pair tests and three small-offset tests pass, including independent geometric integral checks and higher-precision exact-witness reconstruction. Two package acceptance tests also pass, including rejection of a stale supplied bundle before any remote draft action. The separate AI review is disclosed as such. The finite Lean results are unchanged from the earlier checked six-theorem audit; no new Lean build is claimed.

Broad Toeplitz grid scans, D6, arithmetic ablations and D2 exact counts remain stopped. Universal Phi remains stopped: this small-offset point is inconclusive and does not supply the missing uniform cancellation/tail theorem. The laboratory's own D1 comparison is stopped; late symbol dips are a design obstruction. The paper's results concern finite-detector calibration, not a route to RH by themselves.

The final reproducibility manifest, extended targeted column, rendered paper and private Zenodo draft are recorded separately. The author must press Publish; draft preparation does not publish the work.
