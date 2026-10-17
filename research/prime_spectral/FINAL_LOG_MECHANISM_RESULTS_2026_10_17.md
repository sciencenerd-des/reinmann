# Final matched-mixture mechanism round — 17 October 2026

## Result: both final forecasts fail; forecasting is closed

The same-conductor, same-odd-gamma measurement gives κ=1.0975310108891705. Six saved normalized witnesses give κ′=0.3603024675237778. The prescribed balance slope 2/(κ−κ′)=2.7128629486728104 was frozen before either new mixture was selected. It fails the preset ±0.25 C tolerance on both final targets. The log fit remains descriptive only; no refit, replacement mechanism or further held-out target is authorized by this round.

| Offset b | Frozen mechanism C | N192 finite-positive evidence | N192 certified negative C | N256 certified negative C | N192 forecast error | Fixed ±0.25 |
|---|---:|---:|---:|---:|---:|---|
| 0.0005 | 48.872600804 | 48.375000 | 48.406250 | 48.375000 | -0.466350804 | Fail |
| 0.00025 | 50.753014108 | 50.156250 | 50.187500 | 50.125000 | -0.565514108 | Fail |

The N256 positive endpoints are 3095/64=48.359375 and 3207/64=50.109375. These are local finite-family bisection intervals. Their positive sides do not certify full-window positivity or minimum negative support; the negative trials give support upper bounds. Retained-degree sensitivity strengthens the observed misses, but does not change the primary N192 assessment. The frozen descriptive predictions also miss both endpoint tolerances and are not substituted after the fact.

The protocol and exact local forecast hash are in [FINAL_LOG_MECHANISM_PROTOCOL](FINAL_LOG_MECHANISM_PROTOCOL_2026_10_17.md). Primary κ uses fixed b=0.001, N192 and C=32,34,36,38,40,42. Sensitivities use b=0.002 and N128. Adjacent slopes vary, and the saved derivative witnesses vary with both b and C; no limiting spectral exponent is proved. All six saved transform values and derivatives pass independent formula checks. The finite quartet agrees well with the leading approximation; the infinite zero tail is not attributed at that tiny scale.

## Certification and provenance

Both new atlases are complete to H=160: 123 total zeros, 113 line zeros and five right off-line zeros with reflected partners. Their lowest off-line pair is the selected near-collision pair at height about 31.433535. Every disk has radius 10^-80, far below the pair separation. Each fresh replay evaluates 5814 contour segments at 320 bits and 118 root gates at 640 bits. These are re-evaluations with the same Arb/FLINT backend, not independent arithmetic implementations.

Both final N192 exact rational witnesses were reconstructed at 4352 bits and remained strictly negative:

- b=0.0005, C=48.40625: even quotient [-1.01753034830962130e-22 +/- 2.18e-40]
- b=0.00025, C=50.1875: even quotient [-1.09767524299313388e-23 +/- 3.49e-41]

Source, forecast, definition, atlas, replay and trial hashes are bound by the final-round verifier. The previous round's scientific artifacts remain unchanged. Four documents are explicitly reconciled: README and the same-height TeX/PDF/HTML. The committed worktree versions of those four are retained under `historical_worktree_9b65a08/` and checked against the previous manifest, while the current reconciled versions are separately bound. Historical manifests are not rewritten.

The source of the unavailable FLINT series-sinh API and the first Lean proof attempt are retained as diagnostic failures. The compatible derivative companion, direct Lean build, full build and axiom audit are the successful records. Failures are not counted as passed checks.

## Model theorem: a counterexample and a corrected cutoff

The proposed sine-type hypotheses do not imply logarithmic support growth. [SINE_TYPE_LOG_COST_OBSTRUCTION](SINE_TYPE_LOG_COST_OBSTRUCTION_2026_10_17.md) gives explicit fixed-support negative witnesses, including a smooth real even witness for a positive-height quartet and versions satisfying the two pole-removal constraints. Uniform sine-type growth persists along the collision path; pair separation shrinks with b as it must in this regime.

For the unconstrained centered lattice form, the written proof computes the actual cutoff through a two-by-two Gram matrix:

    L_*(b) = π − (32/π)b² + O(b⁴),
    C_*(b) = exp(2π)[1 − (64/π)b² + O(b⁴)].

This is a finite limiting cutoff, not a log(1/b) divergence. Fourier identities, pair formulas, Gram integration and the cutoff expansion have 16 numerical sanity checks in addition to the written proof. They are not Lean formalizations. The note cites the targeted primary-source sampling/interpolation literature and makes no novelty claim. It also proves an elementary conditional exponential-balance lemma and lists the stronger frame/derivative hypotheses that would be needed in another model. This does not refute the observed arithmetic calibration or establish its asymptotic behavior.

## Reconciliation and formal work

- Worktree round: `9b65a08`; reconciliation merge into `rh-structural-theory`: `701ea85`.
- The main README layout and same-height section removals are preserved. Track 1 and 3 scope rows are corrected; the generic phase-crossing inference is replaced by its counterexample.
- Uniform actual-Xi integral tail: `f0dd349`, four new Lean theorems in `XiMellinRectangle.lean`. For T≥1 on 0≤Re(s)≤1 and |Im(s)|≤14.1, the actual Xi truncation error is at most (19981/50)exp(−T). Full build 3563 jobs and 244-theorem axiom audit pass, with no sorry or custom axioms.
- This is not a zero-free rectangle certificate. Finite-theta tails, quadrature, tile coverage and nonvanishing remain open; see [XI_LOW_RECTANGLE_STATUS](XI_LOW_RECTANGLE_STATUS_2026_10_17.md).
- Finite-product split-pair formalization remains deferred pending the requested go-ahead to start before publication. Broad Toeplitz scans, D1 comparison engineering, D2 exact counts, D6 and arithmetic ablations remain stopped.

The [local follow-up draft](../../paper/dh_final_log_mechanism_note.md) is unreviewed and unpublished. The original controls PDF is unchanged from the human-review request. This round sends no message, posts no Liu note, pushes no branch and publishes no record. Release remains conditional on substantive human review and the separate fresh-PDF/full-supplement verification gate.
