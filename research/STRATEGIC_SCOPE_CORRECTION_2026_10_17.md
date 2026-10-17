# Strategic scope correction — 17 October 2026

The useful near-term outputs are finite RH-criterion calibration and formalization of explicit reductions. They are not RH proofs. No new Lean theorem or build is claimed by this editorial correction.

| Track | Actual status inspected in this checkout |
|---|---|
| Toeplitz ladder | `RHReductionCapstone.xiToeplitzTotalPositive_iff_riemannHypothesis` takes four named classical bridge/converse hypotheses. It is an equivalence under those inputs, not an unconditional discharge of them or of the ladder. |
| All-window Weil positivity | A classical RH criterion after the functional and legal test class have been identified. `WeilWindowHypotheses.lean` checks scalar assembly and passage from a supplied cofinal family to all-window positivity; its genuine-functional identification and analytic inputs remain explicit. It does not itself assert an unconditional zeta/RH equivalence. |
| Same-height exclusion | Checked reductions retain their exclusion hypotheses. The proposed phase hypothesis `(H_theta)` has no checked zeta-specific bridge to componentwise exclusion in this checkout. Do not claim a Lean equivalence for it merely from inactive draft filenames. |
| Green paired budget | `XiGreenModel.green_paired_budget_iff_riemannHypothesis` explicitly proves the equivalence. The budget remains unproved. |

## Corrected claims

The same-height source, PDF and HTML now remove unsupported assertions that an arbitrary thin rectangle containing two function zeros contains exactly one derivative zero, that a horizontal phase crossing follows, or that GUE statistics establish a uniform deterministic nonvanishing bound. The example `f(z)=exp(i*z)*z*(z-1)` has two real endpoint zeros but `Im(f'/f)=1` throughout their interior. This refutes that general phase-crossing implication; it is not a zeta counterexample.

Conjugation symmetry does not alone establish the claimed self-adjoint operator domain, and a zero of a real potential does not force nonreal spectrum. The topological and heat-flow claims also lack their stated bridges and limiting arguments. These proposals are now labeled unproved and outside the active Lean surface. The historical componentwise-exclusion note is explicitly marked withdrawn as a proof. Pre-correction source/HTML snapshots are retained in the new round's records.

## Release and next work

The DH controls paper already states its finite/calibration scope and no-route-to-RH limitation. Its human-review request was sent to David Platt on 17 October with PDF and checklist; no review is inferred. Publication is authorized only after his substantive read, correction of required issues, and fresh verification of both draft files. A quiet daily follow-up checks that conversation. Zenodo's large-supplement transfer remains unresolved from the preceding round.

Decision on Liu: defer the public replay note until the controls paper has a verified public link. No Liu issue/comment is posted now. The replay is computational re-execution, not human analytic review or a second arithmetic implementation.

The split-pair finite-product theorem and `ZetaNoLowStripZero (141/10)` remain post-publication projects. The author reports a now-compiling `XiMellinRemainder` in the main checkout; that file is absent from this research worktree. After release, inspect and integrate the actual source, rerun its direct build and axiom checks, then prove the complete low rectangle. Do not treat a compiling remainder estimate as the rectangle certificate itself.
