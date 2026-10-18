# Reinmann Lean Verification Scaffold

This is a Lean/Lake scaffold for formal Riemann Hypothesis exploration. It does
not prove the Riemann Hypothesis. The project imports mathlib's formal
`RiemannHypothesis : Prop` target and verifies only reductions and supporting
lemmas that Lean can check.

The near-term outputs are **calibration and formalization**, not an RH proof.
The universal Toeplitz ladder retains the classical bridge hypotheses in
`RHReductionCapstone.lean`; positivity on every Weil window is an RH criterion,
not a consequence of the finite certificates. The Green-form paired budget is
explicitly equivalent to RH in `XiGreenModel.lean`. The same-height paper's
proposed phase hypothesis `(H_θ)` and its zeta-specific exclusion bridge remain
unproved; inactive `.lean.draft` files are not checked proofs. A scope correction
removes earlier unsupported claims based on winding counts, GUE statistics,
operator self-adjointness and heat-flow heuristics.

The [DH controls paper](paper/dh_controls_paper.pdf) measures finite detection
sensitivity. It was published on 18 October 2026 as an unreviewed preprint:
[DOI 10.5281/zenodo.23401370](https://doi.org/10.5281/zenodo.23401370).
The final PDF and complete supplement were checksum-verified; no completed
external human review is claimed. The [held-out logarithmic forecast test](research/prime_spectral/LOG_FORECAST_RESULTS_2026_10_17.md)
adds offsets0.002 and0.001; the measured plain-L exponent does not meet either
registered forecast tolerance. The [final matched-mixture test](research/prime_spectral/FINAL_LOG_MECHANISM_RESULTS_2026_10_17.md)
also misses both fixed forecast tolerances at offsets 0.0005 and 0.00025.
The logarithmic fit remains descriptive; forecasting is closed.
The [uniform actual-Xi Mellin truncation tail](research/prime_spectral/XI_LOW_RECTANGLE_STATUS_2026_10_17.md)
now compiles and passes the full axiom audit; the zero-free rectangle is still open.
The [finite-product split-pair theorem](research/prime_spectral/FORMAL_TARGET_A_2026_10_17.md)
now derives the actual reciprocal coefficients, a nonzero leading coefficient,
an exponential remainder and both determinant signs at unbounded ranks.
The [Jacobi bridge and evaluator components](research/prime_spectral/FORMAL_TARGET_A_JACOBI_AND_EVALUATOR_2026_10_18.md)
now identify these reciprocal minors with the original coefficient minors.
Finite-theta tails, quadrature rules and a closed-grid cover are source-checked.
The entire-function determinant extension and actual Xi tile certificates remain open.

> **Current research status (updated 18 October 2026):**
> [`research/RESEARCH_STATUS_2026_10_11.md`](research/RESEARCH_STATUS_2026_10_11.md)
> records the evidence and open assumptions for the active tracks. It supersedes
> older priority and novelty claims below. The active outputs are the unreviewed
> controls preprint and formal targets A and B; logarithmic forecasting is closed.
> D1 comparison engineering, broad Toeplitz scans, D2 exact counts, D6 induction
> and arithmetic ablations remain stopped.
> [`ARCHITECTURE.md`](ARCHITECTURE.md) supplies the broader module inventory and
> reduction map; its counts and validation claims must be read with their dates.
> The executable research roadmap is
> [`research/RH_PROOF_PLAN_2026_07_17.md`](research/RH_PROOF_PLAN_2026_07_17.md).
> Run `bash scripts/verify_axiom_clean.sh` to confirm the 0-`sorry` /
> 0-custom-axiom claim. Historical progress notes live in [`docs/archive/`](docs/archive/).

## Research tracks at a glance

The established capstones retain RH-level obligations. Lean checks the
reductions with explicit named inputs; proposed analytic bridges must be
proved before they can be classified as sufficient conditions for RH.

| Track | Manuscript (`paper/`) | Lean capstone (`Reinmann/`) | Open obligation |
|---|---|---|---|
| 1. Same-height fibers | `rh_same_height_fiber_framework.tex` | `riemannHypothesis_iff_noSameImaginaryPartCollision` (`RiemannSpine`), `riemannHypothesis_of_all_fiber_card_le_one` (`FiberCentroid`) | Componentwise critical exclusion remains open. The proposed phase condition (H<sub>θ</sub>) also needs a valid zeta-specific exclusion bridge; no Lean equivalence for it is claimed |
| 2. Pólya frequency / Toeplitz and Jensen | `rh_reduction_paper.tex`, `rh_two_routes_paper.tex`, `hef_companion_paper.tex` | `riemannHypothesis_of_strictLadder` (`ToeplitzFullPF`), `riemannHypothesis_of_hpss_route` (`EffectiveAssembly`) | Strict contiguous ladder at unbounded rank (RH-strength), plus the classical scaffolding bridges. Fixed rank is classical (PF43; PF58 under quasi-RH) |
| 3. Semilocal Weil operator and controls | `weil_infinite_rank_tail_paper.tex`, `dh_controls_paper.tex` | `WeilRankTail`, `CoupledRankEnergy`, `WeilWindowHypotheses`, `WeilSchurInertia` | All-support positivity remains a classical RH criterion after genuine-form identification; Lean checks conditional assembly and a supplied cofinal family. Own full-window certificates reach C ≈ 4.9998. Liu frozen A/B replays are merged computational audits, not a new analytic proof or own window record |
| 4. Pseudo-Hermitian / Fock-space jets | none yet; see [`research/pseudo_hermitian/RESEARCH_OBJECTIVE.md`](research/pseudo_hermitian/RESEARCH_OBJECTIVE.md) | `PseudoHermitian*`, `XiAlgebraicJet*`, `XiGreenModel` | The Green form has Lean-checked symmetry and all-zero masses; its paired residual budget is Lean-proved *equivalent* to RH (`green_paired_budget_iff_riemannHypothesis`) |

### Latest results

- **Finite-product split-pair theorem.** Lean proves the actual reciprocal
  determinant expansion, nonzero Vandermonde coefficient, root-order gap,
  exponential remainder and both signs at unbounded ranks. Finite geometric
  sums cover rational and irrational phases together. Quadratic and cubic
  controls instantiate the result. The Jacobi bridge now transfers the conclusion
  to original coefficient minors, with the sign cancellation proved. See
  [`FORMAL_TARGET_A`](research/prime_spectral/FORMAL_TARGET_A_2026_10_17.md) and
  [the Jacobi round](research/prime_spectral/FORMAL_TARGET_A_JACOBI_AND_EVALUATOR_2026_10_18.md).
- **Uniform low-rectangle tail.** Lean proves the actual Xi truncation error
  is at most (19981/50)e<sup>−T</sup> for T ≥ 1 throughout
  0 ≤ Re(s) ≤ 1, |Im(s)| ≤ 14.1. The full build and 244-theorem axiom audit pass.
  The new source-checked components add Gaussian finite-theta tails, midpoint
  quadrature with variation, and a closed-grid cover. Actual Xi center enclosures
  and positive tile margins remain open; there is no zero-free rectangle certificate. See
  [`XI_LOW_RECTANGLE_STATUS`](research/prime_spectral/XI_LOW_RECTANGLE_STATUS_2026_10_17.md).
- **Sine-type model obstruction.** An explicit fixed-bandwidth negative witness
  works for every b > 0 in a finite perturbation of the cosine lattice. The proposed
  general log(1/b) support lower bound needs stronger hypotheses. See
  [`SINE_TYPE_LOG_COST_OBSTRUCTION`](research/prime_spectral/SINE_TYPE_LOG_COST_OBSTRUCTION_2026_10_17.md).
- **Davenport–Heilbronn controls.** A complete certified atlas to height
  340 gives a PF<sub>435</sub> sector guarantee. All 18,291 solid minors at
  ranks 430–520 are positive. Seven controls give certified negative Weil
  windows, and a pre-registered q = 17 forecast held. See
  [`DH_FALSIFICATION`](research/prime_spectral/DH_FALSIFICATION_2026_10_12.md),
  [`RESEARCH_ROUND`](research/prime_spectral/RESEARCH_ROUND_2026_10_12.md) and
  [`CALIBRATION_AND_SYMBOL_ROUND`](research/prime_spectral/CALIBRATION_AND_SYMBOL_ROUND_2026_10_13.md).
- **Whole-cluster certificates (D1–D6).** Two-sided full-operator block
  certificates at fixed support; the robustness obstruction at C = 3.2; the
  inertia obstruction to a rank-one induction. See
  [`CLUSTER_PROGRAM`](research/prime_spectral/CLUSTER_PROGRAM_2026_10_12.md)
  and [`DIRECTIONS_OUTCOME`](research/prime_spectral/DIRECTIONS_OUTCOME_2026_10_12.md).
  The motivating diagnostics are in
  [`RESEARCH_DIRECTIONS_2026_10_12`](research/RESEARCH_DIRECTIONS_2026_10_12.md).
- **Certified windows.** Arb certificates reach C ≈ 4.9998, an
  independent replication of Zhu's window; see
  [`CERTIFIED_WINDOW_POSITIVITY`](research/prime_spectral/CERTIFIED_WINDOW_POSITIVITY_2026_10_07.md).
- **Strict finite PF.** Real-zero extraction gives strict contiguous
  positivity through rank 43, with a Lean-checked determinant expansion; see
  [`STRICT_FINITE_PF_FROM_REAL_ZEROS`](research/STRICT_FINITE_PF_FROM_REAL_ZEROS_2026_10_06.md).
- **Manuscript audit (16 October).** The HEF companion was rewritten around a
  corrected transport identity. Two invalid arguments were withdrawn from the
  same-height paper. See
  [`paper/MANUSCRIPT_REVIEW_AUDIT_2026_10_16.md`](paper/MANUSCRIPT_REVIEW_AUDIT_2026_10_16.md).

Longer histories live in the dated notes under `research/` and in
[`docs/archive/`](docs/archive/).

## Commands

Fetch dependencies and cached mathlib artifacts:

```sh
lake update
lake exe cache get
```

Run the full verifier:

```sh
./scripts/safe-verify.sh
```

With no arguments, the harness scans `Reinmann.lean` and every `.lean` file
under `Reinmann/`, then runs `lake build` and typechecks every active file
directly with `lake env lean`.

```sh
./scripts/safe-verify.sh Reinmann.lean
```

With file arguments, the harness still scans every active `.lean` file for
shortcuts, then runs `lake env lean` on each target file.

## Verification boundary

Only `.lean` files under `Reinmann/` are part of the active checked proof
surface. Draft files live under `research/` and `research/active-lean-drafts/`;
they are research notes, not verified proof artifacts.

The active root module `Reinmann.lean` imports every proof-grade Lean module
(more than one hundred). The original spine modules are:

- `Reinmann.RiemannSpine`
- `Reinmann.ConjugateHalfPlane`
- `Reinmann.InvolutionSymmetry`
- `Reinmann.KnownZeroFreeRegions`
- `Reinmann.TwoBranchArchitecture`
- `Reinmann.ZeroSymmetry`
- `Reinmann.ProofArchitecture`

## Current proof spine

`Reinmann/RiemannSpine.lean` proves a conditional reduction:

- existing mathlib fact: `riemannZeta_ne_zero_of_one_le_re` eliminates zeros
  with `1 <= s.re`
- existing mathlib fact: `riemannZeta_neg_two_mul_nat_add_one` verifies the
  negative even zeros
- local theorem: `left_of_strip_zero_is_trivial` proves every zero with
  `s.re <= 0` is one of the negative even zeros
- local theorem: `strip_zero_reflection_iff` proves that, inside the critical
  strip, zerohood is equivalent for `s` and its reflection `1 - s`
- local theorem: `functionalEquation_prefactor_ne_zero_in_strip` proves the
  non-zeta prefactor in the functional equation cannot create zeros inside the
  open critical strip
- local theorem: `riemannHypothesis_of_rightHalfStripZeroFree` proves that it
  is enough to rule out zeros in the one-sided region `1 / 2 < s.re < 1`
- local theorem: `rightHalfStripZeroFree_iff_riemannHypothesis` proves that the
  one-sided zero-free target is equivalent to mathlib's formal
  `RiemannHypothesis`
- local theorem: `riemannZeta_conj_of_one_lt_re` proves
  `riemannZeta (conj s) = conj (riemannZeta s)` in the Dirichlet-series
  half-plane `1 < s.re`
- local definition: `StripConjugateZeroSymmetry` names the exact zero-level
  conjugation obligation needed by the uniqueness route; it is weaker than
  global value-level `ConjugateSymmetry`
- local theorem: `stripConjugateZeroSymmetry_of_conjugateSymmetry` proves that
  full conjugate symmetry implies the narrower strip zero-level obligation
- local definition: `ZeroFiberRealUnique γ` names the fiberwise target: at
  height `γ`, all critical-strip zeros have the same real coordinate
- local theorem: `zeroImUniqueness_iff_forall_zeroFiberRealUnique` proves that
  `ZeroImUniqueness` is exactly the conjunction of all fiberwise targets
- local definition: `NoSameImaginaryPartCollision` names the spectral
  no-degeneracy target: no two critical-strip zeros share an imaginary part
  while having different real parts
- local theorem: `noSameImaginaryPartCollision_iff_zeroImUniqueness` proves the
  no-collision target is exactly equivalent to `ZeroImUniqueness`
- local theorem: `riemannHypothesis_iff_noSameImaginaryPartCollision` proves
  that, assuming `StripConjugateZeroSymmetry`, RH is exactly equivalent to the
  no-collision target
- local theorem: `riemannHypothesis_iff_forall_zeroFiberRealUnique` proves that,
  assuming `StripConjugateZeroSymmetry`, RH is exactly equivalent to every
  imaginary-height fiber being real-coordinate unique
- local theorem: `not_riemannHypothesis_implies_same_height_collision` proves
  that, assuming `StripConjugateZeroSymmetry`, any RH counterexample forces a
  same-height pair of strip zeros with different real parts
- local theorem: `not_riemannHypothesis_implies_failed_zeroFiberRealUnique`
  proves that, assuming `StripConjugateZeroSymmetry`, any RH counterexample
  produces a failed imaginary-height fiber
- local theorem: `stripConjugateZeroSymmetry_of_riemannHypothesis` proves that
  RH itself implies the strip zero-level conjugation bridge
- local theorems: `rh_iff_noCollision_obligations` and
  `rh_iff_fiberUniqueness_obligations` prove that the no-collision and
  fiberwise remaining-obligation bundles are exactly RH-strength
- local theorems: `one_lt_re_halfPlane_isOpen`,
  `one_lt_re_halfPlane_isPreconnected`, and `one_lt_re_halfPlane_isConnected`
  record the topology of the Dirichlet-series half-plane for future analytic
  continuation work
- local theorem: `criticalStripObligations_iff_riemannHypothesis` proves that
  the native open-critical-strip obligation is equivalent to mathlib's formal
  `RiemannHypothesis`
- local theorem: `not_riemannHypothesis_iff_exists_rightHalfStrip_zero` proves
  that a failure of `RiemannHypothesis` is exactly an explicit zero with
  `1 / 2 < s.re < 1`
- local definition: `RightHalfStripCounterexample` names that exact
  counterexample shape for future proof-search steps
- local definition: `LeftHalfStripCounterexample` names the reflected companion
  shape
- local theorem: `exists_rightHalfCounterexample_iff_exists_leftHalfCounterexample`
  proves that counterexamples, if they exist, occur in reflected pairs across
  `s ↦ 1 - s`
- local theorem: `leftHalfStripZeroFree_iff_rightHalfStripZeroFree` proves that
  zero-freeness on the left half of the critical strip is equivalent to
  zero-freeness on the right half
- local theorem: `leftHalfStripZeroFree_iff_riemannHypothesis` proves that the
  left-half zero-free target is also equivalent to mathlib's formal
  `RiemannHypothesis`
- local theorem: `not_riemannHypothesis_iff_exists_leftHalfStripCounterexample`
  proves that RH failure can be witnessed on the left half as well
- local theorems: `riemannHypothesis_iff_no_rightHalfStripCounterexample` and
  `riemannHypothesis_iff_no_leftHalfStripCounterexample` name the exact
  no-counterexample targets equivalent to RH
- local definition: `CriticalStripOffLineZero` names the native strip-zero
  counterexample shape: a zero with `0 < s.re < 1` and `s.re ≠ 1 / 2`
- local theorem: `not_riemannHypothesis_iff_exists_criticalStripOffLineZero`
  proves that RH failure is exactly the existence of such an off-line strip zero
- local theorem: `noCriticalStripOffLineZero_iff_criticalStripObligations`
  proves directly that ruling out off-line strip zeros is the same as the native
  critical-strip obligation
- local structure: `RHEquivalentTarget` registers targets by storing an
  equivalence to `RiemannHypothesis`, not a proof of the target
- local theorems: `riemannHypothesis_of_target` and
  `target_of_riemannHypothesis` convert between any registered target and RH
- remaining obligation: prove `RightHalfStripZeroFree`; via the uniqueness
  path, it is enough to prove both `StripConjugateZeroSymmetry` and
  `ZeroImUniqueness`, equivalently `StripConjugateZeroSymmetry` plus either
  `NoSameImaginaryPartCollision` or `∀ γ, ZeroFiberRealUnique γ`

The remaining obligation is not a weaker workaround: the equivalence theorem
shows it is exactly Riemann-Hypothesis-strength.

## Research draft policy

Exploratory files with placeholders or conjectural axioms are preserved under
`research/*.lean.draft` and `research/lean-drafts/`. They are intentionally not
imported by `Reinmann.lean` and not scanned as verified Lean code. Promote a
draft into `Reinmann/` only after replacing every placeholder and axiom with
Lean-checked proofs that pass `./scripts/safe-verify.sh`. Drafts must not be
cited as formalized results.

## What SafeVerify rejects

Before invoking Lean/Lake, the harness rejects files containing obvious
verification shortcuts:

- `sorry`
- `admit`
- `axiom` declarations
- `constant` declarations
- `opaque` declarations
- `unsafe`
- `set_option autoImplicit true`
- `set_option relaxedAutoImplicit true`

## Limitations

- The precheck strips nested block comments and line comments before scanning,
  but it is not a full Lean parser and may reject forbidden words inside strings.
- The precheck is not a full Lean parser and cannot prove that a development is
  mathematically complete or trustworthy.
- Passing this harness only means the scanned files avoid the listed shortcuts
  and typecheck with the configured Lean/Lake toolchain.
