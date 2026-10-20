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
The [actual-Xi closed-rectangle certificate](research/prime_spectral/XI_RECTANGLE_2026_10_20.md)
now proves nonvanishing on `0 ≤ Re(s) ≤ 1`, `|Im(s)| ≤ 14.1`, using 44
degree-12 tiles. The optional `XiRectangle` library discharges the low-height
input in its PF43 and PF58 wrappers; their other hypotheses remain explicit.
The [finite-product split-pair theorem](research/prime_spectral/FORMAL_TARGET_A_2026_10_17.md)
now derives the actual reciprocal coefficients, a nonzero leading coefficient,
an exponential remainder and both determinant signs at unbounded ranks.
The [Jacobi bridge and evaluator components](research/prime_spectral/FORMAL_TARGET_A_JACOBI_AND_EVALUATOR_2026_10_18.md)
now identify these reciprocal minors with the original coefficient minors.
The [standalone entire-function extension](research/prime_spectral/ANALYTIC_SPLIT_PAIR_AND_HARD_TILE_2026_10_18.md)
also compiles, including the transfer to actual Taylor-coefficient minors. It
assumes simple selected zeros and strict modulus gaps; it does not replace the
general PF-to-RH bridges.

> **Current research status (updated 20 October 2026):**
> [`research/RESEARCH_STATUS_2026_10_11.md`](research/RESEARCH_STATUS_2026_10_11.md)
> records the evidence and open assumptions for the active tracks. It supersedes
> older priority and novelty claims below. The 20 October rectangle report above
> supersedes earlier Target B status notes. The active outputs are the unreviewed
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
| 2. Pólya frequency / Toeplitz and Jensen | `rh_reduction_paper.tex`, `rh_two_routes_paper.tex`, `hef_companion_paper.tex` | `riemannHypothesis_of_strictLadder` (`ToeplitzFullPF`), `riemannHypothesis_of_hpss_route` (`EffectiveAssembly`) | Strict contiguous ladder at unbounded rank remains RH-strength. Target B supplies height 14.1, and the actual folded-Xi sector bridge is proved. Unconditional `XiFinitePFCertified.finitePF43` is CI-verified at `150537b` ([run 39470397281](https://github.com/sciencenerd-des/reinmann/actions/runs/39470397281)); PF58 retains the external seven-eighths input |
| 3. Semilocal Weil operator and controls | `weil_infinite_rank_tail_paper.tex`, `dh_controls_paper.tex` | `WeilRankTail`, `CoupledRankEnergy`, `WeilWindowHypotheses`, `WeilSchurInertia` | All-support positivity remains a classical RH criterion after genuine-form identification; Lean checks conditional assembly and a supplied cofinal family. Own full-window certificates reach C ≈ 4.9998. Liu frozen A/B replays are merged computational audits, not a new analytic proof or own window record |
| 4. Pseudo-Hermitian / Fock-space jets | none yet; see [`research/pseudo_hermitian/RESEARCH_OBJECTIVE.md`](research/pseudo_hermitian/RESEARCH_OBJECTIVE.md) | `PseudoHermitian*`, `XiAlgebraicJet*`, `XiGreenModel` | The Green form has Lean-checked symmetry and all-zero masses; its paired residual budget is Lean-proved *equivalent* to RH (`green_paired_budget_iff_riemannHypothesis`) |

The [standing DH gate](research/RH_DH_DISCRIMINATOR_REGISTER.md) records retained failures and missing arithmetic discriminators for the open RH-strength targets. Shared finite prerequisites are not advertised as RH strategies.

### Latest results

- **Formalization version 2 released.** The unreviewed preprint now includes the
  actual-Xi evaluator, closed height-14.1 rectangle and unconditional PF43,
  presented as formalizations of classical facts.
  [DOI 10.5281/zenodo.23516924](https://doi.org/10.5281/zenodo.23516924) includes
  the complete pinned source supplement; all public downloads were checksum-verified.
  The split-pair theorem retains its simple-zero and isolated-tie hypotheses.

- **Finite-product split-pair theorem.** Lean proves the actual reciprocal
  determinant expansion, nonzero Vandermonde coefficient, root-order gap,
  exponential remainder and both signs at unbounded ranks. Finite geometric
  sums cover rational and irrational phases together. Quadratic and cubic
  controls instantiate the result. The Jacobi bridge now transfers the conclusion
  to original coefficient minors, with the sign cancellation proved. See
  [`FORMAL_TARGET_A`](research/prime_spectral/FORMAL_TARGET_A_2026_10_17.md) and
  [the Jacobi round](research/prime_spectral/FORMAL_TARGET_A_JACOBI_AND_EVALUATOR_2026_10_18.md).
- **Actual-Xi closed rectangle.** Lean proves `xiCompleted s ≠ 0` throughout
  `0 ≤ Re(s) ≤ 1`, `|Im(s)| ≤ 14.1`. A closed rational cover uses 44 degree-12
  Taylor certificates, reusable Gamma/zeta remainder bounds and a zeta identity
  regularized through `s = 1`. The theorem supplies `ZetaNoLowStripZero (141/10)`
  to `XiFinitePFCertified.finitePF43` without a theorem hypothesis. The default
  2,608-row audit, separate 1,700-declaration rectangle audit and explicit PF43
  check use only standard foundational axioms. All fourteen jobs passed in
  [CI run 39470397281](https://github.com/sciencenerd-des/reinmann/actions/runs/39470397281)
  at proof source `150537b`. The actual genus-zero identity, inverse-zero
  summability and fixed-rank sector bridge are proved using the attributed
  [PNT+ backport](research/prime_spectral/PNT_HADAMARD_BACKPORT_2026_10_20.md).
  The bounded numerical replay took 109.37 monotonic minutes with warm dependencies;
  see [the certificate and reproduction notes](research/prime_spectral/XI_RECTANGLE_2026_10_20.md).
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

Build and audit the optional numerical rectangle library separately, using
bounded concurrency to limit memory:

```sh
python3 experiments/prime_spectral/build_xi_rectangle.py --jobs 4 --output tmp/xi-rectangle-replay
python3 experiments/prime_spectral/verify_xi_rectangle.py --live-audit
```

Use fewer jobs on a smaller machine. The [rectangle report](research/prime_spectral/XI_RECTANGLE_2026_10_20.md)
records the proof status, storage cost and measured runtime.

## Verification boundary

The default checked proof surface is `Reinmann.lean` and the `.lean` files under
`Reinmann/`. The optional `XiRectangle.lean` and `XiRectangle/` numerical library
has a separate build and axiom audit. Drafts and archived experiments under
`research/` are outside these library import surfaces; their individual status
is recorded in the dated notes and verification receipts.

The root module `Reinmann.lean` supplies the default mathematical imports;
`XiRectangle` is imported separately. The original spine modules are:

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
