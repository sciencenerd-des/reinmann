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
sensitivity. Its human-review request was sent on 17 October 2026; review and
publication remain pending. The [held-out logarithmic forecast test](research/prime_spectral/LOG_FORECAST_RESULTS_2026_10_17.md)
adds offsets0.002 and0.001; the measured plain-L exponent does not meet either
registered forecast tolerance. The split-pair finite-product theorem and certified
low-zero rectangle are [post-publication formal targets](research/prime_spectral/POST_PUBLICATION_FORMAL_TARGETS_2026_10_15.md).

> **Current research status (updated 17 October 2026):**
> [`research/RESEARCH_STATUS_2026_10_11.md`](research/RESEARCH_STATUS_2026_10_11.md)
> records the evidence and open assumptions for the active tracks. It supersedes
> older priority and novelty claims below. The immediate target is a certified
> full-operator spectral cluster, followed by prime-side counting and Fourier convergence.
> [`ARCHITECTURE.md`](ARCHITECTURE.md) supplies the broader module inventory and
> reduction map; its counts and validation claims must be read with their dates.
> The executable research roadmap is
> [`research/RH_PROOF_PLAN_2026_07_17.md`](research/RH_PROOF_PLAN_2026_07_17.md).
> Run `bash scripts/verify_axiom_clean.sh` to confirm the 0-`sorry` /
> 0-custom-axiom claim. Historical progress notes live in [`docs/archive/`](docs/archive/).

## Current research implementation

The [D1–D6 cluster program](research/prime_spectral/CLUSTER_PROGRAM_2026_10_12.md)
replaces division by an internal ground-state gap with a two-sided certificate
for a whole full-operator block. The proposed rank staircase is checked at fixed
supports rather than assumed as a counting theorem. It also records a precise
[robustness obstruction at C=3.2](research/prime_spectral/ROBUSTNESS_OBSTRUCTION_C3P2_2026_10_12.md)
and an arithmetic Davenport–Heilbronn negative control. An all-support counting
law, calibrated zero-free region and full negative-control scan remain open.
The [remaining-directions results](research/prime_spectral/DIRECTIONS_OUTCOME_2026_10_12.md)
improve the C=3 full projector-distance bound to 0.425 and certify exactly four
levels below 0.1, qualifying the proposed staircase. The actual DH form has a
negative trial at C=31, despite passing finite ground gates and 6,400 tested
solid Toeplitz minors. A packet-dependent window-to-zero theorem includes an
explicit infinite tail; a universal ordinate-only region remains open.

The [canonical arithmetic/prolate comparison](research/prime_spectral/CANONICAL_PROLATE_ADJOINT_2026_10_11.md)
now has a [free-boundary and ground-angle improvement](research/prime_spectral/BOUNDARY_MOMENT_ADJOINT_2026_10_12.md):
full Weil ground-state Fourier errors are below 0.000948 at C=2 and
0.006274 at C=3 on abs(Re z)≤1, abs(Im z)≤0.4. The certificate retains the
unprojected candidate, its odd part, nonzero boundary terms and every residual
mode. Six abstract Hilbert-space lemmas are checked separately in Lean.
These fixed-support bounds do not establish an increasing-support Xi limit
for the ground states or RH.

The isolated [Xi and local eigenvector research objective](research/pseudo_hermitian/RESEARCH_OBJECTIVE.md)
records the coefficient normalization and zero-set corrections, and the new
domain-explicit pseudo-Hermitian reduction with relative defect and residual
bounds. The [Xi coefficient candidate](research/pseudo_hermitian/FOCK_CANDIDATE.md)
constructs a zero-independent operator domain and explicit unit-mass zero
states. Its required symmetry remains open. A separate written
[Hilbert-space domain argument](research/pseudo_hermitian/FOCK_DOMAIN_ESTIMATES.md)
has not been formalized or independently reviewed.

The [Xi divided-difference form](research/pseudo_hermitian/XI_DIVIDED_DIFFERENCE.md)
supplies a written bounded Hermitian form and domain symmetry, with checked
kernel identities and actual-domain Jordan obstructions. The
[approximate packet mass argument](research/pseudo_hermitian/APPROXIMATE_PACKET_MASS.md)
constructs nonzero masses without assuming simple zeros. Its required paired
residual control remains open. Generic mass lower bounds, normalization and
ordinary residual estimates are now checked in Lean, with a checked Xi kernel
packet realization for conditional simple off-critical pairs. The
[higher-jet mass bridge](research/pseudo_hermitian/HIGHER_JET_MASS_BRIDGE.md)
now checks coefficient-domain jets, finite multiplicity and a nonzero kernel
derivative at every Xi zero. Full Fock-space compatibility remains a written
proof without independent review. An optional checked norm criterion controls
the product of state
and residual norms at unit absolute mass. A checked real Jordan example shows
that criterion is stronger than the required paired-defect condition.

The [fixed algebraic jet construction](research/pseudo_hermitian/ALGEBRAIC_JET_MASS.md)
now checks unique finite coordinates inside the coefficient space, the restricted
arithmetic action and Xi-row domain, and one fixed Hermitian kernel-derivative
form. Every Xi zero has an actual nonzero cross-pairing for this form, giving
explicit packet mass bounds and unit absolute mass without assuming simplicity.
Action symmetry and the relative paired budget for this algebraic form remain
open; the full Fock-space claims retain their separate analytic obligations.

The [2026-09-13 implementation report](research/RH_IMPLEMENTATION_2026_09_13.md)
records the repaired classical Jensen interfaces, rigorous Xi coefficient balls,
finite-PF baseline, theta deficit laboratory, quantitative recurrence candidate,
and independent prime-defined Weil-form program. It supersedes older claims
about coefficient certification, quartic discriminant classifiers and universal
Hadamard cancellation. Historical manuscript and figures have not been regenerated.

The prime-defined track's [exact prolate residual-and-gap audit](research/prime_spectral/PROLATE_RESIDUAL_GAP_AUDIT_2026_09_26.md)
tests the canonical candidate in the certified Weil Fourier space. Its finite
Rayleigh quotients fail the strip theorem's clearance gate. The
[smooth-support derivative audit](research/prime_spectral/SMOOTH_SUPPORT_DERIVATIVE_2026_10_05.md)
gives finite, certified one-sided matrix and ground-profile derivatives,
including the prime-threshold jump; an all-support profile bound remains open.
The [closed Weil Taylor audit](research/prime_spectral/CLOSED_WEIL_TAYLOR_CELL_2026_10_05.md)
now encloses the full rank-8 even matrix and its derivative throughout the
17–19 support cell, with analytic remainder bounds and both boundary checks.
The [uniform even eigenfamily audit](research/prime_spectral/WEIL_EVEN_EIGENFAMILY_CELL_2026_10_05.md)
validates positive lowest even eigenvalues, spectral separation and an
origin-normalized candidate-profile error below `1.285e-9` throughout that
cell. The [full-cell ground and spatial audit](research/prime_spectral/WEIL_FULL_CELL_GATES_2026_10_05.md)
now closes the odd-parity and positive-kernel gates throughout that same
cell with degree-64 enclosures. An exact displacement argument also makes
nonzero spatial boundary follow from strict parity separation at any finite
rank. All-support/all-rank control and Xi identification remain open.
The [coupled density budget](research/prime_spectral/WEIL_STRIP_CELL_BUDGET_2026_10_05.md)
bounds exact profile increments across any two supports in that cell,
including spatial endpoint flux and certified transfer errors: below
`0.085421` on the height-`2/5` strip and `0.203537` on the height-`1` strip.
Infinite-path summability remains open.
The [infinite Fourier-tail audit](research/prime_spectral/WEIL_INFINITE_RANK_TAIL_2026_10_06.md)
now bounds all omitted even forcing modes `j>64` by `9.491e-12` in
`l2`, uniformly across that cell, using shared signed moments and an
effective geometric remainder. A discrete Hilbert commutator also gives
rank-independent operator bounds and explicit high-mode coercivity.
The intermediate-mode inverse response and all-rank profile budget remain open.
The [signed spectral-deflation audit](research/prime_spectral/DEFLATED_RANK_RESPONSE_2026_10_06.md)
reduces finite rank-transfer bounds by extracting two constrained low modes
before bounding complementary energy. High-mode coercivity also bounds the
number of potentially dangerous modes uniformly in rank on the 17–19 cell;
their inverse projections and cumulative budget remain uncontrolled.
The [residual-centered prolate audit](research/prime_spectral/COUPLED_PROLATE_RESIDUAL_2026_10_06.md)
checks the normalization and exact Fourier projection and sharpens Rayleigh
error transfer by up to 181,000 times in the tested cases. The canonical
prolate candidate still fails the finite residual-clearance gate.
The [common-parameter cumulative audit](research/prime_spectral/COMMON_SHIFT_CUMULATIVE_BUDGET_2026_10_06.md)
derives an absolute compact-profile rank budget conditional on two bounded
telescoping energies and gives an explicit changing-ground-parameter bound.
The finite joint energy bound loses rank alignment, the uniform constrained
gap remains open, and generic boundary dual energy diverges.

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

The active root module imports all proof-grade Lean modules:

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

## Research Exploration

### Creative Approaches Developed

This project has explored **7 novel mathematical approaches** to prove ZeroImUniqueness (the assertion that each imaginary height has at most one zero in the critical strip). These are documented in:

- `CREATIVE_BREAKTHROUGH_ATTEMPTS.md` - Overview of all 7 approaches
- `CREATIVE_RESEARCH_COMPLETE.md` - Summary of creative research phase

**Most Promising Approach: Near-Coincidence Impossibility**

The near-coincidence impossibility approach uses derivative bounds to prove zeros cannot be arbitrarily close:

1. **Hadamard Product** → Lower bound: |ζ'(ρ₁)| ≥ C/‖ρ₁-ρ₂‖
2. **Known Estimates** → Upper bound: |ζ'(ρ)| ≤ poly(T)
3. **Functional Equation** → Geometric packing constraints
4. **Synthesis** → "Scissors effect" forces uniqueness

**Status:** Complete theoretical framework in `NEAR_COINCIDENCE_COMPLETE.md` (~600 lines)

**Gap Identified:** Hadamard constant needs improvement from C ≈ 0.1 to C ≥ 50

**Research Files:**
- `research/HadamardProduct.lean.draft` - Derivative bound analysis
- `research/FunctionalEquationConstraints.lean.draft` - Geometric constraints
- `research/GeometricDerivativeSynthesis.lean.draft` - Combined synthesis
- `research/ZeroSeparation.lean.draft` - Separation theorems

### Other Approaches Documented

- **Li's Criterion** (RH ⟺ λₙ ≥ 0) - Most computational
- **Random Matrix Theory** (GUE statistics) - Strong physical intuition
- **Two-Framework Synthesis** - Inspired by unit distance proof methodology
- **Spectral Theory** (Hilbert-Pólya) - Requires operator construction
- **4 additional novel approaches** - See CREATIVE_BREAKTHROUGH_ATTEMPTS.md

### Research Draft Policy

Exploratory files with placeholders or conjectural axioms are preserved under
`research/*.lean.draft`. They are intentionally not imported by
`Reinmann.lean` and not scanned as verified Lean code. Promote a draft back into
`Reinmann/` only after replacing every placeholder and axiom with Lean-checked
proofs that pass `./scripts/safe-verify.sh`.

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
