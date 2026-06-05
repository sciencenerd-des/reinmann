# Reinmann Lean Verification Scaffold

This is a Lean/Lake scaffold for formal Riemann Hypothesis exploration. It does
not prove the Riemann Hypothesis. The project imports mathlib's formal
`RiemannHypothesis : Prop` target and verifies only reductions and supporting
lemmas that Lean can check.

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

With no arguments, the harness scans every `.lean` file outside `.lake/`, then
runs `lake build` and typechecks every active `.lean` file directly with
`lake env lean`.

```sh
./scripts/safe-verify.sh Reinmann.lean
```

With file arguments, the harness still scans every local `.lean` file for
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

- The precheck is lexical and conservative; it may reject forbidden words inside
  comments or strings.
- The precheck is not a full Lean parser and cannot prove that a development is
  mathematically complete or trustworthy.
- Passing this harness only means the scanned files avoid the listed shortcuts
  and typecheck with the configured Lean/Lake toolchain.
