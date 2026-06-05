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
runs `lake build`.

```sh
./scripts/safe-verify.sh Reinmann.lean
```

With file arguments, the harness still scans every local `.lean` file for
shortcuts, then runs `lake env lean` on each target file.

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
- remaining obligation: prove `RightHalfStripZeroFree`

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
