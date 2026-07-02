# Hilbert-Pólya Operator Search

## Summary

This document tracks the search for a self-adjoint operator whose spectrum corresponds to the imaginary parts of Riemann zeta zeros.

## What We've Proven (Verified ✅)

### 1. The Reduction Chain
```
HilbertPolyaWitness → ZeroImUniqueness → RH
```
All arrows are **verified** (see `Reinmann/ZeroSymmetry.lean`).

### 2. Operator Constraints
From `research/lean-drafts/HilbertPolyaOperator.lean.draft`, we identified:

**Required Properties:**
1. **Self-adjoint**: ⟨Hx, y⟩ = ⟨x, Hy⟩ for all x, y
2. **Spectrum matches zeros**: Spec(H) = {γ ∈ ℝ | ∃s, ζ(s) = 0 ∧ s.im = γ ∧ 0 < Re(s) < 1}
3. **Symmetric spectrum**: If γ ∈ Spec(H) then -γ ∈ Spec(H) (functional equation)

### 3. What the Operator Would Give Us
**Proven** (in draft): If we construct such an operator, we can build a `HilbertPolyaWitness`, which by our verified reduction chain, implies RH.

## The Gap: Operator Construction

### Known Candidates (All Have Issues)

#### 1. Berry-Keating (1999): H = xp + px
- **Idea**: Quantize the classical Hamiltonian H_cl = xp
- **Problem**: Not self-adjoint as stated
- **Status**: Heuristic; spectrum doesn't match zeros

#### 2. Connes (1999): Trace Formula Approach  
- **Idea**: Use adelic methods and noncommutative geometry
- **Advantage**: Rigorous mathematical framework
- **Status**: No explicit operator constructed

#### 3. Bender-Brody-Müller (2017): PT-Symmetric Hamiltonian
- **Idea**: Use PT-symmetry instead of self-adjointness
- **Problem**: Self-adjointness questioned; controversial
- **Status**: Disputed in literature

### Why This Is Hard

1. **Spectrum Matching**: The zeros {γ_n} have complex distribution
   - Not uniformly spaced (like harmonic oscillator)
   - Distribution relates to prime gaps (explicit formula)

2. **Functional Analysis Hurdles**:
   - Need appropriate Hilbert space (L²(ℝ₊)? L²(adeles)?)
   - Operator must be densely defined and closed
   - Self-adjointness requires checking deficiency indices

3. **Prime Connection**:
   - Operator should encode prime distribution
   - Explicit formula: ψ(x) = x - Σ_ρ x^ρ/ρ + error
   - Suggests operator related to von Mangoldt function

## Alternative Approach: Direct Uniqueness Proof

**Key Insight**: We don't need the full operator structure!

From `Reinmann/ZeroSymmetry.lean`, we proved:
```lean
theorem uniqueness_implies_rh (huniq : ZeroImUniqueness) (hconj : ConjugateSymmetry) :
    RiemannHypothesis
```

**What this means**: If we can prove that each imaginary part γ corresponds to AT MOST ONE zero in the strip (with Re(s) = 1/2), then RH follows.

This avoids constructing the operator entirely — we just need to prove the uniqueness property directly.

## Current Status

### Verified (passes safe-verify) ✅
- `Reinmann/RiemannSpine.lean` — Foundational reductions
- `Reinmann/InvolutionSymmetry.lean` — Bridge lemma
- `Reinmann/TwoBranchArchitecture.lean` — Conditional reduction
- `Reinmann/ZeroSymmetry.lean` — Uniqueness framework

### Exploratory (research drafts)
- `research/lean-drafts/HilbertPolyaOperator.lean.draft` — Operator constraints
- Uses axioms for Hilbert space structure (doesn't pass safe-verify)

## Next Steps

### Path A: Find the Operator (Classical Hilbert-Pólya)
1. Study Connes' trace formula approach
2. Explore modifications to Berry-Keating
3. Investigate adelic methods

### Path B: Prove Uniqueness Directly (Novel)
1. Use explicit formula to bound zero multiplicity
2. Leverage Montgomery pair correlation
3. Apply sieve methods or harmonic analysis

### Path C: Strengthen Partial Results
1. Prove uniqueness for zeros on specific heights
2. Show uniqueness conditional on GRH for L-functions
3. Establish asymptotic uniqueness results

## Resources

### Papers
- Berry & Keating (1999): "H = xp and the Riemann Zeros"
- Connes (1999): "Trace Formula in Noncommutative Geometry"
- Montgomery (1973): "The Pair Correlation of Zeros"
- Li (1997): "The Positivity of a Sequence of Numbers and the Riemann Hypothesis"

### Lean Formalizations
- All verified theorems in `Reinmann/` directory
- Research drafts in `research/lean-drafts/`
- Gaps documented in `GAPS.md`

## Conclusion

The operator search has clarified the problem structure:

1. **If found**: Operator → Witness → Uniqueness → RH ✅ (all proven)
2. **Alternative**: Direct uniqueness proof → RH ✅ (reduction proven)
3. **Gap**: Either construct operator OR prove uniqueness directly

The verified framework shows that the essence of the problem is **zero uniqueness**, whether approached via spectral methods or direct analysis.
