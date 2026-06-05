# Critical Flaw in the Horizontal Line Argument

## The Claim

The Horizontal Line Argument claims:
> If ζ has two zeros ρ₁ = σ₁ + iγ and ρ₂ = σ₂ + iγ with σ₁ ≠ σ₂, 
> then by the identity theorem, ζ ≡ 0 on the segment [ρ₁, ρ₂],
> which contradicts isolated zeros.

## The Flaw

**The identity theorem does NOT apply to two isolated zeros.**

### What the Identity Theorem Actually Says

From Mathlib `AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero`:

```lean
theorem eqOn_zero_of_preconnected_of_frequently_eq_zero 
    (hf : AnalyticOnNhd 𝕜 f U) 
    (hU : IsPreconnected U)
    (h₀ : z₀ ∈ U) 
    (hfz₀ : ∃ᶠ z in 𝓝[≠] z₀, f z = 0) :  -- FREQUENTLY, not just at isolated points
    EqOn f 0 U
```

**Key requirement:** `∃ᶠ z in 𝓝[≠] z₀, f z = 0`

This means f = 0 **frequently** (infinitely often) in a punctured neighborhood of z₀.

### Why Two Isolated Zeros Don't Suffice

Two isolated zeros ρ₁ and ρ₂ do NOT satisfy the "frequently zero" condition:
- ρ₁ is NOT in closure({zeros} \ {ρ₁}) because zeros are isolated
- ρ₂ is NOT in closure({zeros} \ {ρ₂}) because zeros are isolated
- Neither zero accumulates to the other

### Counterexample

Consider f(z) = (z - ρ₁)(z - ρ₂)

- f is analytic everywhere (entire function)
- f(ρ₁) = 0 and f(ρ₂) = 0
- But f is NOT zero on the segment [ρ₁, ρ₂]
- In fact, f ≠ 0 at all points between ρ₁ and ρ₂

**Conclusion:** Two zeros do not force f ≡ 0 on the connecting segment.

## Why the Research Notes Claimed This Works

The notes at line 77-85 say:
> "**Key Lemma:** If f is analytic on a line segment [a,b] and f(a) = f(b) = 0 with a ≠ b, 
> then f ≡ 0 on [a,b]."

This is **FALSE** as stated.

The notes then say:
> "**Answer:** YES! ζ is analytic on {s : s ≠ 1}, which includes an open neighborhood of any 
> line segment in the critical strip not containing s = 1.
> Therefore: The identity theorem DOES apply! ✓"

This conclusion is **WRONG**. Being analytic in an open neighborhood is necessary but not sufficient.
You also need the zeros to **accumulate**, which isolated zeros do not.

## Assessment

The Horizontal Line Argument is **fatally flawed**.

The identity theorem requires:
- Analytic in open connected set ✓ (ζ satisfies this)
- Zeros accumulate at a point ✗ (isolated zeros don't accumulate)

Two isolated zeros are not enough to trigger the identity theorem.

## What Would Actually Work

To make this argument work, we would need:
1. **Infinitely many zeros** at the same height γ, OR
2. **A sequence of zeros** with same Im part that accumulates, OR
3. **A completely different mathematical principle**

None of these are available without already knowing RH or something equivalent.

## Conclusion

The Horizontal Line Argument does not prove ZeroImUniqueness.

The ~20-30% success probability in the research notes was too optimistic.

We need a different approach.

---

**Date:** 2026-06-05  
**Status:** Approach invalidated
