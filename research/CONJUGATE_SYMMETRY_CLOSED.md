# Gap #1 (Conjugate Symmetry) — CLOSED

**Date:** 2026-06-05
**Verification:** `scripts/safe-verify.sh` → exit 0 (10 Lean files, no `sorry`/`axiom`/`admit`)
**Axiom audit:** all key results depend only on `[propext, Classical.choice, Quot.sound]`

---

## What was independently verified

The prior findings reproduced and re-checked under `safe-verify.sh`:

- `ConjugateHalfPlane.lean`: `ζ(conj s) = conj (ζ s)` for `1 < re s`
  (Dirichlet series, term-by-term), plus half-plane openness/convex
  connectedness — all clean.
- `ZeroSymmetry.lean`: the reduction `RH ↔ NoSameImaginaryPartCollision`
  *under* a `StripConjugateZeroSymmetry` hypothesis, with the full
  `ZeroImUniqueness` / fiberwise-uniqueness equivalence lattice.

## The next gap, now closed

Previously the global statement `ζ(conj s) = conj (ζ s)` for all `s ≠ 1` was
left as "a separate analytic-continuation gap" because complex conjugation is
anti-holomorphic. **This gap is now fully closed** in
`ConjugateSymmetryComplete.lean`:

### Method (identity theorem)

1. The reflected map `g s = conj (ζ (conj s))` is holomorphic on `{1}ᶜ`,
   because `conj ∘ f ∘ conj` is holomorphic when `f` is
   (`DifferentiableAt.conj_conj`, Mathlib).
2. `ζ` is analytic on `{1}ᶜ` (`analyticOn_riemannZeta`).
3. On the open half-plane `1 < re s`, the verified Dirichlet result gives
   `ζ s = g s`, hence `ζ =ᶠ[𝓝 2] g`.
4. `{1}ᶜ` is preconnected (`isConnected_compl_singleton_of_one_lt_rank`), so the
   identity theorem (`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`)
   forces `ζ = g` on all of `{1}ᶜ`.
5. Evaluating at `conj s` yields `ζ(conj s) = conj (ζ s)` for every `s ≠ 1`.

### New theorems (all `sorry`/axiom-free)

- `riemannZeta_conj : ∀ s ≠ 1, ζ(conj s) = conj (ζ s)`
- `conjugateSymmetry_proved : ConjugateSymmetry`
- `stripConjugateZeroSymmetry_proved : StripConjugateZeroSymmetry`

## Consequence: RH reduces to a single statement

`RiemannHypothesisReduction.lean` now removes the conjugate-symmetry side
condition everywhere, giving an **unconditional** equivalence:

```
riemannHypothesis_iff_zeroImUniqueness : RiemannHypothesis ↔ ZeroImUniqueness
riemannHypothesis_of_zeroImUniqueness  : ZeroImUniqueness → RiemannHypothesis
```

plus the no-collision and fiberwise-uniqueness reformulations.

## Status of the two original gaps

| Gap | Status |
|-----|--------|
| Conjugate symmetry (`StripConjugateZeroSymmetry`) | **PROVED** (theorem) |
| `ZeroImUniqueness` (≤ 1 zero per imaginary height) | **OPEN** — the entire remaining content of RH |

The whole difficulty of RH is now isolated in the single arithmetic target
`ZeroImUniqueness`.
