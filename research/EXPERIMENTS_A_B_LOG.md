# Iterative Experiments A & B: Zero-Free Region and Hilbert–Pólya

**Date:** 2026-06-05
**Verification:** `safe-verify.sh` exit 0 (16 files); all theorems below depend only
on `[propext, Classical.choice, Quot.sound]`.
**Spirit:** first-principles attacks; failures logged as stepping stones.

---

## Experiment B — Hilbert–Pólya (the bigger success)

### Hypothesis
The folklore "self-adjointness ⇒ critical line" can be turned from an *assumed*
clause into a *proved* mechanism, isolating the genuinely open part.

### What worked (verified)
- `symmetric_eigenvalue_conj_eq`: **eigenvalues of a symmetric operator are real**,
  proved from the inner-product axioms alone —
  `⟪Tv,v⟫ = ⟪v,Tv⟫ ⟹ conj μ · ⟪v,v⟫ = μ · ⟪v,v⟫ ⟹ conj μ = μ`. No spectral
  theorem, completeness, or boundedness needed.
- `spectralParam s = -i(s - 1/2)`, with `spectralParam_real_iff`:
  `μ(s)` real ⟺ `Re s = 1/2`. This is the encoding that converts "real spectrum"
  into "zeros on the line."
- `riemannHypothesis_of_symmetric_eigendata`: **if** a complex inner-product space
  carries a symmetric `T` with a nonzero eigenvector of eigenvalue `μ(s)` for every
  critical-strip zero `s`, **then** RH. Reality is *derived*, not assumed.

### Scrutiny / anti-vacuity check
Could a trivial `T` cheat? If `T = 0` then `heig` forces `μ(s) • v s = 0` with
`v s ≠ 0`, hence `μ(s) = 0`, i.e. `Re s = 1/2` — which is RH itself. So the
hypothesis cannot be satisfied trivially unless RH already holds. The implication
is therefore honest and correctly directed.

### What remains (the real open part)
Construct the triple `(E, T, v)`. This is the actual Hilbert–Pólya problem. What
the experiment *removed* is the hand-wave: the only thing left to supply is the
operator and eigenvectors; their reality (and hence RH) is automatic. This is a
strictly more honest formalization than an asserted `selfAdjoint_forces_criticalLine`.

### Why this is progress, not a restatement
The back-calculation lemma says any *faithful* sufficient condition is `≡ RH`. The
eigendata hypothesis is indeed `≥ RH` in strength — but the experiment's value is
that it factors that hypothesis through a *proved* lemma of independent content
(real eigenvalues), exposing exactly one external object to build.

---

## Experiment A — Zero-Free Region (engine isolated, region still open)

### Hypothesis
Reproduce the de la Vallée Poussin mechanism and see how far into the strip it can
be pushed with currently-formalized tools.

### What worked (verified)
- `cos_341_eq`: `3 + 4cosθ + cos2θ = 2(1+cosθ)²` — the exact algebraic engine.
- `cos_341_nonneg`: the positivity that makes every Euler factor cooperate.
- `cos_341_eq_zero_iff`: the boundary case is maximally rigid (`cos θ = -1` only).
- `zeroFreeRightOf_half_iff_riemannHypothesis`: the precise target — pushing the
  zero-free boundary to `Re = 1/2` *is* RH — with monotonicity `zeroFreeRightOf_mono`.

### What failed / what is missing (logged honestly)
- **Reaching into the strip failed with current Mathlib.** Converting the engine
  into a region `Re > 1 - c/log|t|` needs two analytic inputs Mathlib does not yet
  expose in usable form:
  1. the explicit logarithmic Euler series `log|ζ(σ+it)| = ∑_{p,k} k⁻¹p^{-kσ}cos(kt log p)`
     with its summability/interchange (Mathlib has `exp(∑ -log(1-p^{-s})) = ζ`,
     but not the term-by-term real-part cosine series ready to bound);
  2. growth bounds on `ζ` near `Re = 1` (Borel–Carathéodory / Hadamard
     three-circles) to convert `|ζ(σ)|³|ζ(σ+it)|⁴|ζ(σ+2it)| ≥ 1` into a quantitative
     boundary.
- Mathlib's own `riemannZeta_ne_zero_of_one_le_re` uses this very product trick but
  does not factor out a reusable quantitative region, so there was nothing to lift.

### Net result
The positivity engine is now a verified, reusable lemma in the project, and the
target is pinned. The missing pieces are *named analytic theorems*, not vague
gaps — a concrete to-do list for a future formalization push.

---

## Cross-experiment reading

Both experiments terminate at the same kind of boundary the cross-field analysis
predicted:

| Experiment | Verified core | Open external input | Nature of the gap |
|------------|---------------|---------------------|-------------------|
| B (Hilbert–Pólya) | real eigenvalues of symmetric `T` | construct `(E, T, v)` | build one operator |
| A (zero-free) | `3+4cosθ+cos2θ ≥ 0` | log-Euler series + growth bounds | analytic estimates |

Neither closes RH (by the back-calculation lemma, neither can without proving RH).
Both convert "magic" into a **single, sharply named missing object** — an operator
in B, two analytic estimates in A. That is the honest yield: the unknown is now
small, explicit, and machine-checkable once supplied.
