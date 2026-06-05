# A Theory of de la Vallée Poussin Certificates (Experimental)

**Date:** 2026-06-05 · `safe-verify` exit 0 (20 files) · axioms only
`[propext, Classical.choice, Quot.sound]`.

---

## First-principles ideation

The named open input for the zero-free direction was "the positivity engine + the
analytic inputs." Stripping the analytic part away, the *combinatorial* heart is a
nonnegative cosine polynomial with a specific coefficient gap. We isolated the two
structural properties that actually do the work:

1. **nonnegativity** `∑ cₖ cos(kθ) ≥ 0` (makes the Euler-product log-sum `≥ 0`);
2. **the gap `c₀ < c₁`** (pole weight `c₀` < boundary-zero weight `c₁`), giving net
   vanishing exponent `c₁·m − c₀ > 0` for a zero of order `m ≥ 1`.

Anything with these two properties is a **certificate**. The classical
`3 + 4cosθ + cos2θ` is the smallest one.

## The family we generated and verified

From `(1+cosθ)ⁿ ≥ 0` (trivially nonnegative — `one_add_cos_pow_nonneg`) we produced
an infinite family by expanding into the cosine basis:

| n | identity (`= 2ⁿ⁻¹(1+cosθ)ⁿ`) | (c₀,c₁) | gap c₁/c₀ | theorem |
|---|------------------------------|---------|-----------|---------|
| 2 | `3+4c+cos2θ` | (3,4) | 1.333… | `certificate_two` |
| 3 | `10+15c+6cos2θ+cos3θ` | (10,15) | 1.5 | `certificate_three` |
| 4 | `35+56c+28cos2θ+8cos3θ+cos4θ` | (35,56) | 1.6 | `certificate_four` |

Each is **proved** to equal `2ⁿ⁻¹(1+cosθ)ⁿ` (via `cos_two_mul`, `cos_three_mul`)
and hence **proved nonnegative** (`certificate_{two,three,four}_nonneg`).

## The general criterion (verified)

`general_vdp_net_exponent_pos`: for any `0 ≤ c₀ < c₁` and `m ≥ 1`,
`0 < c₁·m − c₀`. This generalizes the `(3,4)` case to the whole family, and it is
the exact algebraic reason a boundary zero is impossible (it composes with the
verified `product_bound_contradiction` from `VdpConditional`).

## Experimental findings (verified numerics)

- `certificate_ratios_strictly_increasing`: `4/3 < 15/10 < 56/35` — the gap ratio
  **strictly increases** with the order.
- `certificate_ratios_below_two`: all observed ratios are `< 2`.

**Conjecture from the data (not proved):** `c₁/c₀ ↗ 2` as `n → ∞`. The threshold
`2` is significant: a larger gap ratio lets the *same* contradiction argument push
the zero-free boundary further left into the strip. So the higher-order
certificates are precisely the instruments for a *quantitative* region — and they
cost nothing in nonnegativity, since they all descend from `1 + cosθ ≥ 0`.

## What this contributes

- A reusable, verified **family** of positivity certificates (not just the single
  classical one), with the structural criterion that makes any of them work.
- A clean separation: the certificate side is now *fully formalized theory*; the
  only remaining inputs for an actual region are the two named analytic facts
  (log-Euler series, growth bounds) consumed as hypotheses by
  `product_bound_contradiction`.
- Honest experimental data (`c₁/c₀` behaviour) generated and machine-checked,
  pointing at where the quantitative strength comes from.

No `sorry`, no `axiom`. Nothing here proves RH; it develops and verifies the
combinatorial engine theory and reports its experimental behaviour.
