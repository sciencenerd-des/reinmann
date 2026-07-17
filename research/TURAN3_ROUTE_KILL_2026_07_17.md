# Route-kill: local Turán data cannot close the order-3 contiguous rung

**Date:** 2026-07-17
**Status:** machine-checked falsification (`Reinmann/TuranRouteKill.lean`); not an RH result.

## Question investigated

The strict-ladder frontier `XiContigMinorStrictPositiveAt 3` asks for strict
positivity of every contiguous `3 × 3` Toeplitz minor of the signed xi moment
coefficients.  The nearest unconditional classical results are:

- second-order (ordinary) Turán inequalities — Csordas–Norfolk–Varga,
  *The Riemann hypothesis and the Turán inequalities*, Trans. AMS 296 (1986);
- third-order Turán inequalities — Dimitrov–Lucas,
  *Higher order Turán inequalities for the Riemann ξ-function*,
  Proc. AMS 139 (2011).

Question: is there a **sequence-level** implication

> positivity + strict 2nd-order Turán + 3rd-order Turán (on the five-term
> window `b₀,…,b₄`)  ⟹  `3 × 3` contiguous Toeplitz determinant ≥ 0 ?

If true, the `k = 3` rung would follow from named classical inputs by pure
algebra (and the machinery of `FeketeRowGap`/`FeketeAllOrders` would lift it).

## Answer: no

Counterexample, exact and machine-checked (`turan23_not_imp_toeplitz3`):

```
(b₀, b₁, b₂, b₃, b₄) = (1/100, 1, 5/4, 1, 1/100)
```

- positivity: all five entries positive;
- strict log-concavity: `b₁² = 1 > b₀b₂`, `b₂² = 25/16 > b₁b₃ = 1`,
  `b₃² = 1 > b₂b₄`;
- third-order Turán at both centers: margin `≈ 0.684` each;
- Toeplitz determinant:
  `b₂(b₂²−b₁b₃) − b₁(b₂b₃−b₁b₄) + b₀(b₃²−b₂b₄) = 45/64 − 31/25 + 79/8000
   ≈ −0.527 < 0`.

## Structure of the failure

The determinant is **linear and increasing in `b₄`** (coefficient
`b₁² − b₀b₂ > 0` by log-concavity), and at the log-concavity boundary
`b₄ = b₃²/b₂` it degenerates to the perfect square `(b₂² − b₁b₃)²/b₂ ≥ 0`.
The danger zone is small `b₀, b₄`: there the third-order Turán inequalities
relax to `3b₂² ≥ 4b₁b₃`, while determinant positivity at `b₄ = 0` needs the
strictly stronger `b₂³ + b₀b₃² ≥ 2b₁b₂b₃`.  Any window with
`4/3 ≤ b₂²/(b₁b₃) < 2` and depleted ends violates it.

## Consequence for the program

The `k = 3` rung cannot be closed by local `(2nd, 3rd)`-Turán data alone.
Closing it honestly requires xi-specific quantitative input, e.g.:

1. effective coefficient asymptotics (Griffin–Ono–Rolen–Zagier-style) giving
   the determinant's positivity for all offsets `m ≥ M`, plus
2. an interval-certified finite prefix `m < M` imported and checked in Lean.

Note the xi coefficients do **not** live near the counterexample's regime:
their windows have `b₂²/(b₁b₃) → 1⁺` with specific super-exponential decay,
which is exactly the information the local Turán window forgets.

RH remains unproved; this note prunes a dead branch.
