# The Moment-Kernel Mechanism: Why Order-≥3 Toeplitz Minors Are RH

**Date:** 2026-06-06
**Status:** honest frontier analysis + verified mechanism. **Not** a proof of RH.

## Bottom line

The order-`≥3` Toeplitz (Pólya-frequency) minors of the signed Ξ coefficients
**cannot be proved without proving RH** — they are RH. This document records the
genuine deep analysis of *why*, and the machine-verified anatomy of the
obstruction (`Reinmann/XiMomentKernel.lean`, standard axioms only). No axioms, no
`sorry`, no circular argument.

## The representation that controls everything

Riemann's **Pólya integral representation** (classical, elementary, NOT RH —
it follows from positivity of an explicit theta-type kernel):

```
Ξ(t) = 2 ∫₀^∞ Φ(u) cos(ut) du ,   Φ(u) > 0,  Φ even, rapidly decaying.
```

Expanding `cos(ut) = Σ_k (-1)^k (ut)^{2k}/(2k)!` term-by-term:

```
XiCoeff n = b_n = (-1)^n · 2 M_n / (2n)! ,   M_n := ∫₀^∞ Φ(u) u^{2n} du > 0.
```

So the **signed** coefficients are

```
μ_n = (-1)^n b_n = 2 M_n / (2n)!  > 0.
```

The `M_n` are the **even moments of the positive measure Φ(u)du**.

## The exact obstruction (the factorial battlefield)

RH ⟺ `μ` is a **Pólya frequency sequence** ⟺ all **Toeplitz** minors `det[μ_{i-j}] ≥ 0`
(Aissen–Edrei–Schoenberg–Whitney). PF sequences are **log-concave**.

But the moment sequence `(M_n)` is a **Hankel/Stieltjes** sequence, so it is
**log-convex** (Cauchy–Schwarz): `M_n² ≤ M_{n-1} M_{n+1}` — the *opposite*
curvature. The factorial weights carry the entire conversion:

```
   μ_n²                 M_n²                 (2n+1)(2n+2)
 ───────────  =  ─────────────────────  ·  ───────────────
 μ_{n-1}μ_{n+1}   M_{n-1} M_{n+1}            (2n-1)(2n)
                  └── ≤ 1 (moments) ──┘     └─ > 1 (slack) ─┘
```

This is the heart of the matter, and it is now **verified** in Lean
(`xiMoment_logConcave_iff_relaxedMoment_of_kernelRep`): under the Pólya
representation, the order-`2` Toeplitz/Turán minor is *equivalent* to the
**relaxed moment inequality**

```
M_n · M_{n+2} · (2n+1)(2n+2)  ≤  M_{n+1}² · (2n+3)(2n+4).
```

Interpretation per order:

| order | minor | status | why |
|------|--------|--------|-----|
| 1 | `μ_n ≥ 0` | **free** | `Φ > 0` ⟹ `M_n > 0` (`xiMomentCoeff_pos_of_kernelRep`) |
| 2 | Turán | **theorem (CNV)** | slack `(2n+3)(2n+4)/((2n+1)(2n+2))` beats moment log-convexity — *narrowly*, needs the explicit `Φ` |
| ≥3 | higher PF | **open = RH** | same battle at higher order; moment representation yields Hankel, not Toeplitz, positivity |

## Why this is a genuine wall, not a gap in effort

The natural analytic object — the integral representation — **structurally
produces the wrong (Hankel) positivity**. Karlin's basic composition formula
turns `μ_n = ∫ K(n,v) dσ(v)` into control of **Hankel** minors `det[μ_{i+j}]`
(indices add), never **Toeplitz** minors `det[μ_{i-j}]` (indices subtract). The
factorial weights `1/(2n)!` are precisely the data the moment problem cannot see;
converting Hankel-positivity-of-`M` into Toeplitz-positivity-of-`M/(2n)!` across
all orders **is** the statement that Ξ ∈ Laguerre–Pólya, i.e. RH.

Every known partial result fits this picture:

- **CNV / Csordas–Varga**: order-2 Turán and a few low-order Laguerre
  inequalities — the slack winning at small order, proven via the explicit `Φ`.
- **GORZ (2019)**: for each fixed degree `d`, Jensen polynomials are hyperbolic
  for all but finitely many `n` — the slack winning *asymptotically* (the ratio
  `(2n+3)(2n+4)/((2n+1)(2n+2)) → 1`, so it is a near-tie at large `n`, governed
  by Hermite asymptotics).
- The **open wedge** is finite-`n`, order-`≥3`: exactly where neither the
  small-order CNV technique nor the large-`n` GORZ asymptotics reaches.

## What was verified (`Reinmann/XiMomentKernel.lean`)

All with axioms `[propext, Classical.choice, Quot.sound]`:

- `weighted_logConcave_iff`, `logConcave_slack_iff` — general algebra of trading
  weights for the slack factor (true for *all* sequences; not about ζ).
- `factorial_slack_nat` / `factorial_slack_real` — the exact identity
  `(2n)!·(2n+4)!·(2n+1)(2n+2) = ((2n+2)!)²·(2n+3)(2n+4)`.
- `XiMomentKernelRep` — Pólya's positive-moment representation as a **named
  external classical input** (true, not RH, not an axiom; its Lean proof needs
  the Fourier/theta construction of `Φ`, absent from Mathlib).
- `xiMomentCoeff_eq_of_kernelRep`, `xiMomentCoeff_pos_of_kernelRep` — under the
  representation, `μ_n = 2M_n/(2n)!` and order-`1` positivity is free.
- `xiMoment_logConcave_iff_relaxedMoment_of_kernelRep` — the order-`2` minor ⟺
  the relaxed moment inequality, with the slack made explicit.

## Honest verdict

I cannot prove the order-`≥3` minors. They are RH. What is delivered is the
*verified mechanism*: the precise reduction of each PF rung to "factorial slack
vs moment log-convexity," the proof that orders 1–2 fall to it (free / CNV), and
the structural reason (Hankel ≠ Toeplitz under the moment map) that order `≥3` is
the genuine open analytic problem. This sharpens the target to a single,
sign-correct, falsifiable statement — the most honest progress possible without
solving RH itself.
