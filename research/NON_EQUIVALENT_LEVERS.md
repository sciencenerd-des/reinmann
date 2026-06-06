# Beyond the Tight Reduction: Candidate Non-RH-Equivalent Levers

**Date:** 2026-06-06
**Status:** strategy. Honest about what is equivalent to RH and what is not.

## Where we stand (verified)

- `RHReductionCapstone`: RH ⟺ `XiToeplitzTotalPositive` (order-`≥3` Toeplitz
  positivity of Riemann-`ξ` coefficients), *given* the classical bridges
  (Edrei–ASW, LP closure, Pólya–Jensen). The reduction is **tight** — the lone
  open input is provably RH-equivalent, so it cannot be "postulated" as progress.
- `XiMomentKernel`: under Pólya's `Φ>0` representation, order `n`-rungs reduce to
  factorial-slack-vs-moment-log-convexity; the order-`2` slack factor
  `s_n = (2n+3)(2n+4)/((2n+1)(2n+2))` is `>1` and strictly decreasing to `1`
  (`one_lt_slackFactor`, `slackFactor_succ_lt`).

A genuine lever must be a statement that **implies RH but is not a restatement of
the zero locus** — its truth attackable by methods foreign to the zeros. Three
candidates, with the precise object each must produce.

## Lever 1 — Quantitative moment regularity of `Φ` (analysis on one explicit function)

**Object.** A concrete inequality on the even moments `M_n = ∫₀^∞ Φ(u) u^{2n} du` of
Riemann's explicit positive kernel `Φ`, sufficient to force PF positivity at all
orders. The order-`2` form is `M_{n+1}²/(M_n M_{n+2}) ≥ 1/s_n` (verified
equivalent to Turán). The general form is a **factorial-weighted Hankel/Toeplitz
positivity of `(M_n)`**.

**Why not obviously RH-equivalent.** This is a property of a *single, explicitly
defined* smooth function `Φ` (a theta-type series). It is attacked by hard analysis
(saddle point, log-concavity of integral transforms, Laguerre/Laplace methods) on
`Φ` — never by locating zeros. CNV (order 2) and the higher Laguerre inequalities
(Csordas–Varga; Dimitrov) are exactly such results, proven this way. The lever is
"push the moment-regularity estimates of `Φ` to all orders, uniformly."

**Formalizable now.** The reduction order-`n` ⟶ moment inequality (we have order 2);
`Φ`'s definition and `M_n` would need Mathlib Mellin/theta infrastructure.

## Lever 2 — Heat-flow contraction (de Bruijn–Newman, `Λ ≤ 0`)

**Object.** A strictly dissipative Lyapunov functional for the backward-heat-flow
zero dynamics of `Ξ`, with the all-real configuration as global attractor, yielding
the de Bruijn–Newman bound `Λ_{dBN} ≤ 0`. Combined with Rodgers–Tao (`Λ ≥ 0`,
proven) this gives `Λ = 0` ⟺ RH.

**Why not obviously RH-equivalent.** The handle is PDE/entropy: monotonicity under a
heat semigroup proven by differential inequalities, the same toolkit Rodgers–Tao
used for the matching half. The content is dynamical regularity, not zero-counting.

**Formalizable now.** Only the *definitions* (`H_t`, `Λ_{dBN}`) and the
re-expression `Λ_{dBN}=0 ↔ RH` in our fiber-energy language; the heat kernel on `ξ`
is not in Mathlib.

## Lever 3 — Pseudo-Hermitian / PT realization (operator positivity)

**Object.** An operator `H` with spectrum `{γ_k}` and a positive metric `η` making
`H` `η`-self-adjoint (Mostafazadeh pseudo-Hermiticity; Bender–Brody–Müller). Then
RH ⟺ `η` positive-definite (unbroken PT ⟺ real spectrum), using our verified
`zetaInvolution` (fixed-point set = critical line) as the geometric PT operator.

**Why not obviously RH-equivalent.** The handle is operator theory + a positivity
(quadratic-form) condition — tools independent of the zeros. "Unbroken PT ⟺ real
spectrum" is a theorem about operators, not a restatement of RH.

**Formalizable now.** The *reduction* (a pseudo-Hermitian witness `(E,η,H)` ⟹ RH)
adapts our `symmetric_eigenvalue_conj_eq`; the existence of `(H,η)` is the open part.

## Honest ranking

1. **Lever 1** is closest to verified ground: we have the order-`2` reduction and
   the slack quantification; it rests on hard analysis of one explicit function,
   exactly where CNV/Dimitrov already succeeded at low order. The open content is a
   *uniform* moment estimate — hard, but a concrete analysis problem, not a
   zero-locus tautology.
2. **Lever 2** is the deepest analytic bet, anchored by a celebrated half-result.
3. **Lever 3** yields an immediately formalizable reduction artifact; existence open.

None is a proof. Each is a target whose *truth* would be established by machinery
foreign to the zeros — the only kind of input that can advance, rather than
restate, RH.
