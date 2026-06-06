# Experiment Log: Attacking the Moment-Determinant Ladder with Numerics

**Date:** 2026-06-06
**Tool (foreign to the zeros):** high-precision numerics on Riemann's `ξ`
(`scripts/moment_determinant_experiment.py`, mpmath, 80 digits).

## What was tested

Verified reduction (`Reinmann/XiMomentKernel.lean`,
`xiToeplitzContigMinor_nonneg_iff_moment_of_kernelRep`):

> RH ⟺ for all `k, m`: `0 ≤ det[ μ_{m+i-j} ]`, where `μ_n = (-1)^n b_n`,
> `b_n = [t^{2n}] ξ(1/2+it)`.

We computed the actual `b_n` (hence `μ_n`) to 80 digits and measured positivity
**and margins**.

## Findings

1. **Order-1 (`μ_n > 0`): holds** — as forced by `Φ > 0`.

2. **Order-2 is comfortable — `μ` is genuinely log-concave.** The moment ratio
   `R_n = μ_{n+1}²/(μ_n μ_{n+2})` is `> 1` for every `n` (2.15, 1.59, 1.41, …,
   1.12 at `n=10`), decreasing toward `1`. The factorial-slack threshold
   `1/s_n = (2n+1)(2n+2)/((2n+3)(2n+4))` rises toward `1` from below. So Turán
   holds with a *double* safety margin: `R_n > 1 > 1/s_n`. The order-2 rung does
   **not** even need the slack — `μ` is outright log-concave.

3. **High-order PF ladder holds.** Every contiguous Toeplitz minor
   `det[μ_{m+i-j}]` for `k = 1..6` and all tested offsets is **strictly positive**
   (values from `~0.5` down to `~10^{-105}` — the smallness is pure scale from the
   factorial decay of `μ_n`, not near-degeneracy; no sign changes).

4. **Jensen hyperbolicity holds.** `J_{d,n}` for `d = 2, 3, 4` has all-real roots
   (max `|Im root| = 0` to working precision) for every computed `n`.

**Conclusion.** The reduction's premise is confirmed numerically: for ξ, the signed
coefficients form (empirically) a Pólya-frequency sequence, low orders with room
to spare. The difficulty is therefore **not** at low order — it is **uniformity**.

## The precise open targets this localizes (each attackable by foreign tools)

### Target A — Uniform total positivity (the crux)
Prove `det[μ_{m+i-j}] ≥ 0` for **all** `k, m` (not just small `k`).
*Foreign tools:* Karlin's total-positivity theory; the variation-diminishing
property of the kernel `cosh(u√z)` (since `Σ μ_n z^n = ∫₀^∞ Φ(u) cosh(u√z) du`);
Schoenberg's theory of Pólya-frequency *functions*. The clean sub-question: is the
map `u ↦ Φ(u)` such that the kernel `(n,u) ↦ u^{2n}/(2n)!` composed against `Φ`
yields a PF sequence? This is a statement about the explicit positive `Φ`, never
about zeros.

### Target B — Asymptotic margin `R_n → 1`, `1/s_n → 1`
The data shows `R_n - 1 > 0` shrinking and `1 - 1/s_n` shrinking. The order-2
asymptotic crux is the rate: `R_n - 1 ∼ ?` vs `1 - 1/s_n ∼ 8/(2n)² `.
*Foreign tools:* Griffin–Ono–Rolen–Zagier Hermite asymptotics of the normalized
Jensen polynomials, made effective and uniform in `d`. The data's monotone
`R_n ↓ 1` is the empirical shadow of the Hermite limit.

### Target C — `μ` log-concavity from the shape of `Φ` (cleanest)
The strongest empirical fact is `R_n > 1` (μ log-concave), i.e.
`μ_{n+1}² > μ_n μ_{n+2}` for all `n` — *stronger* than slack-Turán. Since
`μ_n = 2∫Φ u^{2n}/(2n)!`, this is a concrete inequality between weighted moments
of the explicit `Φ`. *Foreign tools:* log-concavity / Pólya-frequency-function
structure of `Φ`, classical moment inequalities (Cauchy–Schwarz with corrections),
Laplace/saddle-point asymptotics. Proving `R_n > 1` for all `n` would give the
order-2 rung unconditionally with the *correct* (now ξ-targeted) coefficients.

## Honest status

This is evidence and target-localization, not a proof. It shows: (i) the reduction
is sound and its premise holds for ξ at all tested orders; (ii) the genuine open
content is *uniform* high-order total positivity / the `n→∞` margin, attackable by
Karlin TP, Schoenberg PF-functions, and GORZ Hermite asymptotics — all tools about
the explicit positive kernel `Φ`, none about the zeros.
