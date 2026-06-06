/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.XiToeplitzPositivity
import Mathlib.Data.Nat.Factorial.Basic

/-!
# The Moment-Kernel Mechanism for the Pólya-Frequency Frontier

This file isolates, and *verifies*, the precise analytic mechanism that governs
the open order-`≥3` Toeplitz (Pólya-frequency) minors of `XiToeplitzPositivity`.

**Correctness note (2026-06-06).** `Ξ` is now **Riemann's `ξ`** (see
`JensenProgram`), so Pólya's positive-kernel representation below genuinely applies
(it is a property of `ξ`, false for the earlier `Λ₀` slice).  `XiMomentKernelRep`
states that representation as a **named external classical input** (true, not RH,
not an axiom); the CNV/Pólya facts cited are external and **not formalized here**.

## The genuine obstruction (why order `≥ 3` is RH)

Riemann's **Pólya integral representation** (classical, elementary, NOT RH):
`Ξ(t) = 2∫₀^∞ Φ(u) cos(ut) du` with `Φ > 0`.  Expanding `cos` gives the Taylor
coefficients as **even moments** of the positive measure `Φ`:

  `XiCoeff n = (-1)^n · 2·Mₙ / (2n)!`,  `Mₙ := ∫₀^∞ Φ(u) u^{2n} du > 0`.

Hence the signed coefficients are `μₙ = (-1)^n·XiCoeff n = 2Mₙ/(2n)! > 0` — the
order-`1` minors are positive *for free*.

The crux: PF positivity needs `μ` to be **Toeplitz** totally positive
(log-concave at order 2, etc.), but the moment sequence `(Mₙ)` is **Hankel**
positive, hence **log-convex** `Mₙ² ≤ M_{n-1}M_{n+1}` — the *wrong* direction.
The factorial weights `(2n)!` carry the entire fight:

  `μₙ²/(μ_{n-1}μ_{n+1}) = (Mₙ²/M_{n-1}M_{n+1}) · ((2n+1)(2n+2)/((2n-1)(2n)))`,

a product of a `≤1` moment factor and a `>1` factorial-slack factor.  Order 1 is
free; order 2 (Turán) is the slack winning narrowly (why CNV needed the explicit
`Φ`); order `≥ 3` is the same battle at higher order and is genuinely open,
because the integral representation *structurally* yields Hankel (not Toeplitz)
positivity.

## What is verified here (honest, non-RH content)

* `weighted_logConcave_iff`, `logConcave_slack_iff` — general algebra of weighted
  log-concavity and the "slack" reweighting (true for all sequences).
* `factorial_slack_nat` / `factorial_slack_real` — the exact factorial identity
  `(2n)!·(2n+4)!·(2n+1)(2n+2) = ((2n+2)!)²·(2n+3)(2n+4)` providing the slack.
* `XiMomentKernelRep` — Pólya's positive-moment representation, stated as a NAMED
  external classical input (not an axiom, not assumed true here).
* `xiMomentCoeff_eq_of_kernelRep`, `xiMomentCoeff_pos_of_kernelRep` — under the
  representation, `μₙ = 2Mₙ/(2n)!` and the order-`1` minors are positive.
* `xiMoment_logConcave_iff_relaxedMoment_of_kernelRep` — under the representation,
  the order-`2` (Turán) minor is **equivalent** to the *relaxed* moment inequality
  `Mₙ·M_{n+2}·(2n+1)(2n+2) ≤ M_{n+1}²·(2n+3)(2n+4)`, exhibiting the slack
  `(2n+3)(2n+4) / ((2n+1)(2n+2)) > 1` explicitly.

None of this proves RH.  It is the verified anatomy of exactly where the open
analysis lives: defeating moment log-convexity by the factorial slack at order
`≥ 3`.
-/

noncomputable section

open scoped Nat

namespace Reinmann

/-! ## General algebra: weighted log-concavity and slack reweighting -/

/-- Clearing positive denominators in a weighted log-concavity comparison. -/
theorem weighted_logConcave_iff {a b c wa wb wc : ℝ}
    (hwa : 0 < wa) (hwb : 0 < wb) (hwc : 0 < wc) :
    (a / wa) * (c / wc) ≤ (b / wb) ^ 2 ↔ a * c * wb ^ 2 ≤ b ^ 2 * (wa * wc) := by
  rw [div_mul_div_comm, div_pow, div_le_div_iff₀ (by positivity) (by positivity)]

/-- **Slack reweighting.** If positive weights satisfy `wa·wc·P = wb²·Q`, then a
log-concavity comparison with the `(wa,wb,wc)` weights is equivalent to the same
comparison with the `(P,Q)` weights.  This is the abstract form of trading the
factorial weights for the elementary slack factor. -/
theorem logConcave_slack_iff {x y z wa wb wc P Q : ℝ}
    (hwb : 0 < wb) (hP : 0 < P) (hslack : wa * wc * P = wb ^ 2 * Q) :
    x * y * wb ^ 2 ≤ z ^ 2 * (wa * wc) ↔ x * y * P ≤ z ^ 2 * Q := by
  have hwb2 : 0 < wb ^ 2 := by positivity
  constructor
  · intro h
    nlinarith [mul_nonneg (sub_nonneg.mpr h) hP.le, hslack, hwb2]
  · intro h
    nlinarith [mul_nonneg (sub_nonneg.mpr h) hwb2.le, hslack, hP]

/-! ## The exact factorial slack identity -/

/-- The factorial identity that produces the slack factor:
`(2n)!·(2n+4)!·(2n+1)(2n+2) = ((2n+2)!)²·(2n+3)(2n+4)`. -/
theorem factorial_slack_nat (n : ℕ) :
    (2 * n).factorial * (2 * n + 4).factorial * ((2 * n + 1) * (2 * n + 2))
      = (2 * n + 2).factorial ^ 2 * ((2 * n + 3) * (2 * n + 4)) := by
  have e2 : (2 * n + 2).factorial = (2 * n + 2) * (2 * n + 1) * (2 * n).factorial := by
    rw [show 2 * n + 2 = (2 * n + 1) + 1 from rfl, Nat.factorial_succ, Nat.factorial_succ]
    ring
  have e4 : (2 * n + 4).factorial
      = (2 * n + 4) * (2 * n + 3) * (2 * n + 2).factorial := by
    rw [show 2 * n + 4 = (2 * n + 3) + 1 from rfl, Nat.factorial_succ,
        show 2 * n + 3 = (2 * n + 2) + 1 from rfl, Nat.factorial_succ]
    ring
  rw [e4, e2]; ring

/-- Real-cast form of the factorial slack identity. -/
theorem factorial_slack_real (n : ℕ) :
    ((2 * n).factorial : ℝ) * ((2 * n + 4).factorial : ℝ)
        * (((2 * n + 1) * (2 * n + 2) : ℕ) : ℝ)
      = ((2 * n + 2).factorial : ℝ) ^ 2 * (((2 * n + 3) * (2 * n + 4) : ℕ) : ℝ) := by
  exact_mod_cast factorial_slack_nat n

/-! ## Pólya's positive-moment representation (named external classical input) -/

/-- **Pólya's positive-moment representation of `Ξ`.** There is a positive
sequence `M` (the even moments `∫ Φ·u^{2n}` of Riemann's positive kernel `Φ`)
with `XiCoeff n = (-1)^n · 2·Mₙ / (2n)!`.

This is a *true classical theorem* (it follows from `Φ > 0`, which is elementary),
**not** RH and **not** an axiom — it is a named hypothesis whose Lean proof would
require the Fourier/heat-kernel construction of `Φ`, not yet in Mathlib. -/
def XiMomentKernelRep : Prop :=
  ∃ M : ℕ → ℝ, (∀ n, 0 < M n) ∧
    ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))

/-- Under the moment representation, the signed coefficient is the bare
factorial-weighted moment: `μₙ = 2Mₙ/(2n)!` (the sign cancels). -/
theorem xiMomentCoeff_eq_of_kernelRep {M : ℕ → ℝ}
    (hM : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))) (n : ℕ) :
    XiMomentCoeff n = 2 * M n / ((2 * n).factorial : ℝ) := by
  unfold XiMomentCoeff
  rw [hM n, ← mul_assoc,
      show (-1 : ℝ) ^ n * (-1) ^ n = 1 from by
        rw [← pow_add]; exact Even.neg_one_pow ⟨n, by ring⟩,
      one_mul]

/-- **Order-`1` positivity is free.** Under the moment representation, every signed
moment coefficient is positive. -/
theorem xiMomentCoeff_pos_of_kernelRep {M : ℕ → ℝ}
    (hMpos : ∀ n, 0 < M n)
    (hM : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))) (n : ℕ) :
    0 < XiMomentCoeff n := by
  rw [xiMomentCoeff_eq_of_kernelRep hM n]
  apply div_pos
  · linarith [hMpos n]
  · exact_mod_cast (2 * n).factorial_pos

/-! ## The order-`2` rung as a relaxed moment inequality (the slack made explicit) -/

/-- **The mechanism, verified.** Under the moment representation, the order-`2`
Toeplitz/Turán minor of the signed coefficients is *equivalent* to the **relaxed
moment inequality**
`Mₙ·M_{n+2}·(2n+1)(2n+2) ≤ M_{n+1}²·(2n+3)(2n+4)`.

The moments are log-convex (`Mₙ² ≤ M_{n-1}M_{n+1}`, the wrong way); the inequality
holds only because the factorial slack `(2n+3)(2n+4)/((2n+1)(2n+2)) > 1` overcomes
it.  Order `≥ 3` is the same battle at higher order — the genuine open frontier. -/
theorem xiMoment_logConcave_iff_relaxedMoment_of_kernelRep {M : ℕ → ℝ}
    (hM : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))) (n : ℕ) :
    XiMomentCoeff n * XiMomentCoeff (n + 2) ≤ XiMomentCoeff (n + 1) ^ 2 ↔
      (M n * M (n + 2)) * (((2 * n + 1) * (2 * n + 2) : ℕ) : ℝ)
        ≤ M (n + 1) ^ 2 * (((2 * n + 3) * (2 * n + 4) : ℕ) : ℝ) := by
  have hfac : ∀ k : ℕ, 0 < ((2 * k).factorial : ℝ) := fun k => by
    exact_mod_cast (2 * k).factorial_pos
  have hP : (0 : ℝ) < (((2 * n + 1) * (2 * n + 2) : ℕ) : ℝ) := by positivity
  have hwb : (0 : ℝ) < ((2 * n + 2).factorial : ℝ) := by exact_mod_cast (2 * n + 2).factorial_pos
  -- rewrite the three signed coefficients via the moment representation
  rw [xiMomentCoeff_eq_of_kernelRep hM n, xiMomentCoeff_eq_of_kernelRep hM (n + 1),
      xiMomentCoeff_eq_of_kernelRep hM (n + 2),
      show 2 * (n + 1) = 2 * n + 2 from by ring, show 2 * (n + 2) = 2 * n + 4 from by ring]
  -- clear denominators to the weighted form
  rw [weighted_logConcave_iff (hfac n) hwb (by exact_mod_cast (2 * n + 4).factorial_pos)]
  -- trade factorial weights for the slack factor
  rw [logConcave_slack_iff hwb hP (factorial_slack_real n)]
  -- cancel the common factor 4 from the doubled moments
  constructor
  · intro h; nlinarith [h]
  · intro h; nlinarith [h]

end Reinmann
