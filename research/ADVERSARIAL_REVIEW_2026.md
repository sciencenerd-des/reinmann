# Adversarial Academic Review of the RH Development

**Date:** 2026-06-06
**Reviewer stance:** hostile referee (analytic number theorist + formal-methods
auditor). Goal: separate genuine novel non-trivial progress from (a) formalization
of known facts, (b) RH-equivalent restatements, (c) scaffolding, and to find
errors.

## Verdict up front

**No result in this development constitutes genuinely novel, non-trivial
mathematics that advances a proof of RH.** Everything verified is one of:
classical fact re-formalized, an RH-equivalent restatement (zero progress by
construction), a named external hypothesis (the hard part, deferred), or an honest
negative result. **Lean soundness is intact** — no false theorem is *proved*; the
RH-linking statements are all unproven `Prop`s. However, **one sub-program (Jensen
/ Toeplitz / moment) is built on the wrong function** and its bridges are therefore
not merely unproven but most likely **false as stated**.

---

## FINDING 1 (critical, mathematical error): the Xi-program targets Λ₀, whose zeros are not the Riemann zeros

`JensenProgram.Xi t := (completedRiemannZeta₀ (1/2 + t·I)).re` builds the entire
Laguerre–Pólya / Jensen / Toeplitz / moment program on **Λ₀ = `completedRiemannZeta₀`**.

Mathlib (`RiemannZeta.lean:85`): `completedRiemannZeta s = completedRiemannZeta₀ s − 1/s − 1/(1−s)`,
i.e. `Λ₀ = Λ + 1/s + 1/(1−s)` where `Λ = π^{-s/2}Γ(s/2)ζ(s)` (`completedRiemannZeta`).

- Zeros of `Λ` in the strip = nontrivial zeros of `ζ` (since `Gammaℝ ≠ 0`).
- At any nontrivial zero `ρ`: `Λ₀(ρ) = Λ(ρ) + 1/ρ + 1/(1−ρ) = 0 + 1/ρ + 1/(1−ρ) ≠ 0`
  (vanishing would need `1 = 0`). **So no Riemann zero is a zero of Λ₀.**
- On the line: `Λ(1/2+it) = −2·Ξ_R(t)/(t²+1/4)` (Ξ_R = Riemann's xi), so
  `Λ₀(1/2+it) = (1 − 2·Ξ_R(t))/(t²+1/4)`. Its zeros are where **Ξ_R(t) = 1/2**,
  not where Ξ_R(t)=0.

**Consequences.**
- `PolyaJensenBridge : RiemannHypothesis ↔ AllJensenHyperbolic` is (almost
  certainly) a **false** proposition: `AllJensenHyperbolic` is real-rootedness of
  `Λ₀(1/2+i·)`, equivalent to "all solutions of Ξ_R(t)=1/2 are real", unrelated to RH.
- `XiTuran2All` is **misattributed**: the Csordas–Norfolk–Varga Turán inequalities
  are for Riemann's ξ, *not* for Λ₀'s Taylor coefficients. The repeated claim
  "order-2 rung is a proven theorem (CNV)" is therefore **unjustified** for `XiCoeff`.
- `XiMomentKernelRep` is dubious/false for Λ₀: Pólya's `Φ>0` cosine-transform
  representation is a property of ξ, not of Λ₀'s slice `(1−2Ξ_R)/(t²+1/4)`.
- Every witness bundling these (`XiToeplitzPositivityWitness`,
  `XiTotalPositivityApertureWitness`, `riemannHypothesis_of_xi…`) rests on a false
  premise; they are vacuously safe in Lean but worthless as a route to RH.

**The fix.** The correct entire object is Riemann's ξ, which *preserves* the zeros
because it removes Λ's poles by **multiplying** by `s(s−1)/2` (not by adding
`1/s+1/(1−s)`):
`ξ(s) = (s(s−1)/2)·Λ(s) = (s(s−1)/2)·Λ₀(s) + 1/2`.
On the line: `Ξ_R(t) = (1 − (t²+1/4)·Λ₀(1/2+it))/2`. The program must be rebuilt on
`Ξ_R` (with the `(t²+1/4)` weight and the `+1/2`), not on `Λ₀` raw. Until then the
Jensen/Toeplitz/moment files are formally valid but mathematically off-target.

Note the repo *already contains the correct function elsewhere*:
`CriticalLineRealSlice.Zslice t = (completedRiemannZeta (1/2+it)).re` uses **Λ**, and
`Zslice_eq_zero_iff` correctly reduces to `riemannZeta(1/2+it)=0`. The counting
machinery is sound; the LP program simply chose the wrong completed-zeta variant.

---

## FINDING 2: the RH-equivalence chain is correct but is, by construction, zero progress

`riemannHypothesis_iff_zeroImUniqueness`, `…_iff_forall_fiberEnergy_zero`,
`zeroFreeRightOf_half_iff_riemannHypothesis`, `XiToeplitzTotalPositive`(→RH), etc.
are genuine equivalences/implications. But:

- They are **RH-equivalent restatements**. Trading "all zeros on the line" for
  "≤1 zero per height" or "all fiber energies vanish" or "Toeplitz TP" relocates
  the difficulty; it does not reduce it.
- The "back-calculation lemma" ("any faithful sufficient condition is ≡ RH") is
  **near-tautological**: "faithful" is defined as `RH → P`, so `P → RH` plus
  faithful is `P ↔ RH` by definition. Dressing this as a lemma overstates it.

Honest value: these are clean **formalizations**, useful as scaffolding, with no
bearing on hardness.

---

## FINDING 3: the "new theorems about ζ′" are classical and trivial-from-symmetry

`deriv_riemannZeta_conj` (`ζ′(s̄)=conj ζ′(s)`) and `deriv_riemannZeta_zero_conj`
are correct but are the **Schwarz reflection** principle applied to a function with
real Dirichlet coefficients — entirely classical, and the ζ′ versions are immediate
corollaries of the ζ version. `SpeiserLeftHalfZeroFree`/`SpeiserBridge` are correct
*definitions* of a classically-RH-equivalent target (Speiser 1934), unproved.
**Not novel mathematics.** Formalization value only.

Same category: `riemannZeta_conj`, `completedRiemannZeta(₀)_real_on_critical_line`,
`fiber_centroid_eq_half` (elementary: zeros at a height pair under `ρ↦1−ρ̄`,
averaging to ½) — all correct, all classical/elementary.

---

## FINDING 4: the 3-4-1 / Euler-positivity work is the classical Mertens argument

`zeta_341_modulus` (`‖ζ(σ)³ζ(σ+it)⁴ζ(σ+2it)‖ ≥ 1`) and
`no_zeta_zero_on_re_eq_one` reproduce the **standard** de la Vallée Poussin /
Mertens 3-4-1 proof that `ζ(1+it) ≠ 0` (Mathlib already has
`riemannZeta_ne_zero_of_one_le_re`). Correct, well-known, not novel.

The `CertificateBarrier` (gap ratio `2n/(n+1) < 2`) is an **honest negative
result**: it shows the 3-4-1 certificate family cannot reach `Re = 1/2`. This is
mildly original as a *formalized* obstruction but only confirms folklore (3-4-1
gives zero-free regions near `Re=1`, never RH).

---

## FINDING 5: Hilbert–Pólya content is the textbook heuristic; existence deferred

`symmetric_eigenvalue_conj_eq` ("symmetric operator ⇒ real eigenvalues") is
standard linear algebra. `riemannHypothesis_of_symmetric_eigendata` and the
`HilbertPolyaWitness'` packaging encode the **classical Hilbert–Pólya conjecture**:
*if* an operator with spectrum `{γ_k}` exists then RH. Existence — the entire
content — is an unproved hypothesis. The file itself documents the
unbounded-operator obstruction. No progress on existence.

---

## What is genuinely sound and worth keeping

- The **critical-line real-slice + Hardy-Z sign-change counting**
  (`Zslice`, `riemannZeta_critical_zero_of_sign_change`, the alternating-sign
  counting) — correct, uses the right function (Λ), genuinely detects real zeros of
  ζ. This is solid (if classical) formalization.
- The **axiom hygiene**: everything reduces to `[propext, Classical.choice,
  Quot.sound]`; the `safe-verify` discipline (no `sorry`/`axiom`) is real and
  maintained.
- The **honest negative results** (certificate barrier) and the **correct
  identification** that total positivity for LP is Toeplitz/Edrei–ASW (the
  *framework* is right even though it was applied to the wrong function).

## What must be retracted or fixed

1. **Rebuild the Jensen/Toeplitz/moment program on Ξ_R = (1 − (t²+1/4)Λ₀(1/2+i·))/2**
   (Riemann's ξ), not on `Λ₀` raw. Current `Xi`, `XiCoeff`, `XiTuran2`,
   `XiToeplitz*`, `XiMomentKernelRep` are off-target.
2. **Retract the "CNV proves order-2"** claim until `XiCoeff` are ξ's coefficients.
3. **Downgrade language** in commit messages/docs that frames RH-equivalent
   restatements or classical formalizations as "new mathematics / progress."

## Resolution status (2026-06-06)

- **Finding 1 — FIXED.** `JensenProgram.Xi` is rebuilt on Riemann's `ξ`:
  `xiCompleted s = (s(s-1)/2)·completedRiemannZeta s`,
  `Xi t = -((t²+1/4)/2)·Zslice t = Re ξ(1/2+it)`. New verified lemmas:
  `xiCompleted_critical_eq_ofReal_Xi`, `Xi_even`, and crucially
  `Xi_eq_zero_iff_riemannZeta : Ξ t = 0 ↔ ζ(1/2+it) = 0` — the zero-correspondence
  `Λ₀` lacked. All downstream Toeplitz/moment files recompile unchanged (they use
  `XiCoeff` abstractly). With `Ξ = ξ`, the Pólya/CNV citations are now correctly
  attributable. Axiom-clean, `safe-verify` passes (44 files).
- **Finding (CNV attribution) — FIXED.** Docstrings now state CNV/Pólya are
  **external classical inputs, not formalized here**; the "subsumes the CNV rung"
  / "already a theorem" language is downgraded accordingly.
- **Findings 2–5 stand.** The equivalence chain is still RH-equivalent (no progress),
  the classical-formalization and Hilbert–Pólya assessments are unchanged.

## One-line summary

Sound Lean engineering and honest bookkeeping; **zero genuinely new mathematics
toward RH**, plus a real mathematical mis-targeting (Λ₀ vs ξ) that invalidates the
flagship Laguerre–Pólya sub-program until corrected.
