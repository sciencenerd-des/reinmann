/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.XiToeplitzPositivity

/-!
# Capstone: the RH reduction, with every input classified — and proven *tight*

This file assembles the Laguerre–Pólya / Toeplitz route into a single verified
**conditional reduction** and, crucially, proves that the reduction is **tight**:
the lone non-classical hypothesis is *equivalent to RH*.

## Why this is the honest encoding (read before "axiomatizing")

A reduction "RH follows from `X`" is mathematical progress only if `X` is **weaker
than, or independent of, RH**.  Our inputs split into two kinds:

**(A) Classical theorems, strictly weaker than RH** — true, citable, just not yet in
Mathlib.  Safe to assume as background, but insufficient for RH on their own:
* `XiToeplitzTPToScaledFiniteBridge` — Aissen–Schoenberg–Whitney / Edrei
  characterization of Pólya-frequency sequences (a universal theorem about
  sequences).
* `XiLaguerrePolyaClosureBridge` — Laguerre–Pólya limit closure.
* `PolyaJensenBridge` — the Pólya–Jensen hyperbolicity equivalence (Pólya 1927;
  Csordas–Norfolk–Varga 1986).

**(B) Exactly one input that is RH-equivalent:**
* `XiToeplitzTotalPositive` — total positivity of the Toeplitz matrix of the signed
  Riemann-`ξ` coefficients ⟺ `ξ ∈` Laguerre–Pólya ⟺ RH.

`riemannHypothesis_of_pf_and_classical_inputs` proves `RH` from (B) + (A).
`xiToeplitzTotalPositive_iff_riemannHypothesis` proves (given the classical (A)
bridges and their classical converse) that **(B) ⟺ RH**.

**Consequence — the point of this file.** Because (B) is *provably equivalent to
RH*, declaring `axiom xiToeplitzTotalPositive : XiToeplitzTotalPositive` is
mathematically identical to `axiom rh : RiemannHypothesis`.  Deriving `RH` from it
is assuming the conclusion; it is **not** a proof of RH, and `#print axioms` would
expose the assumption.  The honest object is therefore this conditional theorem,
kept axiom-clean (`[propext, Classical.choice, Quot.sound]`), which isolates the
single genuinely-RH-hard input (the order-`≥3` Toeplitz minors,
`XiToeplitzPositivity`) from the classical scaffolding.
-/

noncomputable section

namespace Reinmann

/-- **Forward capstone.** RH follows from the RH-equivalent input
`XiToeplitzTotalPositive` (B) together with the three classical bridges (A).
Axiom-clean; this is a *conditional reduction*, not an unconditional proof. -/
theorem riemannHypothesis_of_pf_and_classical_inputs
    (hPF : XiToeplitzTotalPositive)
    (hASW : XiToeplitzTPToScaledFiniteBridge)
    (hLP : XiLaguerrePolyaClosureBridge)
    (hPJ : PolyaJensenBridge) :
    RiemannHypothesis :=
  riemannHypothesis_of_xiLaguerrePolyaScaledFinite (hASW hPF) hLP hPJ

/-- The classical converse direction (RH ⟹ Toeplitz total positivity): under RH,
Riemann's `ξ` is Laguerre–Pólya (Hadamard factorisation), so its coefficient
sequence is Pólya-frequency (Aissen–Schoenberg–Whitney / Edrei).  This is a
classical implication, *weaker* than RH; named as an external input. -/
def XiToeplitzTPFromRH : Prop := RiemannHypothesis → XiToeplitzTotalPositive

/-- **Tightness of the reduction.** Given the classical (A) bridges and their
classical converse, the lone non-classical input is *exactly* RH:

`XiToeplitzTotalPositive ↔ RiemannHypothesis`.

This is the formal statement of why (B) cannot be honestly "postulated" to solve
RH: postulating it *is* postulating RH. -/
theorem xiToeplitzTotalPositive_iff_riemannHypothesis
    (hASW : XiToeplitzTPToScaledFiniteBridge)
    (hLP : XiLaguerrePolyaClosureBridge)
    (hPJ : PolyaJensenBridge)
    (hconv : XiToeplitzTPFromRH) :
    XiToeplitzTotalPositive ↔ RiemannHypothesis :=
  ⟨fun hPF => riemannHypothesis_of_pf_and_classical_inputs hPF hASW hLP hPJ, hconv⟩

/-- Bundled statement: the full classical scaffolding (A) for the Toeplitz route.
Separating these from the RH-hard input (B) makes explicit that *all* the
formalizable-from-the-literature content lives here, and the entire remaining
difficulty is `XiToeplitzTotalPositive`. -/
structure ClassicalToeplitzScaffolding : Prop where
  asw : XiToeplitzTPToScaledFiniteBridge
  lp : XiLaguerrePolyaClosureBridge
  polyaJensen : PolyaJensenBridge
  converse : XiToeplitzTPFromRH

/-- With the classical scaffolding supplied, RH is *equivalent* to the order-`≥3`
Toeplitz positivity — the entire open problem, packaged. -/
theorem riemannHypothesis_iff_pf_of_scaffolding
    (S : ClassicalToeplitzScaffolding) :
    RiemannHypothesis ↔ XiToeplitzTotalPositive :=
  (xiToeplitzTotalPositive_iff_riemannHypothesis S.asw S.lp S.polyaJensen S.converse).symm

end Reinmann
