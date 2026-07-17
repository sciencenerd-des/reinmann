# RH Proof Program — Executable Plan

**Date:** 2026-07-17  
**Status:** research program, not a proof of RH

## Goal

Prove `RiemannHypothesis` in Lean by completing the signed-xi
Toeplitz/Pólya-frequency route, while keeping every classical theorem,
Xi-specific estimate, and RH-equivalent payload visibly separate.

The current checked capstone is:

```text
ClassicalToeplitzScaffolding
  + KernelContigToPFInitialColumnGeFourTheorem
  -> RiemannHypothesis
```

This is a conditional reduction. The work below is the plan for removing its
hypotheses one at a time.

## Non-negotiable proof rules

1. No `sorry`, project axiom, or theorem whose proof merely restates its target.
2. A numerical check is evidence or a falsification test, never a proof.
3. A theorem equivalent to RH must be labeled RH-strength, even when it has a
   convenient positivity or spectral formulation.
4. Continuous-kernel total positivity, moment-sequence total positivity, and
   coefficient-sequence total positivity are different statements. Every map
   between them needs its own theorem.
5. Every promoted theorem must pass `./scripts/safe-verify.sh` and the semantic
   axiom audit.

## Objects that must not be conflated

| Object | Current role | Status |
|---|---|---|
| `Φ(u)` / the de Bruijn--Newman translation kernel | Possible analytic source of inequalities | PF order five fails for the continuous kernel at a certified configuration; this does not directly decide the discrete coefficient target |
| Kernel moments `M n` | Pólya integral representation of Xi coefficients | Positivity and representation are classical but not yet formalized in Lean |
| Signed coefficients `XiMomentCoeff n` | Entries of the lower-triangular Toeplitz matrix | Full Pólya-frequency positivity is the RH-strength target |
| Jensen polynomials | Independent hyperbolicity route and cross-check | Effective fixed-degree/asymptotic results exist, but uniform all-degree hyperbolicity remains RH-strength |

The continuous-kernel warning is based on the 2026 certified PF5 counterexample
for `Φ(|u|)`: <https://arxiv.org/abs/2602.20313>. It invalidates any argument
that silently treats that continuous kernel as PF-infinity. It does **not** by
itself refute positivity of the discrete moment or coefficient Toeplitz matrix.

## Phase 0 — Proof-surface integrity

**Outcome:** completed in the current worktree.

- Keep unfinished mathematics as named `Prop` contracts or witness fields.
- Keep generated research artifacts outside the active Lean verification
  surface.
- Reject placeholders and project axioms automatically.
- Preserve a semantic `#print axioms` audit of the headline reductions.

Acceptance criteria:

- `./scripts/safe-verify.sh` passes.
- `bash scripts/verify_axiom_clean.sh` reports zero placeholders and zero custom
  axioms.

## Phase 1 — Falsification and definition audit

Before proving more infrastructure, attack the exact conjectures numerically
with certified intervals.

### 1.1 Extend the coefficient certificate

- Recompute `XiMomentCoeff n` with interval arithmetic rather than plain
  `mpmath` values.
- Store precision, truncation error, coefficient convention, and source formula
  with every artifact.
- Cross-check the first coefficients against two independent formulas: the Xi
  Taylor expansion and Pólya's kernel integral.

### 1.2 Search the actual remaining minors

Test, independently:

- contiguous minors through orders at least `k = 8`;
- all order-three initial-column row-gap patterns within a growing index box;
- order-four initial-column row-gap patterns;
- arbitrary minors only as diagnostics, not as substitutes for the named
  initial-column target.

Use interval determinants or exact rational enclosures. Record the smallest
certified margin and its row pattern.

Progress marker: `scripts/arbitrary_row_minor_scan.py` now enumerates all
strictly increasing row selections for the initial-column orders `k = 3, 4`
inside a configurable row box.  With `--max-row 30`, the stored-decimal
enclosures certify positivity for all 4,495 order-three and 31,465 order-four
selections, with no negative or inconclusive intervals.  This is a
storage-level interval result; the cache's cross-precision metadata is not a
formal proof of the Xi coefficient computation.

### 1.3 Route-kill condition

If any required discrete minor is certified negative, stop the PF program at
that theorem, preserve the counterexample, and pivot to the Jensen route. Do
not repair the conjecture by changing normalization after seeing the result
unless a new equivalence to RH is proved.

Acceptance criteria:

- Reproducible command and machine-readable output.
- Every reported sign is interval-certified.
- A regression fixture covers the tightest observed minor.

## Phase 2 — Formalize the classical scaffolding

These steps are substantial, but they are not supposed to contain the new
RH-breaking idea. Completing them prevents the final proof from hiding behind
literature labels.

### 2.1 Pólya kernel representation

Prove `XiMomentKernelRep` from the explicit Fourier kernel:

1. define the kernel and establish integrability;
2. prove strict positivity;
3. justify differentiation/integration exchange;
4. derive the exact factorial and sign normalization for `XiCoeff`.

### 2.2 Pólya--Jensen equivalence

Formalize `PolyaJensenBridge` using the exact Xi coefficient convention in the
repo. The primary modern checkpoint is the effective Xi Jensen-polynomial work:
<https://arxiv.org/abs/1910.01227>.

### 2.3 Laguerre--Pólya closure

Formalize the locally uniform limit theorem for real-rooted polynomials and
instantiate `XiLaguerrePolyaClosureBridge`. Required subtheorems include
Hurwitz zero persistence, exclusion of the identically-zero limit, and transfer
from real zeros to Jensen hyperbolicity.

### 2.4 ASW/Edrei bridge

Formalize the finite and limiting Pólya-frequency characterization used by
`XiToeplitzTPToScaledFiniteBridge`. Prove every normalization and one-sided
support condition explicitly.

### 2.5 Initial-column criterion

Formalize Cryer's lower-triangular total-nonnegativity criterion as a reusable
finite matrix theorem, then apply it to every finite Xi Toeplitz truncation.
Cryer's Theorem 4 states the needed nonsingular lower-triangular criterion:
<https://doi.org/10.1016/0024-3795(76)90076-8>.

Acceptance criteria for Phase 2:

- Each bridge is a proved theorem, not a field inserted into the capstone.
- Each theorem has an isolated source note and a small axiom-audit entry.
- The generic matrix/complex-analysis theorems are tested independently of Xi.

Progress marker: the `k = 2` and `k = 3` Dodgson base cases are now Lean-proved
as `dodgsonCondensationIdentity_fin_two` and
`dodgsonCondensationIdentity_fin_three`. The all-size identity and the
positivity induction are still open theorem targets.

## Phase 3 — Close the order-three Xi frontier

Target: `XiInitialColumnMinorThreeFromContig`.

1. Finish the existing support decomposition into zero, full-support, and
   banded mixed-support cases.
2. Reduce full-support determinants to the explicit moment inequality already
   named in `RHTheoremTargets.lean`.
3. Express the determinant as an integral or covariance-type quantity under
   Pólya's positive kernel.
4. Prove a finite prefix by interval certificates only if those certificates
   are imported and checked in Lean.
5. Prove the infinite tail analytically using explicit coefficient asymptotics
   and a positive error margin.

The current coefficient cache tests offsets `0..116`; all contiguous order-three
determinants are positive, with the smallest normalized value approximately
`4.21082170579e-6` at offset `116`. This is encouraging evidence, not proof.

Acceptance criteria:

- `XiInitialColumnMinorThreeFromContig` has a direct Lean proof.
- The proof consumes `XiMomentKernelRep` and proved inequalities only.
- No generic witness field contains the order-three conclusion itself.

Progress marker (2026-07-17, `Reinmann/FeketeRowGap.lean`): the order-three
arbitrary-row target is now **proved in Lean modulo one classical strictness
input**.  `xiInitialColumnMinorThreeFromContig_of_kernelRep_strictTuran`
derives `XiInitialColumnMinorThreeFromContig` from `XiMomentKernelRep` plus
`XiMomentStrictTuran` (the Csordas–Norfolk–Varga **strict** Turán inequality, a
proved classical theorem whose analytic Lean proof is still an external named
hypothesis).  The mechanism is Fekete's gap-shrinking induction: two
Grassmann–Plücker three-term identities (`xiInitialMinor3_gap_first/second`,
pure `ring` facts) shrink one row gap per step, dividing by a strict
arbitrary-row `2 × 2` minor supplied by strict TP₂ propagation
(`xiMomentCoeff_strict_tp2`).  This does **not** fully discharge the
acceptance criteria above (strict Turán is a hypothesis, not yet a Lean
theorem), and it is not RH.

## Phase 4 — Prove contiguous all-order kernel positivity

Target: `KernelContigTotalPositive M` for the concrete Pólya moment sequence.

Candidate mechanisms, in priority order:

1. a determinant integral with a manifestly nonnegative integrand;
2. a planar-network or nonintersecting-path representation;
3. a recurrence/Neville-elimination factorization with nonnegative pivots;
4. a generating-function characterization that applies to the **discrete
   moment sequence**, not merely to the continuous translation kernel.

Dodgson condensation is only algebraic infrastructure. It cannot prove signs
without strict pivot control, and zero middle minors must be handled separately.

Acceptance criteria:

- A theorem proves every `momentToeplitzContigMinor M k m ≥ 0`.
- Degenerate minors and zero denominators are handled explicitly.
- The proof does not assume a continuous-kernel PF-infinity statement
  contradicted by the PF5 counterexample.

Progress marker: `Reinmann/InitialColumnThree.lean` now proves the exact
six-term expansion `xiInitialColumnMinorThree_det_eq` for full-support
initial-column `3 × 3` minors.  It is an algebraic normalization only; the
sign of that polynomial remains the order-three Xi frontier.  The same module
also proves `xiInitialColumnMinorThree_nonneg_of_contig` for consecutive rows,
anchoring the row-gap program to the existing contiguous ladder.

## Phase 5 — Close arbitrary-row initial columns for `k ≥ 4`

Target: `XiInitialColumnMinorGeFourFromContig`.

1. Prove the first new rung `k = 4` with arbitrary row gaps.
2. Identify the induction invariant: compound matrices, Neville elimination,
   or a subtraction-free planar-network certificate.
3. Generalize from `k` to `k + 1` without division by a minor that may vanish.
4. Keep consecutive-row minors as the base case, not as the induction claim.

Acceptance criteria:

- The theorem covers every strictly increasing row selector and every `k ≥ 4`.
- Every induction branch is total, including singular/zero-minor cases.
- Combining it with Phase 3 and Cryer's criterion constructs
  `KernelContigToPFInitialColumnGeFourTheorem` without open fields.

Progress marker 3 (2026-07-17, `Reinmann/ToeplitzFullPF.lean`): **the full
arbitrary-row/arbitrary-column Pólya-frequency condition is proved from the
strict contiguous ladder alone**, eliminating both Cryer's initial-column
criterion and Pólya's kernel representation from the sharpest reduction.
Mechanism: a dominance dichotomy — minors with some `rows a < cols a` vanish
(`xiMinor_eq_zero_of_lt`, permutation pigeonhole on the lower-triangular zero
pattern), dominated minors are strictly positive (`xiMinor_pos_of_dominant`,
Fekete induction with arbitrary fixed columns, whose contiguous-row base case
reduces to the initial-column theorem by the Toeplitz reversal symmetry
`xiMinor_contigRows`).  The end-to-end reduction is now
`riemannHypothesis_of_strictLadder : ClassicalToeplitzScaffolding →
XiContigToeplitzStrictPositive → RiemannHypothesis`.  **RH-strength labeling**:
since `xiToeplitzTotalPositive_of_strictLadder` shows the strict ladder implies
the RH-equivalent PF condition, `XiContigToeplitzStrictPositive` is at least
RH-strength and must never be assumed or axiomatized.  The named Cryer bridge
`XiInitialColumnMinorToFullPFBridge` remains open *as stated* (its hypotheses
are weaker), but the reduction no longer consumes it.  RH remains unproved:
the open surface is exactly the strict ladder plus the four classical
scaffolding bridges (ASW/Edrei, Laguerre–Pólya closure, Pólya–Jensen, and the
classical converse).

Progress marker 2 (2026-07-17, `Reinmann/GrassmannSyzygy.lean` +
`Reinmann/FeketeAllOrders.lean`): **the whole arbitrary-row initial-column
program is now closed at every order `k` under a single named strictness
hypothesis.**  The generic `(q+3)`-row Grassmann syzygy
(`maxMinor_syzygy`, proved by a duplicated-column determinant) contracts
against a spectator cofactor functional to the all-orders three-term identity
`grassmann_three_term`; sorting signs come from `Fin.sign_cycleRange`.  The
joint induction `xiInitialMinor_pos_of_strictLadder` (outer on order, inner on
dispersion) then proves: `XiContigToeplitzStrictPositive` — the strict
contiguous ladder, whose `k = 1` rung is strict coefficient positivity and
whose `k = 2` rung is the classical strict Turán inequality — implies strict
positivity of **every** arbitrary-row initial-column minor
(`XiInitialColumnMinorTotalPositive`, and with it the order-3, `k ≥ 4`, and
`k ≥ 5` named targets).  The end-to-end conditional reduction is
`riemannHypothesis_of_strictLadder_and_criterion`: RH follows from classical
scaffolding + Pólya kernel data + strict ladder + Cryer's criterion.  RH
remains unproved: the strict ladder is RH-adjacent and open, and the
scaffolding, kernel representation, and Cryer's criterion are classical but
unformalized.

Progress marker 1 (2026-07-17, `Reinmann/FeketeRowGap.lean`): the first rung
`k = 4` is proved with arbitrary row gaps
(`xiInitialColumnMinorFourFromContig_of_strictTuran`), by the same Fekete
induction one level up: three order-4 gap-shrinking identities divide by a
**strict** arbitrary-row `3 × 3` minor, which `xiInitialMinor3_pos` supplies
from the strict order-3 contiguous rung (`XiContigMinorStrictPositiveAt 3`, a
new named strictness hypothesis backed by the interval scans).  The tail is
re-split as `XiInitialColumnMinorGeFiveFromContig`, and
`kernelContigToPFInitialColumnGeFourTheorem_of_strictTuran_and_geFive`
rebuilds the capstone input with orders three and four discharged.  The
induction invariant sought in step 2 is identified: it is the three-term
Grassmann syzygy, and each order `k` consumes the strict order-`(k-1)`
arbitrary-row result as its divisor.  Remaining open: a generic all-`k`
syzygy formalization for `k ≥ 5`, strictness of the contiguous rungs, and
strict Turán itself.  RH remains unproved.

## Phase 6 — Assemble and audit the unconditional capstone

Construct:

```text
S : ClassicalToeplitzScaffolding
T : KernelContigToPFInitialColumnGeFourTheorem
```

from proved theorems, then apply
`riemannHypothesis_of_kernelContigToPFInitialColumnGeFour S T`.

Final acceptance criteria:

- `#print axioms` reports only Lean's foundational axioms.
- No argument to the capstone is an unproved theorem contract.
- An external mathematical review checks the coefficient conventions and every
  literature-to-Lean theorem statement.
- The repository says “RH proved” only after all three checks succeed:
  mathematical peer review, Lean verification, and independent build replay.

## Parallel Jensen fallback

Maintain the Jensen route as an independent branch, not as duplicate prose.
The useful known result is eventual hyperbolicity for fixed degree/effective
large offset, while RH requires all degrees and offsets. See
<https://arxiv.org/abs/1902.07321> and <https://arxiv.org/abs/1910.01227>.

The fallback work package is:

1. formalize the effective asymptotic hyperbolicity theorem;
2. certify the finite region below its threshold;
3. expose the remaining two-parameter uniformity gap mechanically;
4. search for a degree-uniform inequality rather than extrapolating from fixed
   degree asymptotics.

## Immediate next work package

1. Extend the interval-certified arbitrary-row minor scan beyond the current
   `max-row 30` box, and replace storage-level enclosures with a
   rigorously generated coefficient certificate.
2. Add the continuous-kernel PF5 counterexample as a route-separation regression
   note so it cannot be accidentally used against the wrong object.
3. Extend the Dodgson module from the proved `k = 2` and `k = 3` finite cases
   toward the generic finite identity, while keeping the positivity induction
   separate.
4. ~~Add `XiInitialColumnMinorThreeFromContig` … to `AxiomAudit.lean` only
   after they are actually proved.~~ Done for the conditional reductions: the
   Fekete row-gap theorems are audited in `AxiomAudit.lean` and depend only on
   the three foundational axioms.  The unconditional statements still await
   Lean proofs of strict Turán and the strict order-3 contiguous rung.
5. ~~Formalize the generic `(k+1)`-row Grassmann syzygy to extend the Fekete
   induction from fixed orders `3, 4` to all `k ≥ 5`.~~ Done:
   `Reinmann/GrassmannSyzygy.lean` and `Reinmann/FeketeAllOrders.lean` close
   every order at once from the strict contiguous ladder.
6. ~~Formalize Cryer's criterion / route the reduction through the kernel
   representation.~~ Superseded: `Reinmann/ToeplitzFullPF.lean` proves full PF
   positivity directly from the strict ladder, so the sharpest reduction is
   `RH ⟸ ClassicalToeplitzScaffolding + XiContigToeplitzStrictPositive`.
Progress marker 4 (2026-07-17, `Reinmann/HyperbolicLimit.lean` +
`Reinmann/TuranRouteKill.lean`): scaffolding program started and one shortcut
pruned.  (i) The bounded-degree hyperbolic-limit theorem
`polynomialHyperbolic_of_tendsto` is proved (elementary horizontal-line
estimate, no complex analysis), and the Laguerre–Pólya closure bridge is
reduced to the sharper named condition `XiJensenApproximationBridge`
(Cauchy coefficient convergence + Hermite–Poulain hyperbolicity of Jensen
polynomials + nonvanishing).  (ii) Machine-checked route-kill
`turan23_not_imp_toeplitz3`: the classical second- **and** third-order Turán
inequalities (CNV 1986, Dimitrov–Lucas 2011) do **not** imply the order-3
contiguous Toeplitz rung at the sequence level — witness
`(1/100, 1, 5/4, 1, 1/100)`; see `research/TURAN3_ROUTE_KILL_2026_07_17.md`.
Closing the `k = 3` rung therefore requires xi-specific quantitative input
(effective asymptotics + certified finite prefix), not local Turán data.

7. Final open surface, in priority order:
   (a) `XiContigToeplitzStrictPositive` — the single Xi-specific positivity
   input, now machine-checked to be at least RH-strength; its `k = 1, 2` rungs
   are classical (positivity, strict Turán), `k ≥ 3` is the open frontier
   (numerically supported; the tightest scanned normalized order-3 margin is
   ≈ 4.2e-6).  This is where the genuinely new mathematics must happen.
   (b) The four classical scaffolding bridges
   (`XiToeplitzTPToScaledFiniteBridge`, `XiLaguerrePolyaClosureBridge`,
   `PolyaJensenBridge`, `XiToeplitzTPFromRH`) — proved in the literature
   (ASW/Edrei 1952/53, Laguerre–Pólya theory, Pólya 1927), each a substantial
   analytic formalization.
   (c) Classical analytic side inputs used by secondary routes only:
   `XiMomentKernelRep`, `XiMomentStrictTuran`, `XiInitialColumnMinorToFullPFBridge`.

This package maximizes information gain: it can falsify the route quickly,
formalizes a known reusable theorem, and attacks the smallest genuinely open
Xi-specific determinant before attempting an all-order argument.
