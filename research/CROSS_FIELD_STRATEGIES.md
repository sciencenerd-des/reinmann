# Closing the Gap: Cross-Field Back-Calculation and Why It Relocates Rather Than Closes

**Date:** 2026-06-05
**Scope:** Honest analysis of distant-field strategies for the sole remaining gap,
`ZeroImUniqueness`, plus one formalized physics-inspired equivalent criterion.
**Verification:** every formalized claim referenced here passes `safe-verify.sh`
(exit 0) and depends only on `[propext, Classical.choice, Quot.sound]`.

---

## 0. The meta-theorem that constrains all "back-calculation"

We have a Lean-verified equivalence

  `riemannHypothesis_iff_zeroImUniqueness : RiemannHypothesis ↔ ZeroImUniqueness`.

**Consequence (back-calculation lemma).** Suppose you invent a predicate `X` and
prove `X → ZeroImUniqueness` (i.e. you "back-calculate" a sufficient condition).
Then `X → RH`. If additionally `RH → X` (so the criterion is *faithful*, i.e. not
vacuously strong), then `X ↔ RH`. Therefore:

> Any faithful sufficient condition for the gap is **logically equivalent to RH**.
> Back-calculation can only ever *relocate* the difficulty into proving `X`. It
> cannot reduce RH to something strictly weaker.

This is not pessimism; it is a theorem about where the difficulty can live. A
referee will apply exactly this test to any claimed "new theory": *is the new
hypothesis actually weaker than RH, or is it RH in disguise?* Every honest
reformulation below fails to be weaker — and we say so explicitly.

What this rules out: a "proof of RH" obtained by inventing notation and
back-substituting. What it does **not** rule out: genuinely new *equivalent*
formulations that expose structure, are computable, or connect RH to a domain
with independent tools. Those are the legitimate deliverables.

---

## 1. Statistical mechanics: Lee–Yang and the order parameter  ✅ formalized

**Source problem.** For ferromagnetic Ising models the partition function's zeros
(in fugacity) lie exactly on the unit circle (Lee–Yang, 1952). The phase is
governed by an *order parameter* that vanishes precisely in the symmetric phase.

**Transport to RH.** Treat each imaginary height `γ` as a "system." Its
critical-strip zeros form a finite charge cloud (proved:
`finite_strip_zeros_at_height`), symmetric about the line `Re = 1/2` (proved:
`strip_zero_height_partner`). Define the order parameter as the second moment

  `fiberEnergy γ = ∑_{Re s∈(0,1), Im s=γ, ζ s = 0} (Re s − 1/2)²  ≥ 0`.

**Formalized result.**
`riemannHypothesis_iff_forall_fiberEnergy_zero : RH ↔ ∀ γ, fiberEnergy γ = 0`
with `fiberEnergy_nonneg` and `fiberEnergy_eq_zero_iff`.

**Where it stalls (honest).** Lee–Yang works because the partition function is an
*explicit* polynomial with positive coefficients, giving a circle theorem via
real-rootedness/interlacing. The zeta side has **no** such positive-coefficient
generating identity for the fiber; proving `fiberEnergy γ = 0` is exactly RH. The
criterion is faithful and hence (by §0) equivalent to RH. Value delivered: a
finitely-supported, manifestly nonnegative, physically interpretable target.

---

## 2. Heat flow / diffusion: de Bruijn–Newman constant

**Source problem.** Diffusion smooths distributions; backward diffusion sharpens
them. Newman deformed `ξ` by the backward heat equation, producing `Ξ_t` with a
real-zeros threshold `Λ` (the de Bruijn–Newman constant). `RH ⟺ Λ ≤ 0`.

**State of the art.** Rodgers–Tao (2018) proved `Λ ≥ 0`. Hence `RH ⟺ Λ = 0`.

**Where it stalls (honest).** `Λ ≥ 0` says the zeros are "barely" real — RH is the
knife-edge `Λ = 0`. The remaining inequality `Λ ≤ 0` is open and equivalent to RH.
Formalizing even the *definition* of `Λ` requires the heat-flow theory of `ξ`,
well beyond current Mathlib. Not attempted here; flagged as the most physically
principled equivalent, but still equivalent (§0).

---

## 3. Random matrix theory: Montgomery–Odlyzko / GUE

**Source problem.** Eigenvalue spacings of large random Hermitian matrices (GUE)
follow a universal law; eigenvalues are real because the matrices are Hermitian.

**Transport to RH.** Montgomery's pair-correlation conjecture: the normalized zero
spacings match GUE. Odlyzko's computations confirm this to extraordinary
precision. *If* the zeros were the spectrum of a Hermitian operator (Hilbert–Pólya,
§4), reality of eigenvalues would give RH.

**Where it stalls (honest).** RMT predicts *statistics*, not *individual* zero
locations. Baluyot et al. (2024) get ≥ 61.7% of zeros simple *unconditionally* —
a proportion, never 100%. Statistics cannot yield the deterministic
"every zero" statement without the operator. No formalizable lever here that is
weaker than RH.

---

## 4. Quantum mechanics: Hilbert–Pólya / Berry–Keating

**Source problem.** A self-adjoint operator has real spectrum. Berry–Keating
propose a classical Hamiltonian `H = xp` whose quantization would have the zeros
as eigenvalues.

**Transport to RH.** Codebase already carries `HilbertPolyaWitness`; we proved
`hilbertPolya_implies_uniqueness : HilbertPolyaWitness → ZeroImUniqueness`. So an
operator witness closes the gap.

**Where it stalls (honest).** Constructing the operator (with correct domain,
self-adjointness, and spectrum) is the Hilbert–Pólya program — open since 1914.
`HilbertPolyaWitness` is a *hypothesis*, not a theorem; supplying it is at least as
hard as RH. This is the cleanest "operator" route and the most likely to one day
produce a genuinely external tool, but today it only relocates the gap.

---

## 5. Noncommutative geometry: Connes' trace formula

**Source problem.** Spectral triples encode geometry spectrally; a trace formula
turns a counting problem into a spectral identity.

**Transport to RH.** Connes recasts RH as positivity of a Weil-type functional on
the adèle class space; RH ⟺ a trace formula holds / a quadratic form is positive.

**Where it stalls (honest).** The required positivity is again equivalent to RH
(Weil's positivity criterion). Mathlib lacks adèles/Weil explicit formula at the
needed depth. Equivalent, not weaker.

---

## 6. Functional analysis: Nyman–Beurling

**Source problem.** Approximation/density in a Hilbert space.

**Transport to RH.** `RH ⟺` the indicator `1_{(0,1)}` lies in the `L²(0,1)`-closure
of the span of dilations `{ρ(θ/x)}`. A density statement.

**Where it stalls (honest).** The density is equivalent to RH; the approximation
constants are exactly as inaccessible as the zero locations. Equivalent, not
weaker. (Mentioned for completeness; not formalized.)

---

## 7. What is genuinely new and unconditional here

Independent of RH, and verified:

1. **Conjugate symmetry is now a theorem** (`conjugateSymmetry_proved`), via the
   identity theorem on `{1}ᶜ` using `conj∘ζ∘conj` holomorphic — closing the old
   anti-holomorphic obstacle.
2. **Unconditional reduction** `RH ↔ ZeroImUniqueness` with no side hypothesis.
3. **Each height-fiber is finite** (`finite_strip_zeros_at_height`).
4. **Fiber reflection symmetry** about `Re=1/2` (`strip_zero_height_partner`).
5. **A lone zero at a height must lie on the line**
   (`unique_zero_at_height_on_line`).
6. **Spectral-energy criterion** `RH ↔ ∀ γ, fiberEnergy γ = 0` with manifest
   nonnegativity (§1).

These sharpen the *shape* of the remaining problem: for each height, a finite,
`1/2`-symmetric charge cloud must collapse to a single point on the line.

---

## 8. The honest bottom line

The gap `ZeroImUniqueness` is **equal in strength to RH** (proved). By §0, no
back-calculated criterion can be weaker. Every distant-field strategy, when made
rigorous, terminates at a statement equivalent to RH whose hard step is precisely
the one RH asserts:

| Field | Equivalent target | Hard step (= RH) |
|-------|-------------------|------------------|
| Stat-mech (Lee–Yang) | `fiberEnergy γ = 0` | energy vanishes ✅ formalized |
| Heat flow (dBN) | `Λ = 0` | `Λ ≤ 0` (Rodgers–Tao gave `Λ ≥ 0`) |
| RMT (GUE) | full pair-correlation | statistics ⇒ every zero |
| Quantum (Hilbert–Pólya) | operator exists | construct self-adjoint `H` |
| NCG (Connes) | Weil positivity | the positivity itself |
| Func-an (Nyman–Beurling) | `L²` density | the approximation |

A theory claiming to *close* the gap would have to make one of these hard steps
disappear; by the back-calculation lemma it cannot, unless it proves RH outright.
We therefore deliver verified **equivalences and structure**, and explicitly
**do not** claim a proof. That is the form of this work that withstands
aggressive scrutiny: every stated theorem is machine-checked, and the one
unproved statement is named, isolated, and shown equal to RH.
