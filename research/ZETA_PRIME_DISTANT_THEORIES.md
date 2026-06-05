# Theorizing ζ′ from Distant Theories

**Date:** 2026-06-05 · branch `rh-structural-theory` · `safe-verify` exit 0 (26 files),
all results axiom-only `[propext, Classical.choice, Quot.sound]`.

Goal: find a *genuine new, unconditional* theorem about `ζ′` bearing on the open
gap (componentwise critical-pair exclusion = "no two zeros at the same height"),
by importing machinery from fields that solve structurally-similar problems.

---

## The gap, restated via ζ′ (verified, `HorizontalDerivative.lean`)

On the height-`γ` slice `f(x) = ζ(x+iγ)`, the real-direction derivative is the
complex derivative: `f′ = ζ′(·+iγ)`, with `Re ζ′ = (Re f)′`, `Im ζ′ = (Im f)′`.
The remaining RH-strength input is:

> Between two same-height zeros, `ζ′` cannot have **both** `Re ζ′` vanish (at some
> interior `c_re`) and `Im ζ′` vanish (at some interior `c_im`).

Rolle (proved) guarantees both *do* vanish if two such zeros exist, so this input
is true iff RH. We seek instead unconditional constraints.

---

## Distant theories and what each yields

### 1. Complex analysis — Speiser's theorem ⭐ (the canonical ζ′ bridge)
**Speiser 1934:** `RH ⟺ ζ′ has no zeros in 0 < Re s < 1/2`.
- Status: **RH-equivalent** (cannot close), but it *localizes* the relevant ζ′
  zeros to the left half-strip.
- Formalized: `SpeiserLeftHalfZeroFree` (def). Classically ≡ RH; not proved.
- Yield: tells us the gap is about *left-half-strip* zeros of ζ′ specifically.

### 2. Electrostatics / Gauss–Lucas — logarithmic potential ⭐ (gave the new theorem)
`ζ′/ζ = ∑_ρ 1/(s-ρ)` is the field of unit charges at the zeros; `ζ′`-zeros are
field equilibria. A symmetry of the charge configuration ⇒ same symmetry of the
field ⇒ same symmetry of equilibria.
- **Unconditional yield (NEW, verified):** since the zero set is conjugate-symmetric,
  so is `ζ′` and its zero set —
  - `deriv_riemannZeta_conj : ζ′(s̄) = conj(ζ′(s))`,
  - `deriv_riemannZeta_zero_conj : ζ′(s)=0 ⇒ ζ′(s̄)=0`,
  - `deriv_riemannZeta_re_conj / im_conj`: `Re ζ′` even, `Im ζ′` odd in `γ`.
- These are genuine and **not** RH-equivalent.

### 3. Real-rooted polynomials / Hermite–Biehler / de Branges — interlacing
For a real-rooted / HB function, zeros of `f` and `f′` strictly interlace on the
line. The completed `ξ` and de Branges spaces encode RH as a positivity/structure
condition on an HB function.
- Status: the full interlacing statement on the critical line ⇒ RH (RH-equivalent
  flavor); de Branges' program is open.
- Yield: suggests studying `ξ′` (entire, no pole) rather than `ζ′`, where the
  Hadamard/HB structure is cleaner. **Next target:** transport conjugation symmetry
  to `completedRiemannZeta` and its derivative (Mathlib has `completedRiemannZeta`).

### 4. Sturm oscillation theory — counting interior critical points
Sturm chains count real zeros in an interval via sign sequences; Rolle iterates to
bound critical points between zeros.
- Yield: only counts; the *exclusion* needed is RH-strength. Gives no unconditional
  closing, but motivates: between consecutive zeros of `Re f` there is a zero of
  `(Re f)′ = Re ζ′` — pure real calculus, already captured by the proved Rolle.

### 5. Quantum / SUSY (Darboux) — partner operators
`ζ` and `ζ′` as related by a ladder/Darboux transform; spectra of partner
Hamiltonians interlace.
- Status: speculative; no formalizable handle without the Hilbert–Pólya operator.

---

## Net result of this round

- **New unconditional theorem about ζ′** (electrostatic route, verified):
  conjugation symmetry of `ζ′` and its zero set. This is a real (non-equivalent)
  structural constraint — exactly the kind asked for.
- **Localization (Speiser):** the gap's ζ′ content lives in the left half-strip,
  and (by the new symmetry) those zeros come in conjugate pairs.

## Honest assessment

The conjugation symmetry of `ζ′` is genuine and unconditional, but it is a
*symmetry* constraint — it pairs ζ′-zeros, it does not exclude them. The exclusion
needed for the gap remains RH-equivalent (Speiser). The most promising *next*
unconditional target is the de Branges / `ξ`-route (item 3): port the symmetry and
Hadamard structure to `completedRiemannZeta`, where interlacing theory is cleanest,
and look for an unconditional interlacing/positivity fragment there.

## Next provable targets
1. `ξ′` conjugation + functional-equation symmetry (`completedRiemannZeta` is in
   Mathlib; entire, so no pole bookkeeping).
2. Functional-equation symmetry of `ζ′` (differentiate `ζ(1-s)=χ(s)ζ(s)`), giving
   `ζ′` reflection across `Re = 1/2` — pairs left/right half-strip ζ′-zeros and
   meshes with Speiser's localization.
