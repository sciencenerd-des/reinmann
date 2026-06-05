# RH Proof Search: Data Inventory and Experimental Program

**Date:** 2026-06-05 · branch `rh-structural-theory` · 20 Lean files, `safe-verify`
exit 0, all key results depend only on `[propext, Classical.choice, Quot.sound]`.

This document (1) inventories everything we have proved, and (2) formulates the
precise open experiments whose success would advance toward an RH proof, with
honest feasibility and implication labels.

---

## Part I — Data we hold (verified)

### A. The reduction (RH compressed to one statement)
- `riemannHypothesis_iff_zeroImUniqueness` — **RH ⟺ ZeroImUniqueness**, unconditional.
- `conjugateSymmetry_proved`, `stripConjugateZeroSymmetry_proved` — conjugate
  symmetry is now a THEOREM (was the old gap).
- Equivalent faces: `…iff_noSameImaginaryPartCollision`, `…iff_forall_zeroFiberRealUnique`,
  `riemannHypothesis_iff_no_criticalStripOffLineZero`, `…rightHalfStripZeroFree`.

### B. Per-height fiber structure (unconditional)
- `finite_strip_zeros_at_height` — each height carries finitely many strip zeros.
- `fiber_centroid_eq_half` — **1st moment: mean real part = 1/2** (unconditional).
- `riemannHypothesis_iff_forall_fiberEnergy_zero` — **RH ⟺ 2nd moment (energy) = 0**.
- `fiberEnergy_ge_of_offLine`, `fiberEnergy_pos_of_offLine` — **spectral gap**: an
  off-line zero forces energy `≥ 2(σ-1/2)²`.
- `offLine_zero_two_positive_energies` — a counterexample lights up heights `±γ`.

### C. Spectral (Hilbert–Pólya) machinery
- `symmetric_eigenvalue_conj_eq` — symmetric ⇒ real eigenvalues (from inner-product
  axioms).
- `riemannHypothesis_of_symmetric_eigendata` — `∃` symmetric operator with eigenvalue
  `μ(s)=-i(s-1/2)` per zero ⇒ RH.
- `prescribed_real_spectrum_realizable` / `diagOp_*` — symmetric operators with any
  prescribed real spectrum are constructible.
- `hilbertPolya_implies_uniqueness` — HP witness ⇒ ZeroImUniqueness.

### D. Zero-free (de la Vallée Poussin) machinery
- `cos_341_eq/nonneg`, `certificate_{two,three,four}(_nonneg)` — verified family of
  positivity certificates `2^{n-1}(1+cosθ)^n`.
- `general_vdp_net_exponent_pos` — gap criterion `c₀<c₁ ⇒ c₁m-c₀>0`.
- `product_bound_contradiction` — a function `≥1` on `(1,∞)` cannot `→0` at `1⁺`.
- `zeroFreeRightOf_half_iff_riemannHypothesis` — boundary at `1/2` ⟺ RH.
- Experimental data: `certificate_ratios_strictly_increasing` (`4/3<15/10<56/35`),
  `certificate_ratios_below_two`.

### E. Hard meta-fact governing all of this
- **Back-calculation lemma** (proved as a consequence of A): any *faithful*
  sufficient condition for the gap is logically equivalent to RH. So a reformulation
  never closes RH — only an *unconditional* partial result (e.g. a real zero-free
  region) or an external object (the operator) can move the needle.

---

## Part II — The three open inputs, sharply named

1. **(SPEC)** A symmetric operator whose spectrum is the zeros' imaginary parts. ≡ RH.
2. **(EULER)** The logarithmic Euler cosine series for `ζ` ⇒ the 3-4-1 modulus
   inequality. *True, unconditional, not in Mathlib.*
3. **(GROWTH)** Borel–Carathéodory / Hadamard growth bounds for `ζ` near `Re=1`.
   *True, unconditional, not in Mathlib.*

Plus the structural target:
4. **(ENERGY)** `∀ γ, fiberEnergy γ = 0`. ≡ RH.

---

## Part III — Experiments (problem statements)

Legend — Feasibility: **S** ≤ days, **M** weeks, **L** months, **Open** unsolved
mathematics. Implication: **Partial** (true, weaker than RH) or **≡RH**.

### Route 1 — Zero-free region (concrete; known ceiling)

**E1 (EULER). Modulus inequality from the Euler product.**
Target: `theorem zeta_341_modulus (σ t : ℝ) (hσ : 1 < σ) :`
`1 ≤ ‖ζ(σ)‖^3 * ‖ζ(σ+t*I)‖^4 * ‖ζ(σ+2t*I)‖`.
Method: from `riemannZeta_eulerProduct_exp_log`, take `‖·‖`, reduce to
`∑_p Re(-log(1-p^{-s}))`, expand `-log(1-z)=∑_k z^k/k`, apply `cos_341_nonneg` at
angle `k·t·log p` termwise.
Prereqs in Mathlib to verify/build: real part of `Complex.log(1-z)` power series
with summability; double-sum interchange over primes×k.
Feasibility: **M**. Implication: **Partial** (recovers `ζ≠0` on `Re=1`; gateway to E2).
Success test: also derive `riemannZeta_ne_zero` on `Re=1` via `product_bound_contradiction`.

**E2 (GROWTH). Quantitative boundary via growth bounds.**
Target: `∃ c>0, ∀ s, 1 - c/Real.log (|s.im|+2) < s.re → ζ s ≠ 0`.
Prereqs: Borel–Carathéodory theorem (M2), Hadamard three-circles (M3), `ζ` order
bound in strips (M4).
Feasibility: **L**. Implication: **Partial** (the classical dVP region).

**E3 (ceiling check). Can certificates reach `1/2`?**
Problem: prove or refute that the certificate method's reachable boundary
`b(certificate family)` has `inf > 1/2`. Our data (`c₁/c₀ → 2`) suggests a hard
ceiling strictly above `1/2`.
Feasibility: **M** (as a *negative*/limitation theorem). Implication: **Partial**
(formalizes *why* classical methods cannot reach RH — valuable barrier result).

### Route 2 — Hilbert–Pólya (spectral)

**E4a (SPEC, converse). Faithful HP equivalence.**
Target: `RiemannHypothesis → ∃ (E …) (T) (v), T.IsSymmetric ∧ …eigendata…`, hence
`RH ↔ ∃ eigendata`.
Method: under RH all `μ(s)=s.im∈ℝ`; build the diagonal operator on `lp 2` over an
enumeration of the (countable, discrete) zero set; eigenvectors = basis vectors.
Prereqs: countable enumeration of `riemannZetaZeros` (discreteness is in Mathlib);
`lp`/`EuclideanSpace`-style diagonal symmetric operator for a *countable* index.
Feasibility: **M**. Implication: **≡RH** (does not prove RH, but verifies the HP
framework is exactly equivalent — confirms it is the right target, removes vacuity
doubts).

**E4b (SPEC, forward). A concrete candidate operator.**
Problem: instantiate `riemannHypothesis_of_symmetric_eigendata` with a *named*
operator (Berry–Keating `xp` regularization; de Branges canonical system; a
transfer operator) and attempt to verify the eigen-correspondence.
Feasibility: **Open**. Implication: **≡RH** (this IS the Hilbert–Pólya conjecture).
Sub-questions worth isolating and (dis)proving:
- E4b-i: formalize the Berry–Keating Hamiltonian symbol and its formal symmetry.
- E4b-ii: formalize de Branges spaces enough to state the positivity condition.

### Route 3 — Energy / explicit-formula (our framework × analysis)

**E5 (ENERGY via a sum rule). A global identity for total fiber energy.**
Problem: find a *verifiable identity* expressing a weighted total
`∑_γ w(γ)·fiberEnergy(γ)` (or `∑_ρ (Re ρ-1/2)² φ(ρ)`) as an explicit
archimedean-minus-prime quantity, then ask whether that quantity is forced `≤ 0`.
This is the **Weil positivity** content in our coordinates.
Prereqs: Weil explicit formula (M5) — *not in Mathlib*.
Feasibility: **L–Open**. Implication: **≡RH** (Weil's criterion). High structural value.

**E6 (Weil criterion, foundational). Formalize the explicit formula + positivity.**
Target: state `RiemannHypothesis ↔ (∀ test φ, WeilQuadraticForm φ ≥ 0)` and prove the
`←` direction is the standard route.
Prereqs: Hadamard product for `ξ` (M6), explicit formula (M5).
Feasibility: **L**. Implication: **≡RH** (the principled bridge to Connes/NCG).

### Cross-cutting Mathlib prerequisites (formalization sub-experiments)
- **M1** Re/`norm` of `-Complex.log(1-z)` power series + summability  → unlocks E1.
- **M2** Borel–Carathéodory theorem → unlocks E2.
- **M3** Hadamard three-circles → E2.
- **M4** `ζ` growth (order, convexity bounds) in vertical strips → E2.
- **M5** Weil explicit formula → E5, E6.
- **M6** Hadamard factorization of `ξ` (order-1 entire) → E6.

---

## Part IV — Recommended sequencing

1. **E1** (M, Partial) — most tractable genuine analytic step; recovers `Re=1`
   nonvanishing through our pipeline and validates E (the engine) end-to-end.
2. **E4a** (M, ≡RH-equiv) — self-contained, makes Hilbert–Pólya an `iff`; no deep
   analysis, only Hilbert-space plumbing; removes all vacuity doubt about Route 2.
3. **E3** (M, Partial/barrier) — formalize the classical ceiling so the limits of
   Routes 1 are precise and machine-checked.
4. **E2 / M2–M4** (L) — the real partial-progress prize: a formal dVP region.
5. **E5/E6 + M5/M6** (L–Open) — the deepest, principled route (Weil/Connes); largest
   payoff, largest cost.

**Honest expectation:** E1, E3, E4a are achievable and genuinely valuable (an
unconditional region step, a barrier theorem, a completed equivalence). E2 is a
major but finite formalization project yielding real partial progress. E4b, E5, E6
touch the open mathematical core — they sharpen and connect, but closing any of
them *is* proving RH.

---

## Part V — Immediate next action

Begin **E1**: verify Mathlib's `-Complex.log(1-z)` series + summability (sub-task
M1), then assemble `zeta_341_modulus` and feed it to `product_bound_contradiction`
to re-derive `Re=1` nonvanishing through the project's own pipeline.

### M1 assessment (done)

Mathlib **does** provide the per-term building blocks for E1:
- `Complex.hasSum_taylorSeries_neg_log {z} (hz : ‖z‖ < 1) :`
  `HasSum (fun n : ℕ ↦ z ^ n / n) (-Complex.log (1 - z))` — the `-log(1-z)` series.
- `Complex.log_re (x) : x.log.re = Real.log ‖x‖` — converts real parts of logs to
  `log‖·‖`.
- Euler product: `riemannZeta_eulerProduct_exp_log (hs : 1 < s.re) :`
  `exp (∑' p : Nat.Primes, -log (1 - p^(-s))) = ζ s`.

**Verdict:** E1's *per-prime, per-`k`* positivity is now fully supported (take `Re`
of the neg-log series, combine `3·(angle 0) + 4·(angle ktlogp) + 1·(angle 2ktlogp)`,
apply `cos_341_nonneg`). The remaining genuine work is the **double summation**:
summability over `Nat.Primes × ℕ` and the interchange that turns the Euler product's
`∑' p` into the cosine double series. That is the crux of E1 (feasibility still **M**),
and is the precise next formalization target.

### Reformulated micro-experiments toward E1
- **E1.1** `re_neg_log_one_sub` : `(-(Complex.log (1-z))).re = ∑' n, (z^n/n).re` for
  `‖z‖<1` (from `hasSum_taylorSeries_neg_log` + `Complex.re` continuity/HasSum.re). **S**
- **E1.2** per-prime 3-4-1 nonnegativity of
  `3·Re(-log(1-p⁻ˢ)) + 4·Re(-log(1-p⁻ˢ⁻ⁱᵗ)) + Re(-log(1-p⁻ˢ⁻²ⁱᵗ)) ≥ 0`. **S–M**
- **E1.3** summability over primes of the per-prime quantity (from Euler-product
  summability already used by Mathlib's nonvanishing proof). **M**
- **E1.4** assemble `zeta_341_modulus` and discharge `Re=1` nonvanishing via
  `product_bound_contradiction`. **M**
