# Hilbert–Pólya Construction & de la Vallée Poussin — Honest Status

**Date:** 2026-06-05 · `safe-verify` exit 0 (19 files) · axioms only
`[propext, Classical.choice, Quot.sound]`.

---

## 1. Hilbert–Pólya operator — what was constructed

**Cannot be done unconditionally.** `symmetric_eigenvalue_conj_eq` proves symmetric
operators have *real* eigenvalues; an operator with the zeta zeros as spectrum
would therefore prove RH. So an unconditional construction is logically equivalent
to solving RH. Not attempted (it is the open problem).

**What was genuinely constructed and verified** (`HilbertPolyaConstruction.lean`):
the *converse engine* — symmetric operators with **arbitrary prescribed real
spectrum**.

- `diagonal_real_isHermitian`: a real diagonal matrix (entries cast to `ℂ`) is
  Hermitian.
- `diagOp d := (diagonal (d ·)).toEuclideanLin`, with
  `diagOp_isSymmetric` (via the Hermitian↔symmetric bridge) and
  `diagOp_eigen : diagOp d (single i 1) = (d i) • single i 1`.
- `prescribed_real_spectrum_realizable`: for any finite real spectrum `d`, a
  symmetric operator realizing it exists.

**Reading:** the *spectral side* of Hilbert–Pólya is not the obstruction —
self-adjoint operators with any real spectrum are routine and now constructed.
The entire difficulty is arithmetic: making the spectrum *equal the zeros*
(eigenvalues `μ(s) = -i(s-1/2)`, real iff RH). The construction here plugs directly
into `riemannHypothesis_of_symmetric_eigendata`; the only missing instance is the
infinite, zeros-matching one — which is RH.

---

## 2. de la Vallée Poussin region — verified deductive core

**Cannot be completed in-session.** The region needs two analytic facts absent from
Mathlib: the logarithmic Euler cosine series, and Borel–Carathéodory / Hadamard
growth bounds near `Re = 1`. Formalizing them is a multi-thousand-line project.

**What was genuinely verified** (`VdpConditional.lean`, plus the engine in
`ZeroFreeEngine.lean`):

- **Positivity core:** `cos_341_nonneg` — `3+4cosθ+cos2θ = 2(1+cosθ)² ≥ 0`.
- **Order core:** `vdp_net_exponent_pos` — pole order `3` vs zero order `4m` gives
  net exponent `4m - 3 ≥ 1 > 0` for `m ≥ 1`, forcing the product to vanish at `1⁺`.
- **Contradiction core:** `product_bound_contradiction` — a real function that is
  `≥ 1` on `(1,∞)` cannot tend to `0` at `1⁺`. Fully proved (filter argument on
  `𝓝[>] 1`).

These compose to the classical "no zero on `Re = 1`" argument: the two analytic
inputs are exposed as the hypotheses `Tendsto P (𝓝[>]1) (𝓝 0)` (order/growth) and
`P σ ≥ 1` (positivity/Euler). The deduction between them is machine-checked; the
inputs are named, not faked.

---

## Bottom line

Both tasks terminate where the mathematics genuinely sits:

| Task | Verified | Open input (named) |
|------|----------|--------------------|
| Hilbert–Pólya | real spectra realizable by symmetric ops | spectrum = zeros (= RH) |
| de la Vallée Poussin | positivity + order + contradiction cores | log-Euler series + growth bounds |

No `sorry`, no `axiom`. Nothing claims to prove RH. Each "magic step" is now either
a verified lemma or an explicitly named, standard-but-unformalized analytic input.
