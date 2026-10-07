# Forward plan: measurable steps toward RH (2026-10-07)

**Ground rules.** Every route in this repository ends in an RH-equivalent
statement (Toeplitz PF∞, all-degree Jensen, Weil positivity on every window,
`Λ ≤ 0`). No finite computation closes any of them. The honest goal is
therefore **unconditional partial theorems along a monotone parameter whose
limit is RH**, together with formal infrastructure that makes each one
trustworthy. This plan ranks the options by that criterion. It follows the
novelty audit in
[OPENAI_MATH_RELEASE_AND_NOVELTY_REVIEW_2026_10_07.md](OPENAI_MATH_RELEASE_AND_NOVELTY_REVIEW_2026_10_07.md).

## 0. Done today

- `Reinmann/QuasiRHInputs.lean` (axiom-clean; the audit now covers 240
  theorems). It defines named hypotheses `ZetaZeroFreeRightOf σ`,
  `QuasiRiemannHypothesisSevenEighths`, `ZetaNoLowStripZero γ₀` and
  `KatkovaSectorBridge m`. It proves the following:
  - `zetaZeroFreeRightOf_half_iff_riemannHypothesis`;
  - the narrowed gap `riemannHypothesis_iff_band_of_quasiRH`, namely
    `1/2 < Re s ≤ 7/8`;
  - strip confinement by reflection;
  - the folded-zero angle bound from strip width and first-zero height,
    with explicit `π` checks;
  - `xi_finitePF43_of_classical` and `xi_finitePF58_of_quasiRH`;
  - `forall_angleBound_iff_riemannHypothesis`. This makes formal the claim
    that every fixed order is cheap while all orders together are RH.

## 1. Priority A — certified Weil positivity on windows containing primes

**Target theorem.** For all test functions supported in `[C^{-1/2}, C^{1/2}]`,
the Weil quadratic form is nonnegative, for every `C ≤ C*`. Positivity for
every `C` is equivalent to RH, so `C*` is a monotone, publishable measure of
progress.

**Literature frontier — CORRECTED the same day after a dedicated prior-art
check.** The first version of this paragraph misread Zhu's normalization.
His `supp f ⊆ [-L, L]` corresponds to our `log C = 2L`.
- Yoshida (1992) and Connes–Consani (2021): positivity up to `C = 2`.
- Zhu, arXiv:2608.24827v2: certified positivity at `L = 0.8`, that is
  **`C ≈ 4.95`**, which includes 2, 3 and 4. The retracted §7 claim was at
  `L = 1.19`, `C ≈ 10.8`.
- V. Liu, *Certified Weil Positivity Beyond the Unit Window* (alphaXiv,
  September 2026, under review): claims `C = e² ≈ 7.39` with coercivity
  `2^-151`, and `C ≈ 8.37` with `2^-49162`.

A window containing 2 and 3 is therefore **not** new. See
[prime_spectral/CERTIFIED_WINDOW_POSITIVITY_2026_10_07.md](prime_spectral/CERTIFIED_WINDOW_POSITIVITY_2026_10_07.md)
for our independent certificates and the analysis of what lies beyond.

**Feasibility data.** These come from
[window_lowest_eigenvalue_probe.py](../experiments/prime_spectral/window_lowest_eigenvalue_probe.py).
They are 900-bit approximate eigenvalues of the finite Fourier compression
`A_N(C)`, a diagnostic and not a certificate; see
[the JSON](prime_spectral/window_lowest_eigenvalue_probe_2026_10_07.json).

| C | primes | λ_min, N=48 | λ_2, N=48 | saturated by N=48? |
|---|---|---|---|---|
| 1.9 | — | 3.36e-3 | 1.57e-1 | yes |
| 2.2 | 2 | 2.32e-4 | 1.84e-2 | yes |
| 2.5 | 2 | 1.04e-5 | 1.81e-3 | yes |
| 3.2 | 2, 3 | 6.27e-9 | 2.29e-6 | nearly |
| 4.5 | 2, 3 (and 2²) | 3.45e-15 | 3.04e-12 | nearly |
| 6.5 | ≤ 5 | 2.72e-25 | 6.01e-22 | nearly |
| 9.5 | ≤ 9 | 1.10e-40 | 4.85e-37 | no |
| 17.5 | ≤ 17 | 1.32e-69 (2.1e-81 at N=80) | — | no |

Two conclusions follow.

1. The infimum decays roughly like `10^{-5C}`, which is a Landau–Widom-type
   law. Zhu 2608.24827 already names such a law, so the phenomenon is prior
   art; the constants here are ours. At `C ≈ 17` the margin is below
   `10^{-80}` and still falling. The existing 17–19 cell work therefore
   **cannot** be upgraded to infinite-rank positivity by Galerkin-plus-tail
   estimates. Its value is the ground-state and profile analysis, not window
   positivity.
2. For `C ≤ 4.5` the margin saturates by `N ≈ 32–48`, and the spectral gap
   `λ_2/λ_min` is between 50 and 900. That is the regime where rigorous
   eigenvalue inclusion works.

**Proof architecture (all ingredients except one already exist here).**

1. A certified finite block. Ball-arithmetic `A_N(C)` with the closed entries
   and the rank-independent archimedean tail bound (`closed_weil.py`), made
   uniform in `C` over subcells by the existing degree-64 Taylor-in-`C`
   machinery.
2. A certified approximate ground vector `u` and Rayleigh value `ρ`, with the
   infinite residual `r = A u − ρ u`. The omitted-index part is bounded by the
   signed-moment tail theorem of `WeilRankTail` / `CoupledRankEnergy`, which is
   already Lean-checked algebra plus certificates.
3. A Temple–Kato lower bound `λ_0 ≥ ρ − ‖r‖²/(μ − ρ)`, where `μ` is a rigorous
   lower bound for the **second** eigenvalue of the infinite form.
4. **Missing ingredient:** the lower bound `μ`. Standard tools are
   Lehmann–Goerisch bounds or Plum's homotopy method. A base problem is
   available: a diagonal-dominant comparison operator built from the
   archimedean digamma diagonal, plus the proved high-mode coercivity and the
   `2π sup|b_i|` off-diagonal bound. The current coercivity start of 117,259 is
   far too conservative and must come down to `O(N)`. Sharpening that envelope
   is the first concrete subtask.
5. Lean. Port the matrix identities and Temple inequality, which are pure
   algebra. Ball-arithmetic certificates stay at the FLINT trust boundary, or
   move to `leancert`, the certified interval arithmetic library used by
   OpenAI's library.

**Milestones.** In order:
- (A1) `C ∈ [2, 2.5]`: first window with a prime;
- (A2) `C ∈ [2.5, 3.2]`: prime 3 enters;
- (A3) push toward `C ≈ 4.5–6.5` while precision and the gap allow;
- (A4) publish, with a reproducible certificate archive.

**Risk.** The `μ` lower bound is genuine eigenvalue-inclusion work. If the
gap closes faster than the margins grow, `C*` stalls. That would itself be an
informative negative result.

## 2. Priority B — Toeplitz route: shrink the complementary region

- The Michałowski preprint gives contiguous minors positive for
  `m ≥ 10^18 r^3`. Every fixed order `r` is classical. What remains open is
  unbounded `r` at moderate shifts.
- Study the Liu–Mao closure (arXiv:2610.04972), which uses saddle estimates on
  disks shrinking as `n` grows to propagate iterated log-concavity to all
  orders. Test whether the same disk-shrinking estimates lower Michałowski's
  exponent from `r^3` toward `r^2`.
- Formal: carry the wedge as a named `Prop` and compose it with the existing
  `KernelEffectiveCertificates` receptor.
- Expected value: quantitative and formal. The complementary region stays
  RH-strength, so this does not by itself approach RH.

## 3. Priority C — formalization that converts named inputs into theorems

1. `ZetaNoLowStripZero (141/10)`: a certified zero-free rectangle for
   `|Im s| < 14.1`, via the argument principle with `leancert` bounds. This is
   hard but self-contained, and it removes a classical input from both PF
   theorems.
2. `KatkovaSectorBridge`: Schoenberg's polynomial sector theorem plus
   Hadamard's canonical product for `ξ(1/2+√z)`. This is a large Mathlib-scale
   project; the OpenAI library's Borel–Carathéodory, three-circles and Gamma
   growth files are reusable (Apache-2.0).
3. Comparator challenge files plus `formalization.yaml` for the headline
   theorems, to close the publishability-checklist item on a theorem ledger.

## 4. Stop or de-prioritize

- Fixed-order Toeplitz minor scans and low-degree Jensen/Turán numerics.
  Classical theorems (Katkova, CNV, Dimitrov–Lucas, GORZ, Liu–Mao) settle
  these.
- De Bruijn–Newman upper bounds. The 7/8 strip gives only `Λ ≤ 9/32`, which
  is above the known 0.2.
- Window positivity at large `C` via Galerkin tails (§1, conclusion 1).
- New RH-equivalent reformulations. They are reorganization, not progress.

## 5. Next actions

1. Write `experiments/prime_spectral/window_temple_bound.py`. At `C = 2.2`,
   certify `ρ` and `‖r‖` in balls, and record the `μ` needed for the Temple
   bound to give `λ_0 > 0`.
2. Measure the actual coercivity onset at `C ≤ 3.2`, numerically first, then
   design the comparison operator for Lehmann–Goerisch.
3. Run a dedicated literature check on certified Weil positivity for small
   windows: Yoshida 1992, Bombieri 2000, Connes–Consani 2021, Zhu 2026,
   Suzuki 2026. Do this before any priority claim.
