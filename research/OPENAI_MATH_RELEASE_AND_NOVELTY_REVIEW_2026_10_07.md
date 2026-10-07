# OpenAI mathematics release and a novelty audit of this repository

**Date:** 2026-10-07
**Scope:** (1) what in OpenAI's 6 October 2026 manuscript release is usable by
this project; (2) a literature check of which repository contributions are
mathematically new and which are classical or prior art.
**Status labels:** *established* (refereed or classical), *preprint theorem*
(public claim, not independently checked here), *Lean-checked externally*
(kernel-checked in someone else's library, not imported here), *this repo*.

Nothing in this note changes the repository's position: RH is not proved,
and every external result below would enter Lean only as a named `Prop`,
never an `axiom`.

---

## Part 1 — The OpenAI release

### 1.1 What was released

[`openai/math`](https://github.com/openai/math) contains **722 manuscripts
in 372 result families**, dated 6 October 2026. The figure "782" does not
occur in the repository, the overview PDF or the press coverage reviewed
here; it is presumably a misremembering of 722. Formal coverage:

- 235 families link to a Lean scope document (`lean/docs/NNN.md`);
- about 200 comparator challenges (`lean/ComparatorChallenges/*.lean` +
  `.json`) pin each formal headline statement to plain Mathlib definitions;
- the library has about 120k Lean files on `leanprover/lean4:v4.34.1`, with
  Mathlib commit `d13f23b`, PrimeNumberTheoremAnd, PrimeCert and leancert.
  This repository is on `v4.30.0`.

OpenAI says that unformalized manuscripts may contain errors. As of 7 October
no outside expert has confirmed the major claims
([Scientific American](https://www.scientificamerican.com/article/openai-unleashes-hundreds-more-math-results-upon-a-field-already-in-shock/),
[Latent Space summary](https://www.latent.space/p/ainews-quasi-riemann-hypothesis-openai)).
An earlier audit of OpenAI's August release found no confirmed fatal error,
though review depth varied
([Sienicki & Sienicki, arXiv:2608.14673](https://arxiv.org/abs/2608.14673)).

### 1.2 Directly relevant: family 003, the quasi-Riemann hypothesis

**Claim (preprint theorem; Lean-checked externally).** Every Dirichlet
L-function, including `ζ`, has no zero in `Re s > 7/8`. The same holds for
finite-order Hecke L-functions over `Q(√−3)`. A separate manuscript gives
`Re s > 11/12` by a different proof. A third proves uniform Landau–Siegel
exclusion: `(1−β) log q ≥ c` for an unspecified constant `c`.

- Paper: *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8*
  (`preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf`,
  196 pp.).
- Formal statement, verbatim, in `lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean`:

  ```lean
  theorem OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re
      {s : ℂ} (hs : (7 / 8 : ℝ) < s.re) : riemannZeta s ≠ 0
  ```

  It is checked against the comparator challenge
  `ComparatorChallenges/QuasiRiemannHypothesis.lean`. That challenge uses
  plain Mathlib `riemannZeta`, the same object our `RiemannSpine` uses.
- Method: Kubota–Patterson cubic theta series over `Q(√−3)`, a sextic
  large sieve, reflected/Poisson comparison of completed theta sums, and a
  truncated-inverse zero detector. **No positivity certificate, Toeplitz,
  Jensen or Weil-form ingredient is used.** Its technique therefore does not
  transfer to any route in this repository. Only its *conclusion* is usable.

#### Consequences for this repository, ranked by value

**(a) Finite-PF baseline: PF43 becomes PF58.** This is cheap, concrete and
fits the existing pipeline. The conservative baseline in
[`FINITE_PF_BASELINE_2026_09_13.md`](FINITE_PF_BASELINE_2026_09_13.md) uses
Katkova's Theorem B with two inputs:

1. zeros lie in the critical strip, so `|Re ρ − 1/2| ≤ 1/2`;
2. no zero has `|Im ρ| < γ₁ = 14.1347…`.

In the folded variable `z = (s−1/2)²`, a zero `1/2 + x + iγ` is at angle
`2·atan(|x|/γ)` from the negative axis. PF_m needs that angle to be
`≤ π/(m+1)`:

| strip half-width | max angle `2·atan(w/γ₁)` | largest m |
|---|---|---|
| 1/2 (classical) | 0.0707183 | **43** (`π/44 = 0.0714`) |
| 3/8 (quasi-RH 7/8) | 0.0530484 | **58** (`π/59 = 0.05325`, `π/60 = 0.05236`) |

These values were computed with mpmath at 30 digits:
`m = floor(π / (2·atan(w/γ₁))) − 1` with `γ₁ = 14.134725141734693790…`.
The half-plane is open, so zeros may lie on
`Re s = 7/8`, but the inequality holds there with margin. The strict-PF
extraction argument in
[`STRICT_FINITE_PF_FROM_REAL_ZEROS_2026_10_06.md`](STRICT_FINITE_PF_FROM_REAL_ZEROS_2026_10_06.md)
then gives strict contiguous positivity **at every shift through rank 58**.
`FinitePFStrict.lean` is rank-generic, so no Lean changes are needed beyond
the hypothesis.

Honest scope: fixed rank is *not* RH-strength. If RH is verified to height
`T` (Platt–Trudgian, `T ≈ 3·10¹²`), the same argument already gives
`m ≈ πT` without quasi-RH. Quasi-RH only multiplies that bound by 4/3. Its
value is that **58 needs no large-scale computation**: the classical
first-zero height plus one Lean-checked theorem suffice.

**(b) A formal, numerics-free de Bruijn–Newman bound `Λ ≤ 9/32`.**
De Bruijn's 1950 strip theorem says that if all zeros of `H₀` lie in
`|Im z| ≤ Δ`, then `H_t` has only real zeros for `t ≥ Δ²/2`. In de Bruijn's
normalization the critical strip gives `Δ = 1` and `Λ ≤ 1/2`. The 7/8
half-plane gives `Δ = 3/4`, so `Λ ≤ 9/32 ≈ 0.281`. This is **weaker** than
Polymath15's `Λ ≤ 0.2`, so it is not new mathematics. It may still be the
first bound below 1/2 reachable from Lean-checked inputs plus one classical
theorem, de Bruijn's strip theorem, which is not yet formalized. Worth
logging; not worth a paper.

**(c) Narrowing the formal RH gap.** `KnownZeroFreeRegions.lean` has
`zeroFreeRegion_re_ge_one`. A named hypothesis

```lean
def ZetaZeroFreeRightOf (σ : ℝ) : Prop := ∀ s : ℂ, σ < s.re → riemannZeta s ≠ 0
```

with `σ = 7/8` combines with the existing reflection lemmas in
`RiemannSpine.lean` to confine nontrivial zeros to `1/8 ≤ Re s ≤ 7/8`. The
open right-half-strip obligation `RightHalfStripZeroFree` shrinks to
`1/2 < Re s ≤ 7/8`. Label it *external Lean-checked input (OpenAI library,
toolchain v4.34.1)*. Do not import the library: about 120k files on a newer
toolchain makes a direct dependency impractical for now.

**(d) Weil-form track: constants only.** For a test function supported
at multiplicative scale `C`, an off-line zero at `Re ρ = 1/2 + x` is
amplified by at most `C^{|x|}`. With `|x| ≤ 3/8` instead of `1/2`, at `C = 19`
the factor drops from `≈ 4.36` to `≈ 3.02`. This does not affect the
intermediate-mode inverse bound or Xi identification, which remain open.

**(e) The 3-4-1 certificate barrier is unaffected.** `CertificateBarrier.lean`
proves that classical trigonometric-certificate gap ratios stay below 2.
OpenAI reached a half-plane by a completely different, automorphic route.
The barrier remains a correct statement about its method; descriptions
should not imply that a fixed half-plane is unreachable in general.

### 1.3 Process lessons worth copying

1. **Comparator challenges.** [`leanprover/comparator`](https://github.com/leanprover/comparator)
   runs under `landrun` and checks, in a sandbox, that a compiled proof's
   statement is *syntactically identical* to a small trusted challenge file
   and uses only the standard axioms. This is strictly stronger than our
   `verify_axiom_clean.sh`, which checks axioms but not statement fidelity.
   Adding challenge files for `riemannHypothesis_of_strictLadder`,
   `xiToeplitzTotalPositive_iff_riemannHypothesis` and the Weil-tail Lean
   theorems would settle the open publishability-checklist item on a
   statement ledger.
2. **`formalization.yaml`.** The [mathlib-initiative
   schema](https://github.com/mathlib-initiative/formalization.yaml)
   catalogue maps each paper to declaration, file and comparator config. It
   is a ready-made format for the theorem ledger requested in
   [`PUBLISHABILITY_REVIEW_2026_07_17.md`](PUBLISHABILITY_REVIEW_2026_07_17.md).
3. **Reusable generic analysis.** `OAI/NumberTheory/DirichletL/LogarithmicControl.lean`
   formalizes Borel–Carathéodory on closed balls, Hadamard three-circles
   with power bounds, holomorphic logarithms and log-derivative bounds in
   zero-free disks. The `CubicMoment/Estimates/Gamma*Growth` and
   `Hecke*Growth` files formalize Gamma-quotient and strip-growth
   estimates. These are the tools our unformalized Xi canonical-product and
   Hardy inputs need. They are Apache-2.0 and could be ported at file
   granularity.

### 1.4 Not relevant

The release has no manuscripts on Pólya-frequency sequences, Toeplitz
minors of Xi, Jensen polynomials, Laguerre–Pólya, de Bruijn–Newman,
Weil/explicit-formula positivity or prolate operators. Family 095
(hyperbolicity cones without semidefinite lifts) concerns multivariate
hyperbolic polynomials and does not affect the univariate Jensen/HPSS
route. Families 011, 012, 023, 026 and 028 are prime-distribution results
with no bearing on the reduction chain.

---

## Part 2 — What in this repository is actually new

### 2.1 Search summary

Searches covered the arXiv and refereed literature through 7 October 2026,
building on [`LITERATURE_REVIEW_2026_08_11.md`](LITERATURE_REVIEW_2026_08_11.md)
and [`prime_spectral/WEIL_TAIL_PUBLICATION_REVIEW_2026_10_06.md`](prime_spectral/WEIL_TAIL_PUBLICATION_REVIEW_2026_10_06.md).
Two **new** sources materially affect novelty claims.

**A. Mao, *Eulerian triangle is totally positive of order 3*,
[arXiv:2608.29224](https://arxiv.org/abs/2608.29224) (Aug 2026).** Section
2.1 states, for arbitrary lower-triangular matrices:

- Lemma 2.1: if `i_ℓ < j_ℓ` for some `ℓ`, the minor vanishes. This is our
  *non-dominated minors vanish* half of the dominance dichotomy.
- Lemma 2.2: the block factorization when `j_{ℓ'+1} > i_{ℓ'}`.
- Lemma 2.3: the three-term determinantal identity, attributed to Pinkus,
  *Totally Positive Matrices* (CUP 2010), eq. (1.2). This is our
  `GrassmannSyzygy` three-term identity.
- Lemma 2.4: Fekete's lemma.
- **Theorem 2.5:** if every admissible minor with consecutive rows and
  columns of order `1..r` is strictly positive, then every admissible minor
  of order `≤ r` is strictly positive. This is precisely the
  `FeketeAllOrders` + `ToeplitzFullPF` closure, with Toeplitz as a special
  case. The classical lineage is Fekete (1912), Cryer (1976) on triangular
  total positivity, Gasca–Peña (1992) on Neville elimination, and Pinkus
  (2010).

**B. Liu & Mao, *Infinite log-concavity of the Taylor coefficients of the
Riemann xi-function*, [arXiv:2610.04972](https://arxiv.org/abs/2610.04972)
(4 Oct 2026).** For `λ_n = ξ^{(2n)}(1/2)/(2n)!` — **exactly our folded
coefficients** `XiMomentCoeff n` (Katkova's `b_n`) — they prove
*unconditionally* that `(ℒ^m λ)_n > 0` for all `m, n ≥ 0`. This settles
Zhu's 2023 conjecture. The proof is hybrid: interval arithmetic for
`n < 12000, m ≤ 14`, saddle-point estimates for larger `n`, and a closure
argument that propagates to every iteration order `m`. This is a
*necessary* consequence of RH (Brändén), not a sufficient one, so it is in
the same epistemic class as GORZ eventual hyperbolicity. It must be cited
by any Turán/curvature material in this repository, and its closure step
is a template for our all-rank tail problem.

### 2.2 Verdicts

| Contribution | Literature status | What is genuinely new |
|---|---|---|
| `RH ⇔ Xi Toeplitz PF∞` capstone | Classical: ASW–Edrei + Laguerre–Pólya; Katkova 2007 for Xi explicitly | Lean statement with named hypotheses and axiom audit (**formalization only**) |
| Grassmann syzygy, three-term identity | Pinkus 2010 (1.2); Sylvester/Plücker | Lean proof (**formalization only**) |
| Fekete all-orders + dominance dichotomy (`ToeplitzFullPF`) | Fekete 1912, Cryer 1976, Gasca–Peña 1992; stated verbatim as Mao 2026 Thm 2.5 / Lem 2.1 | Lean proof, and the Toeplitz reversal-symmetry base case as a proof device. **Do not claim the theorem as new mathematics.** |
| PF43 nonnegativity baseline | Katkova 2007 (who states PF44) | The PF44→PF43 correction of Katkova's printed proof (small, real, publishable as an erratum-style remark) |
| Strict contiguous positivity by real-zero extraction | No direct antecedent found; follows from standard Cauchy–Binet and ASW factorization | **Plausibly new but folklore-level.** Lean predecessor-row expansion (`FinitePFStrict`) is a clean formal artifact. Upgradable to rank 58 (Part 1.2a). |
| `TuranRouteKill` witness (1/100, 1, 5/4, 1, 1/100) | No antecedent found | New but elementary; low significance |
| Effective-certificate receptor (`KernelEffectiveCertificates`) | Michałowski arXiv:2607.16795 supplies the tail wedge `k ≥ 10¹⁸ r³` this interface was designed to accept | The **interface** is new; the mathematics it awaits is Michałowski's (tail) plus open prefixes |
| HPSS/Jensen receptor, bounded-degree hyperbolic limit | Classical (Hermite–Poulain, Schur–Szegő, Hurwitz); GORZ 2019 for Xi | Formalization only; Farmer 2022 caution applies |
| `XiTaylorIdentification`: entire folded Xi + global Taylor identity in Lean | No Lean antecedent found; Mathlib has `completedRiemannZeta`, not the folded Xi series | **Formalization novelty, moderate.** Probably the first Lean construction of the folded-Xi coefficient sequence used by Katkova, Michałowski and Liu–Mao |
| Weil infinite-rank tail (signed omitted-index moments, rank-8 support-uniform realization) | Context: Connes–Consani(–Moscovici), Connes–van Suijlekom, Zhu 2608.24827, Groskin 2607.02828, Suzuki 2606.09096 | **Most defensible new mathematics in the repo** (per the 10-06 review): the signed reduction and its certified uniform realization. The displacement formula, Hilbert commutator and translation bounds are prior or classical. |
| Support-translation chain bounds | Haagerup–de la Harpe 1992 (nilpotent numerical radius) | Concrete Lean-proved instances; incremental |
| Fiber centroid = 1/2, same-height framework | Direct consequence of `s ↦ 1−s̄` symmetry | Not new mathematics |
| 3-4-1 certificate barrier (`c₁/c₀ = 2n/(n+1) < 2`) | Classical extremal bounds for nonnegative cosine polynomials (Fejér, Egerváry–Szász) | Formalization only; now also historically superseded by a different route (Part 1.2e) |

### 2.3 Bottom line

1. The repository's **original mathematical content** is concentrated in the
   prime-spectral Weil track: the signed omitted-index tail reduction and its
   certified support-uniform realization. Two smaller observations add to
   it: strict positivity by zero extraction and the PF44→PF43 correction.
2. The Toeplitz/Fekete **algebraic core is classical**. Its value is the
   machine-checked, axiom-audited proof. Papers and READMEs must cite
   Fekete, Cryer, Gasca–Peña, Pinkus and Mao 2026, and phrase the
   contribution as *formalization* rather than *new theorem*.
3. Two **unconditional external results now bracket the Toeplitz route**:
   Michałowski's cubic tail wedge and Liu–Mao's infinite log-concavity of
   the same coefficients. Positioning must state that the open content is
   the complementary finite-shift region for ranks ≥ 59 (or ≥ 44 without
   quasi-RH) in arbitrary rank. That is still RH-strength.
4. OpenAI's quasi-RH, if it survives review, is the first fixed zero-free
   half-plane. For this project it is a constant-improving input (PF58,
   `Λ ≤ 9/32`, narrower formal gap) and a source of process tooling, not a
   new route.

### 2.4 Recommended actions

- [ ] Add `ZetaZeroFreeRightOf` and a PF58 variant of the baseline
      hypothesis as named `Prop`s, citing `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re`.
- [ ] Update `rh_two_routes_paper.tex` related work: Mao 2608.29224
      (closure theorem prior art), Liu–Mao 2610.04972, OpenAI 003.
      Downgrade any "new closure theorem" wording to "formalization of".
- [ ] Adopt comparator challenge files plus `formalization.yaml` for headline
      theorems.
- [ ] Study Liu–Mao's closure argument (§ "global closure") as a template
      for the all-rank tail; check whether its disk-shrinking saddle
      estimates also control contiguous Toeplitz minors.
- [ ] Re-read Katkova's Theorem B in Schoenberg 1955 before publishing the
      PF58 statement. Point (a) inherits that dependency.

## Sources

- OpenAI, [`openai/math`](https://github.com/openai/math): `CONTENTS.md`,
  `overview.pdf`, `lean/docs/003.md`, `lean/formalization.yaml`,
  `lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean` (fetched 2026-10-07).
- [Scientific American, 2026-10](https://www.scientificamerican.com/article/openai-unleashes-hundreds-more-math-results-upon-a-field-already-in-shock/);
  [Latent Space](https://www.latent.space/p/ainews-quasi-riemann-hypothesis-openai);
  [Interesting Engineering](https://interestingengineering.com/ai-robotics/openai-largest-math-release-lean-proofs).
- [Sienicki & Sienicki, arXiv:2608.14673](https://arxiv.org/abs/2608.14673).
- [Mao, arXiv:2608.29224](https://arxiv.org/abs/2608.29224).
- [Liu & Mao, arXiv:2610.04972](https://arxiv.org/abs/2610.04972).
- [Michałowski, arXiv:2607.16795](https://arxiv.org/abs/2607.16795).
- [Katkova, arXiv:math/0505174](https://arxiv.org/abs/math/0505174).
- A. Pinkus, *Totally Positive Matrices*, CUP 2010.
- M. Gasca, J. M. Peña, *Total positivity and Neville elimination*, LAA 165 (1992).
- C. W. Cryer, *Some properties of totally positive matrices*, LAA 15 (1976).
- N. G. de Bruijn, *The roots of trigonometric integrals*, Duke Math. J. 17 (1950).
- D. H. J. Polymath, *Effective approximation of heat flow evolution of the
  Riemann ξ function, and a new upper bound for the de Bruijn–Newman
  constant*, Res. Math. Sci. 6 (2019).
