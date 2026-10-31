# Literature review and next directions (24 October 2026)

Scope: a literature review and a proposal. **No new theorem, certificate,
scan or RH claim.** Both proposed routes are entered in the
[DH register](RH_DH_DISCRIMINATOR_REGISTER.md) as `uninstantiated` before any
development, as `AGENTS.md` requires. External results below are preprints
unless stated otherwise. Statements of their content come from abstracts and
targeted reading, not a full refereeing pass.

## 1. What changed in the literature since the 7 October review

| Work | Status | What it does | Relevance here |
|---|---|---|---|
| OpenAI, [The Quasi-Riemann Hypothesis](https://github.com/openai/math/tree/main/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026) (30 Sep 2026) | Preprint, 7/8 version Lean-checked, unrefereed | Zero-free Re s > 7/8 for every Dirichlet and finite-order Hecke L-function over Q(√−3). Uses a Kubota/Patterson cubic-theta family and a bootstrap on the family zero supremum. A human-edited 11/12 version is what experts are reading ([Quanta, 19 Oct](https://www.quantamagazine.org/ai-proved-the-quasi-riemann-hypothesis-what-happens-now-20261019/)). | Already a `finite_strengthening_controls` entry. It is the only recent progress that is **DH-separating by construction**: the mod-5 DH function has zeros with Re s > 1 (Titchmarsh §10.25). |
| B. Liu, [arXiv:2610.12234](https://arxiv.org/abs/2610.12234) (8/12 Oct 2026) | Preprint, Lean-formalized per abstract | Re-optimizes the same exponent system to B ≈ 0.874957, the root of an explicit cubic. Claims this is optimal for the estimates used. | **New to the repo.** It locates the binding constraint (§2). |
| S. Kintali, [A Short Proof of the Quasi-RH](https://shivakintali.github.io/papers/QRH.pdf) (7 Oct 2026) | Author-hosted note | Weaker Re s > 47/48, using only the unconditional cubic theta formulas, the quadratic Hecke large sieve and a Hecke zero-density lemma. It drops the conditional dispersion inputs. | The structure is visible in about 10 pages: probe ≪ Z^{1/4}, comparison error Z^{β*−2/3−δ₀}, Mellin continuation. A reasonable first Lean-porting target if one is ever wanted. |
| Guth–Maynard, [New large value estimates for Dirichlet polynomials](https://annals.math.princeton.edu/2026/203-2/p06), Annals 203 (2026) | Published | First improvement on Montgomery–Halász/Huxley large values near N^{3/4}. Gives N(σ,T) ≪ T^{30(1−σ)/13+o(1)}. Character extensions: [Chen, arXiv:2507.08296](https://arxiv.org/abs/2507.08296); Gupta–Li (Oxford seminar, 2025). | The OpenAI/Liu character count R* is assembled from large-value detectors and moments (§2). This is the natural point where new large-values input could act. |
| Bellotti–Trudgian–Yang, [arXiv:2603.21490](https://arxiv.org/abs/2603.21490) | Preprint | Explicit zero-free region σ ≥ 1 − 1/(4.896 log t), t ≥ 3. | Finite strengthening. Not a lever here. |
| Connes–Consani–Moscovici, [Zeta Spectral Triples](https://arxiv.org/abs/2511.22755) (Nov 2025) | Preprint / EMS chapter | Rank-one perturbation of the scaling operator on [λ⁻¹,λ], built from the Weil form with p ≤ λ². Its spectrum is the zero set of the ground-state transform ξ̂_λ: real, and numerically matching the zeta zeros. §8 lists two missing steps: simple-even ground state, and ξ_λ ≈ k_λ = E(h_λ) (prolate candidate). | Already in the [11 Oct literature matrix](frontier_audit_2026_10_11/LITERATURE_MATRIX.md). It has **no DH register entry**. See §3. |
| Connes–van Suijlekom, [arXiv:2511.23257](https://arxiv.org/abs/2511.23257) | Preprint (CMP per author page, unverified) | Any real even distribution whose form gives a lower-bounded operator with a simple isolated even minimum has a ground state whose Fourier transform has only real zeros. Finite case: Carathéodory–Fejér. | It needs no positivity and no Euler product. It therefore applies to DH. |
| Connes, [arXiv:2602.04022](https://arxiv.org/abs/2602.04022) (Feb 2026) | Survey | Survey plus a "letter to Riemann". It proposes the same finite-Euler-product convergence route. | Context only. |

Earlier entries remain valid: Liu–Mao infinite log-concavity, Holland's Jensen
asymptotics, Zhu's and V. Liu's Weil-window certificates, and Rodgers–Tao
Λ ≥ 0 ([arXiv:1801.05914](https://arxiv.org/abs/1801.05914)). See
[novelty review](OPENAI_MATH_RELEASE_AND_NOVELTY_REVIEW_2026_10_07.md).

## 2. Where the quasi-RH exponent system binds (from Liu's paper)

This is read from the HTML of arXiv:2610.12234v1. It has not been re-derived.

- Direct bound: |J_η| ≪ Z^{l_x/2 + b/12 + ε}, with l_x = (1−b−ℓ)/2.
  The principal Mellin exponent is C_b(s) = s − (4+b)/6. Equating them gives
  the comparison boundary **B(ℓ) = 11/12 − ℓ/4**. Here ℓ is the total
  exponent of the auxiliary prime lengths.
- Larger ℓ lowers B. **Formally, B = 1/2 needs ℓ = 5/3.** What stops ℓ is the
  set of nonprincipal error classes, which must all save.
- At the optimum, the binding class has character-count exponent R* = 2/3,
  where ∂_b E = R*/2 − 1/3 = 0. So b cannot relax it. The count R* comes from
  simultaneous large-value detectors, a Möbius-weighted second moment, a
  sixth-power amplification and an unweighted fourth moment (Liu, Lemmas
  9.1–9.3, Prop. 18.1). Lowering R* makes the saving −h(1−R) more negative.
- Liu does not discuss Guth–Maynard-type input. His optimality claim is
  relative to those specific moment inputs.

Read this way, **the quasi-RH constant is a function of the large-values and
moment exponents of a sextic/Hecke character family over Q(ω).** That function
has not been written down as a map. Nobody has asked what it gives at the
large-values conjecture, as far as this search found.

## 3. The CCM spectral route fails the DH gate as stated

1. For each window λ, CCM build a self-adjoint operator. Its spectrum is the
   zero set of ξ̂_λ. Connes–van Suijlekom need only a simple isolated even
   minimum of a real even form. The DH Weil form is real and even, so **DH
   ground-state transforms also have only real zeros**, whenever its ground
   state is simple and even. This holds even after the DH form turns negative
   (retained witness C = 7873/256).
2. Ξ_DH has off-line zeros, the first at 0.8085 + 85.70i. By Hurwitz,
   ξ̂^DH_λ cannot converge locally uniformly to a multiple of Ξ_DH on the strip.
3. So **every RH-relevant step of the CCM route is in the comparison
   ξ_λ ≈ c_λ k_λ.** A proof of that comparison that does not use an arithmetic
   property DH lacks would prove a false statement.
4. The repo's existing measurements make the comparison delicate even for
   zeta. The near-null cluster has about 2C directions
   ([10-12 directions note](RESEARCH_DIRECTIONS_2026_10_12.md)). The two lowest
   eigenvalues are 4·10⁻²⁵ and 6·10⁻²² at C = 6.5. Any residual/gap argument
   ‖(I−P)k‖ ≤ ‖(A−μ)k‖/gap therefore needs a residual far smaller than
   e^{−κC}.

No DH ground-state transform has been computed in this repository.
`ground_state_zero_sampling.py` is zeta-only. The DH window code certifies
negativity, not eigenvectors.

## 4. Recommended directions, in order

### Direction 1 (cheap, decisive): instantiate the CCM route for DH

This uses existing infrastructure: `dh_weil_certificate.assemble` and the
Fourier evaluator in `ground_state_zero_sampling.py`.

- **Pre-registered predictions.** Each is to be checked, not assumed.
  - (a) For C below about 85.70/(2π) ≈ 13.6, the real zeros of ξ̂^DH_C track
    the DH line zeros, as the zeta ones do.
  - (b) Beyond that, the off-line pair cannot be reproduced. Either a
    spurious real zero pair appears near t ≈ 85.7, or the tracking breaks.
  - (c) The ground state may stop being simple-even before C ≈ 30.75.
- **Measurement.** Build a DH arithmetic candidate k^DH = E_DH(h_C), with E
  using the DH Dirichlet coefficients. For both functions, track
  residual/gap = ‖(A−μ)k‖/(λ₂−λ₁) as C grows.
  **Correction (same day, after the experiment).** This denominator is the
  wrong one. The Kato–Temple bound ‖(I−P)k‖ ≤ ‖(A−μ)k‖/(λ₂−μ) requires the
  Rayleigh quotient μ to lie below λ₂. A small ratio over the global gap
  λ₂−λ₁ certifies nothing when μ > λ₂. That is exactly what happened at
  C=35 (see §6).
- **Decision.** If DH's residual/gap ratio behaves like zeta's until the
  spurious pair appears, the comparison is a reformulation unless a named
  Euler-product estimate is found. That estimate must control the
  residual/gap ratio and fail for DH. If the DH ratio departs early, the term
  responsible names the arithmetic separator. That would be the first
  measured separator for a spectral route in this repo.
- Floating diagnostics first. Certify only a decisive single window.

### Direction 2 (new mathematics, DH-separated): large values into the quasi-RH bootstrap

1. **Exponent map.** Re-implement Liu's comparison system in exact or
   algebraic arithmetic, with every moment and large-value exponent as a free
   parameter. Reproduce 7/8 and 0.874957 as regression values.
2. **Intrinsic barrier.** Evaluate B under three inputs: the current inputs,
   a hypothetical Guth–Maynard-type gain, and the large-values conjecture
   (equivalently, density-hypothesis strength for the family). If
   B_∞ > 1/2 under the strongest conjecture, then **this method cannot reach
   RH even conditionally.** That negative theorem is worth stating and would
   settle the debate Sawin and Bloom raise in Quanta. If B_∞ = 1/2, the exact
   missing estimate is the new RH-relevant target, and it is arithmetic by
   construction.
3. **The new estimate.** Determine whether Liu's detector normalization
   falls in the regime that Guth–Maynard improves, near V ≈ N^{3/4} for
   unit-size coefficients. If so, try to prove the Guth–Maynard
   large-values theorem for the sextic Hecke-character polynomials over Q(ω).
   Chen's Dirichlet-character extension is the template. Any gain in R*
   moves the constant below 0.874957, which would be a genuine,
   publishable frontier result.
4. **DH gate.** The global DH analogue of any half-plane theorem is false.
   The arithmetic actually used is the Möbius-weighted moment over Hecke
   characters. The register already holds the exact DH obstruction
   b₉₁ − b₇b₁₃ = −1−κ² < 0. The constant itself is a finite strengthening.
   Only the endpoint B = 1/2 would be RH-strength.

Relation to existing work: the parked cubic-row route
(`short_family_mean_square_row_density`) is a different parametrization. Do
not restart it until the Dunn/Platt replies arrive. Direction 2 works with
the published 7/8 system as it stands.

### Direction 3 (formalization, shared prerequisite)

Formalize the finite Carathéodory–Fejér corollary in Lean 4.30: a kernel
vector of a rank-(n−1) PSD Hermitian Toeplitz matrix gives a polynomial with
all zeros on the unit circle. It fits the existing Toeplitz/Schur library.
It is needed by the CCM route and is plausibly a Mathlib contribution. Label
it a shared prerequisite. DH satisfies it.

### Not recommended now

These are reformulations per the register. Finite strengthening of them
remains useful, but not as RH strategy:

- higher Toeplitz PF ranks;
- larger Weil windows;
- Jensen degree scans;
- the Green budget.

Do not port the 199-page 7/8 Lean proof. The external replay already
suffices.

## 5. Honest assessment

No surveyed work, including the AI-produced ones, gives a mechanism that
reaches Re s = 1/2. The two routes that look structurally different are the
metaplectic bootstrap and the CCM spectral approximation. In the bootstrap,
arithmetic enters through Hecke-family moments. In the spectral route, all
the RH content sits in one comparison estimate. Direction 1 tests whether
the second has any arithmetic content. Direction 2 measures how far the
first can go and offers the one concrete place where new analytic number
theory could move the frontier.

## 6. Subsequent finite DH experiment (24 October 2026)

The pre-experiment statements above that no DH ground transform has been
computed are superseded by [the bounded spectral diagnostic](prime_spectral/DH_SPECTRAL_DIAGNOSTIC_2026_10_24.md).
It uses an odd conductor-5 prolate candidate, rather than zeta's even
zero-integral candidate. It finds rank-dependent parity and a nearly
orthogonal candidate at C=35; residual/gap alone is insufficient.
No arithmetic separating inequality, C~13.6 transition or full-operator
convergence claim follows. The bootstrap endpoint route remains uninstantiated.
