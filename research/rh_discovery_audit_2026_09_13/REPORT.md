# RH discovery audit and research program

> This is the pre-repair audit. The [implementation report](../RH_IMPLEMENTATION_2026_09_13.md)
> records subsequent repairs and validation. `diagnostics.json` retains the
> pre-repair snapshot; `diagnostics_after_repairs.json` is the current replay.


Audit completed 13 September 2026. Repository HEAD: `c4729cd8c03063328c6de897f0562ddda16161fe`; analysis includes the existing working-tree changes. Existing source, manuscripts, experiments and data were preserved. This directory contains new analysis artifacts only.

## Recommendation

The best use of this repository is a falsification-led search for an **arithmetic mechanism that forces positivity at unbounded order**, supported by precise analytic estimates and Lean verification. The most suitable local laboratory is the coefficient Toeplitz route. A genuinely independent second program is a prime-defined Weil/spectral construction with quantitative convergence. Neither has a known completion; this is a ranking by tractability and information gain, not a prediction of an RH proof.

Do not measure progress by the number of conditional capstones, positive low-order minors, simulated zeros, or named connections to other fields. Measure it by a proved new estimate, an independently constructed witness, a eliminated hypothesis, or a counterexample that rules out a proposed mechanism.

The most consequential literature correction is that **low-order coefficient positivity is not an unknown mathematical frontier**. Katkova's Theorem 1 states that the folded Xi generating function belongs to PF44. This already covers order-three and order-four nonnegativity at all offsets and arbitrary rows/columns. Exact normalization and strictness still need formal transport; the paper does not instantiate this repository's strict-ladder contract. [Katkova, Theorem 1](https://arxiv.org/html/math/0505174).

## 1. What the codebase actually supplies

This is Lean 4.30.0/mathlib 4.30.0 plus Python experimental scripts and an exact Python/TypeScript/JavaScript determinant pipeline. It is not a computational search system capable of deciding RH.

Useful verified components include:

- Conjugation/reflection symmetry, finite same-height zero fibers, and the unconditional equivalence between same-height real-coordinate uniqueness and RH.
- A fiber centroid of one half and the energy criterion `RH ↔ ∀ γ, fiberEnergy γ = 0` (`SpectralEnergyCriterion.lean:95`). These concern locations of zeros, not simplicity/multiplicity.
- Grassmann identities and Fekete propagation from strict contiguous minors to arbitrary Toeplitz minors (`ToeplitzFullPF.lean:426`).
- Bounded-degree hyperbolic-limit algebra, several explicit counterexamples to proposed shortcuts, and a semantic axiom audit of headline conditional theorems.
- Exact interval determinants conditional on stored decimal coefficient enclosures.

The sharpest coefficient reduction is:

```
strict contiguous Xi coefficient ladder
    -> arbitrary-minor coefficient PF positivity
    -> RH, given the named classical bridges
```

The first implication is proved. The classical bridge statements still need proof **and a normalization audit**. The final capstone at `ToeplitzFullPF.lean:447` is conditional. The headline equivalence at `RHReductionCapstone.lean:75` takes four bridge hypotheses; it is not an unconditional formalization of the classical PF/RH equivalence.

The distinction between a kernel, its unnormalized moments, ordinary coefficients, and derivative-normalized coefficients is essential:

| Object | Formula | Appropriate question |
|---|---|---|
| Critical-line Xi coefficients | `b_n=[t^(2n)]Xi(t)` | Alternating Taylor coefficients |
| Positive ordinary folded coefficients | `mu_n=(-1)^n b_n` | Toeplitz/PF positivity |
| Folded generating function | `F(z)=sum mu_n z^n=xi(1/2+sqrt(z))` | Negative-real zeros |
| Classical folded Jensen sequence | `gamma_n=n! mu_n` | Jensen hyperbolicity |
| Kernel moments | `M_n=integral u^(2n) Phi(u) du` | Hankel moment positivity |

The square-root notation denotes the entire power series, not a choice of branch. A positive geometric rescaling of coefficients preserves Toeplitz signs; multiplication by `n!` is not such a rescaling.

## 2. Concrete issues that change the search agenda

### 2.1 Jensen normalization is not the cited classical normalization

`JensenProgram.lean:121–129` defines `b_n=Xi^(2n)(0)/(2n)!`, then uses `sum choose(d,k)b_(n+k)X^k`. For the folded entire function, the classical Jensen construction instead uses `(n+k)! b_(n+k)`; alternating signs can be removed by a global sign and `X -> -X`. Equations (1.1)–(1.2) of the primary source explicitly use an exponential-series convention. [Griffin et al.](https://arxiv.org/html/1910.01227v3).

This is not a cosmetic change: the current polynomials are associated with a Borel-transformed generating function. The ordinary polynomial `F(z)=1+2z+2z^2` gives, at nominal Jensen degree three, `1+6X+6X^2` without the factorial, but `1+6X+12X^2` with it. Their discriminants are respectively `12` and `-12`. Thus the two tests can disagree about real-rootedness.

Do not claim the exact Xi-specific equivalence has been disproved: it remains an unproved proposition. The concrete finding is that the cited general classical theorem does not justify the encoded convention. Repair the convention or prove an additional substantive bridge. All downstream conclusions that consume `PolyaJensenBridge`, including the PF capstone, must retain that caveat.

### 2.2 The Schur–Szegő route currently assumes its output

`HermitePoulainComposition.lean:344–346` defines `jensenCoeffPoly` by precisely the same formula as `JensenPoly`. Composition with `(1+X)^d` is the identity. Therefore `XiJensenCoeffHyperbolic` already supplies `AllJensenHyperbolic`, without the Schur–Szegő theorem. `SemanticChecks.lean` proves this directly.

The comment in `EffectiveAssembly.lean:174` saying this payload is not RH-strength is misleading under its own assumed Pólya–Jensen equivalence. This interface is valid logic but does not reduce the discovery problem.

Likewise, `KernelEffectiveCertificates M` is equivalent to `KernelLadderStrict M`: the converse chooses cutoff zero. This is also proved in the audit file. The definitions contain no computable cutoff, analytic expansion, remainder bound or rational certificate checker. Those must be supplied before the package is effective mathematics.

### 2.3 The effective order-three estimate uses the wrong ratio direction

`Order3Certificate.lean:244` and `:284–292` require nondecreasing adjacent coefficient ratios. The intended strictly log-concave coefficient sequence has decreasing ratios. All 119 adjacent ratio comparisons in the stored cache decrease; the first four ratios are about `0.023105`, `0.0107481`, `0.00674234`, `0.00479630`.

The algebraic implication is true, but the chosen hypotheses do not match Xi. Replace it with a decreasing-ratio or dimensionless-deficit estimate. Tail lower bounds must scale with the index instead of requiring a fixed positive lower bound on a quantity tending to zero.

### 2.4 Some global cancellation targets are impossible

`HadamardZetaTransfer.lean:118–119`, `:143–144`, and `:169–170` quantify critical-point witnesses over every real height. Their own transfer theorem forces `completedRiemannZeta₀'(1/2+iγ)=0` for every γ. The identity theorem would make this entire function constant. It is not: its values at 2 and 4 are respectively `pi/6-1/2` and `pi^2/90-1/12`.

These are false global targets, not failures of the Lean kernel. Their conditional implications can remain perfectly valid. Restricting the quantifier would create a different target and would need a fresh mathematical justification.

The same module's `canonical : Prop` field is disconnected from the approximants; choosing `True` satisfies the purported canonicality condition. A useful interface must specify the actual zero multiset, normalization and convergence.

### 2.5 The completed function needs an entire extension at the poles

`JensenProgram.lean:58` defines `xiCompleted` as the pointwise product `s(s-1)/2 * completedRiemannZeta s`. In Lean's totalized arithmetic it equals zero at both 0 and 1; the audit file proves these evaluations. Classical entire xi has value one half there.

An everywhere-entire definition is `1/2 + s(s-1)/2 * completedRiemannZeta₀ s`, agreeing with the product away from 0 and 1. This does not invalidate the existing critical-line identities, but matters for future global Hadamard/Hurwitz claims. Also, the regularized entire `completedRiemannZeta₀` itself is not xi and does not have the same zero set.

### 2.6 Older numerical narratives overstate their results

Reproduced without regenerating their reports:

| Experiment | Concrete observation | Consequence |
|---|---|---|
| `uniformity_gap_experiment.py:102` | Its discriminant routine returns 256 for `X^4+1`, which has no real roots | Positive quartic discriminant is not a hyperbolicity test |
| `de_bruijn_newman_simulation.py:104` | Claimed decreasing energy instead rises at all 20 tested steps, from 0.0001 to 0.000103783746 | Generated conclusion contradicts the simulation |
| `hef_theory_experiment.py:16–26` | Derivative of its first coefficient on `[1,2,3,4]` is +2, while the report asserts the opposite sign | Implemented sequence deformation is not its stated equation |

For ordinary even Taylor coefficients and `partial_t H=-partial_x^2 H`, the coefficient equation is `b_n'(t)=-(2n+2)(2n+1)b_(n+1)(t)`. Its iterated solution needs factorial ratios. The present HEF formula omits them. The zero-particle simulation also needs a derivation of its coordinate/sign convention and a symmetry-preserving perturbation before representing de Bruijn–Newman dynamics.

The RMT script samples independent gaps without a recorded seed; it cannot establish determinantal GUE statistics or a universal exclusion of off-line zeros. The README's inverse-distance lower bound on a zero derivative also lacks a valid mechanism: factoring `f=(s-rho1)(s-rho2)g` gives `f'(rho1)=(rho1-rho2)g(rho1)`, not an inverse separation law.

### 2.7 Numerical independence stops at shared input assumptions

The row-48 report contains 18,424 order-three and 211,876 order-four positive interval determinants. These certify the specified decimal boxes. All three implementations share the coefficient cache. `rh_report_figures.py:48–85` uses Cauchy-circle extraction and cross-precision agreement without a displayed rigorous aliasing/evaluation error bound. Agreement is not a coefficient enclosure theorem.

The new diagnostics use exact rational **midpoints**, explicitly not Xi enclosures. No row-48 rerun was needed for this analysis.

## 3. Research landscape and implications

- Low-order PF signs have an established baseline, as noted above. Their formalization is valuable infrastructure; a direct theta-based proof is interesting if it exposes an extendable mechanism.
- A July 2026 preprint claims strict contiguous positivity when shift `n >= 10^18 r^3`. Treat its analytic and computer-assisted claims as external until independently reviewed. Even if accepted, the complementary region remains infinite. [Michałowski](https://arxiv.org/abs/2607.16795).
- Effective Jensen asymptotics give large-shift hyperbolicity for each degree. They do not close the joint degree/shift problem. Farmer explains why universal Hermite behavior is a weak discriminator for RH. [Farmer](https://arxiv.org/abs/2008.07206).
- A separate preprint gives a negative order-five minor of the **continuous translation kernel**. Its v2 withdraws an additional asymptotic-threshold claim while retaining the direct counterexample. Do not use continuous PF-infinity as a shortcut or confuse this kernel with the discrete coefficients. [Michałowski, v2](https://arxiv.org/abs/2602.20313v2).
- Rodgers–Tao prove `Lambda >= 0`; RH requires `Lambda <= 0`. Forward preservation of real zeros does not justify reversing heat evolution to zero. [Rodgers–Tao](https://arxiv.org/abs/1801.05914).
- Prime-built spectral operators offer a substantive alternative to fitting the known zeros. Connes–Consani–Moscovici identify convergence of normalized regularized determinants to Xi as an open step. [Zeta Spectral Triples](https://arxiv.org/abs/2511.22755).
- Suzuki's August 2026 revision connects Weil forms, continuous screw functions and de Branges spaces, while explicitly retaining a limiting-operator conjecture. [Suzuki](https://arxiv.org/abs/2606.09096v2).
- Lamzouri's September 2026 preprint reports more than 67.25% simple critical-line zeros through a Hilbert-space inequality and unconditional pair correlation. Its proof was not independently checked here. It suggests a concrete auxiliary theorem program, not a path from a density bound to exclusion of every exception. [Lamzouri](https://arxiv.org/abs/2609.02882v2).

## 4. Highest-value local laboratory: deficit curvature

For positive coefficients define

\[
q_n=\frac{\mu_n\mu_{n+2}}{\mu_{n+1}^2},\qquad \delta_n=1-q_n.
\]

The generic identity proved in `SemanticChecks.lean` is

\[
\frac{\det[\mu_{n+2+i-j}]_{i,j=0}^{2}}{\mu_{n+2}^{3}}
=\delta_{n+1}^{2}-q_{n+1}^{2}\delta_n\delta_{n+2}.
\]

When `0<q_n<1`, strict positivity is equivalent to

\[
\log\delta_n-2\log\delta_{n+1}+\log\delta_{n+2}
<-2\log q_{n+1}.
\]

This isolates how quickly the *amount* of log-concavity may vary. Log-concavity alone only says that delta is positive; the determinant needs quantitative control of its curvature.

Exact rational substitution verifies the identity on all 117 cached windows. At offsets 0 and 116, the determinant divided by the middle deficit squared is approximately 0.5626754 and 0.0254808. The curvature/budget ratio is approximately 0.113183 and 0.00254740. Small raw determinants therefore do not automatically imply that the curvature condition is close to failure. These are scale-dependent diagnostics, not analytic bounds.

Concrete analytic program:

1. Use the theta integral to define a real interpolation `M(x)` of the moments and a normalized tilted measure proportional to `u^(2x) Phi(u) du`.
2. Derivatives of `log M(x)` become cumulants of `2 log u`; subtract the explicit `log Gamma(2x+1)` normalization to obtain coefficient-ratio information.
3. Bound the finite differences entering delta and its curvature, with remainder control after cancellation. Pointwise relative coefficient error alone can be too weak for a determinant.
4. Prove an explicit strict margin for the tail; import genuinely enclosed coefficients for the remaining finite prefix.
5. Ask whether the mechanism survives at rank four and then as rank grows. A proof confined to rank three is a useful training theorem, not a new solution-level frontier.

The proposed identity is a re-expression of existing determinant algebra; no literature-priority claim is made. The potential new mathematics is a quantitative theta-specific estimate that extends beyond fixed rank.

## 5. Three mechanisms worth exploring

### A. Arithmetic construction of positive factors or path weights

Seek a planar network, bidiagonal factorization, or integral of nonnegative terms whose output is the actual coefficient Toeplitz matrix. The factors must be constructed from the theta series or prime data, and their signs proved independently. Choosing factors by ratios of the very minors whose signs are unknown is circular.

The first experiment is symbolic reconstruction at ranks 3–5 under justified theta-derived inequalities. Use exact rational reconstruction of proposed identities and then Lean. If every representation needs an unproved factor equal to the original determinant, record failure and stop that mechanism.

An all-rank construction, with convergence to the actual coefficients, could supply the missing theorem. No such construction was found in this audit.

### B. Use both rank and shift instead of one-dimensional scans

Normalize `e_n=mu_n/mu_0`, `e_0=1`, and define `h_n` by

\[
\left(\sum e_n(-z)^n\right)\left(\sum h_nz^n\right)=1.
\]

The classical dual Jacobi–Trudi identity rewrites a rank-r, shift-m determinant as a rank-m determinant of h-coefficients (with negative-index coefficients zero). The underlying pair of identities is recalled in [Albion et al., introductory formulas](https://people.smp.uq.edu.au/OleWarnaar/pubs/JacobiTrudiConjectures.pdf):

\[
\det[e_{m+i-j}]_{i,j=0}^{r-1}
=\det[h_{r+i-j}]_{i,j=0}^{m-1}.
\]

This is a proposed interface to add, not a theorem checked in the current audit. It trades high rank/small shift for small matrices of reciprocal coefficients. Study pole-dominance estimates using rigorously known low zeros and explicitly bounded remaining contributions, while retaining hypothetical off-line tail zeros.

Combine this with large-shift saddle analysis and draw the **uncovered** region. Two infinite wedges need not cover the plane. A useful new theorem controls the joint growing-rank/growing-shift region; separate fixed-parameter results do not automatically do so.

### C. Logarithmic derivatives as an independent positivity lens

Set `p_k=(-1)^(k-1) k [z^k] log(F(z)/F(0))`. Under the negative-real-zero product, `p_k` are reciprocal-zero power sums. This suggests testing the moment sequence `p_(n+1)` and its ordinary and shifted Hankel matrices.

Unlike Hankel matrices of the ordinary coefficients, these matrices are compatible with the product geometry. Seek a positive measure, constructed independently of presumed real zeros, for

\[
F'(z)/F(z)=\int\frac{1}{1+zt}\,d\nu(t),\qquad \nu\ge0.
\]

A valid representation on the appropriate cut plane would constrain all poles, hence all zeros of F. The hard part is exactly the independent positivity/representation theorem; finite Hankel tests do not provide it. Moment growth, determinacy, analytic continuation and support all need proof. This is an alternative diagnostic and construction target, not a claim of a new RH criterion or an automatic rescue of the discarded raw-Hankel route.

## 6. Make experiments reject attractive false ideas

Use the family `H_A(t)=A cos(t)+cos(2t)`. It is real, even and the cosine transform of a positive atomic measure for `A>0`. At `A=1`, the product-to-sum identity gives only real zeros. For `A>1`, the equation `2cos(t)^2+Acos(t)-1=0` has a cosine value below -1 and hence nonreal zeros.

The audit's exact `A=3` control has coefficients `(3+4^n)/(2n)!`. It passes every tested contiguous minor of ranks 1–5 at shifts 0–24, yet its rank-six, shift-two determinant is

\[
-26968264743653/74568823160832000<0.
\]

This is **not** a claim of global PF5, and this atomic kernel does not satisfy every special property of the Xi theta kernel. It demonstrates concretely why positive moments, even symmetry and a substantial low-order positive scan do not identify the missing mechanism.

Use `A` approaching 1 from above to calibrate how much order, precision and shift a diagnostic needs to detect a small nonreal perturbation. Add:

- Exact PF controls from products of positive linear factors.
- The repository's Turán counterexample.
- Correctly normalized Jensen controls with known nonreal roots.
- Symmetry-preserving off-line quartets, not a single displaced zero.
- Examples with nearly colliding roots, vanishing pivots and interval signs that must remain inconclusive.

A proposed invariant earns research attention by explaining why Xi obeys a condition that these counterexamples violate. Similarity to Hermite polynomials, good root fits or positive finite samples alone does not do that.

## 7. Independent second program: prime-defined operators

The current `RHAttackBridges.lean` Weil/de Branges witnesses largely store arbitrary propositions and implications. Replace one registry slot with an actual explicit-formula quadratic form or the construction in a primary spectral paper.

Specify the Hilbert space, domain, self-adjointness proof, normalization of determinants, arithmetic inputs and approximation parameter. The relevant target is compact-uniform convergence of nonzero normalized real-rooted determinants to the **correct entire Xi**, with adequate zero coverage. Agreement on a list of low ordinates is insufficient. A diagonal operator whose entries are known zero heights is a control, not an arithmetic explanation of RH.

Study the convergence error, its dependence on compact radius and prime cutoff, and the parts that cannot be controlled by presently known prime estimates. An explicit obstruction or a finite-window error theorem is a useful outcome. Merely assuming convergence in a witness recreates the existing bottleneck.

## 8. Executable sequence and acceptance criteria

These are work packages, not a promised proof timeline.

1. **Semantic repair.** Correct Jensen normalization, separate the entire xi extension, reclassify identity-only and impossible targets, and make numerical reports derive their conclusions from data. Acceptance: literature-to-code formulas match; the adversarial controls are classified correctly; no claim rests on an unattached proposition.
2. **Certified coefficient input.** Produce rational enclosures from theta integrals with explicit series-tail, quadrature and rounding bounds; cross-check Cauchy extraction using an independent error analysis. Acceptance: separate error budget for each coefficient and no claimed digits inferred solely from agreement.
3. **Classical baseline.** Formalize sector-to-finite-PF transport or a similarly reusable known theorem, with the exact coefficient convention. Acceptance: low-order signs are classified as established mathematics, formalization gaps, or strictness refinements.
4. **One analytic laboratory.** Prove a theta-based deficit-curvature bound or identify the precise missing cumulant estimate. Acceptance: an actual all-offset theorem with explicit constants, or a documented obstruction; never simply another named target.
5. **Unbounded-order mechanism.** Test network/factorization, rank–shift duality and cumulant-moment constructions. Acceptance: an exact reusable identity plus an independently provable sign condition whose order dependence is explicit.
6. **Independent spectral track.** Reproduce one prime-defined construction and derive a bounded convergence estimate. Acceptance: error theorem and a precise infinite-limit remainder; no fitting to the zeros used for validation.

For every conjecture store: exact statement and quantifiers; coefficient convention; known supporting theorem; RH dependence; negative controls; search budget; witness/counterexample; reproduction command; and the remaining proof obligation. Let AI propose identities and organize evidence. Use symbolic algebra to verify identities, interval arithmetic to certify finite inequalities, and Lean to verify deductions. The LLM must not classify its own conjecture as established.

Allocate most discovery effort to deriving and trying to falsify a mechanism, not formalizing additional wrappers. Keep enough formalization effort to ensure the proposed mechanism really plugs into the proof. Reassess a direction when it yields only larger positive tables, more equivalent targets, or estimates with an unbounded uncovered region.

## Validation and scope

- `lake build Reinmann` — passed, 3,522 jobs.
- `bash scripts/verify_axiom_clean.sh` — passed, 87 audited theorems; only foundational axioms reported.
- `lake env lean research/rh_discovery_audit_2026_09_13/SemanticChecks.lean` — passed, six audit theorems with only foundational axioms; these are outside the active library.
- `python3 research/rh_discovery_audit_2026_09_13/diagnostics.py` — passed, exact cached-midpoint checks and bounded numerical reproductions; output saved in `diagnostics.json`.
- Existing uncertainty regression tests — four passed during the audit.
- Not run: exhaustive per-file `safe-verify.sh`, row-48 scan, new rigorous Xi coefficient generation, full proof/certificate replay of cited preprints, or manuscript rebuild.

No RH proof, new all-order positivity theorem, or independent coefficient enclosure is claimed. The new checked mathematical artifact is the generic deficit identity; the research contribution of this audit is a corrected target map, concrete falsification controls and a more discriminating discovery program.
