# RH research frontier review — 11 October 2026

This is a research assessment, not a manuscript, novelty certificate, or proof of RH. The best fit for this repository is **quantitative spectral analysis of the prime-defined Weil operator, with independent certificate checking**. The current eigenvector construction is useful for locating obstructions, but its remaining paired-residual requirement is exactly RH in another form. Increasing the number of formal reductions will not by itself overcome that obstruction.

## Scope and evidence

I inspected the main checkout (`rh-structural-theory`) and the separate `codex/xi-eigenvector-reduction` worktree, both based on `f62bb7f7d32f572d5d92300693b3ca4962ce942b`. Both have substantial uncommitted work. This audit leaves existing sources and manuscripts unchanged.

The literature review covers 30 primary papers. Relevant statements and selected proof sections were read in 25; five were screened at abstract/introduction level. This is not a claim to have read all 30 cover to cover or independently verified their proofs. [The reading ledger](LITERATURE_MATRIX.md) identifies the depth and status of each source. Search covered pseudo-Hermitian/Krein constructions, Weil operators, finite-window certificates, Jensen/PF asymptotics, boundary regularity, spectral approximation, and formalization. It is a focused review, not an exhaustive survey of all RH research.

No expensive Lean rebuild or external certificate replay was launched for this audit. Earlier validation artifacts are historical evidence. At the last status inspection, the canonical `XiGreenGram` build had passed, `XiAlgebraicRows` was running, and the full Green integration was incomplete. The separate Green workbench v3 records successful checks, but does not substitute for the unfinished canonical build. The two Fock `.lean.draft` files remain unchecked. See `snapshot.json` for source hashes and the captured tracker.

## Assessment of the repository

| Track | What is valuable now | What remains mathematically missing | Priority |
|---|---|---|---|
| Prime-defined Weil operators | Explicit arithmetic forms, support-dependent shift bounds, interval experiments, honest full-residual failure certificates | Full complementary-operator bounds, useful isolated-eigenvalue estimates, and growing-support identification with Xi | Main research effort |
| Lean analytic infrastructure | Correct xi target and coefficient conventions; explicit conditional reductions and reusable algebra | Actual analytic instances of the classical bridges and operator estimates | Supporting, independently useful effort |
| Pseudo-Hermitian eigenvectors | Concrete Green/jet model, multiplicity bookkeeping, mass and conditioning obstructions | An arithmetic estimate that rules out neutral off-line states | Bounded diagnostic project |
| PF/Jensen positivity | Exact finite algebra and formal interfaces | New estimates uniform in the relevant rank/shift regime | Pursue only after a precise novelty comparison |
| Same-height uniqueness, entropy/flow, near-coincidence heuristics | Ways to formulate questions | Independently justified analytic inequalities | Do not make these the main proof route |

The repository has more value than a collection of numerical experiments: it records failed sufficient conditions and separates several logical layers. However, I do not find evidence that its current unconditional mathematical results lead the RH frontier. Its most credible opportunity is a narrow theorem about an actual infinite-dimensional arithmetic operator, supported by reproducible certificates.

### 1. The eigenvector bottleneck is exact

In `Reinmann/XiGreenModel.lean`, `paired_residual_norm` states, with the repository's conventions,

\[
 \left|d\bigl(x,(T-\lambda(s))x\bigr)\right|
 =2\left|\Re s-\tfrac12\right|\,|\eta(x,x)|,
 \qquad \lambda(s)=-i(s-\tfrac12).
\]

Thus for nonzero mass the normalized defect is independent of the packet:

\[
 \frac{|d(x,(T-\lambda(s))x)|}{|\eta(x,x)|}
 =2|\Re s-\tfrac12|.
\]

Changing jet order, mixing packets, or making an ordinary residual small cannot improve this ratio at a fixed off-line parameter. The source explicitly proves `GreenUnitMassPairedBudget ↔ RiemannHypothesis`. An equivalent reformulation can still be useful, but only if it exposes a genuinely controllable quantity; the present packet optimization does not supply such control.

This fits the established fact that nonreal eigenvalues of a pseudo-Hermitian operator have neutral eigenvectors. Positive-metric characterizations require additional hypotheses; they are not automatic consequences of an indefinite symmetry. [Mostafazadeh I](https://arxiv.org/pdf/math-ph/0107001), [II](https://arxiv.org/pdf/math-ph/0110016). There is also direct published precedent for zeta-related Hilbert–Pólya constructions in Krein spaces. Only the abstract of that paper was accessible reliably in this review, so a detailed construction-by-construction priority comparison remains necessary. [Kapustin](https://link.springer.com/article/10.1134/S0037446624010087).

An exact toy model makes the danger concrete. Put

\[
 P(s)=\big((s-\tfrac12-\tfrac14)^2+1\big)
       \big((s-\tfrac12+\tfrac14)^2+1\big).
\]

It is real, reflection symmetric, positive on the real axis, and has off-line zeros. Its folded polynomial has positive coefficients. Set

\[
 T=\operatorname{diag}(1-i/4,1+i/4),\quad B=-1/2-2i,
 \quad \eta(x,y)=Bx_1\bar y_2+\bar Bx_2\bar y_1.
\]

This form is Hermitian and makes T symmetric. For h>0, define

\[
 \psi_h=\frac{e_1+hB e_2}{\sqrt{(17/2)h}}.
\]

Then \(\eta(\psi_h,\psi_h)=1\), while
\(\|(T-(1-i/4))\psi_h\|_2^2=h/8\to0\).
Nevertheless its paired defect has absolute value 1/2 for every h. The vector norm diverges. This is a counterexample to a generic inference, **not a counterexample to RH or to the arithmetic Xi model**. The accompanying symbolic check verifies these identities exactly.

The productive eigenvector question is now: **which arithmetic property excludes this behavior for Xi?** A proposed property must fail for such toy models, handle multiple zeros, and admit estimates not already assuming RH. A globally positive metric for the current jet action could also exclude Jordan chains, inadvertently demanding simplicity of zeta zeros. Simplicity is stronger than RH and must not enter unnoticed.

### 2. Finite positivity is much further developed than old local notes suggest

The June review calls order-three Toeplitz positivity the first open frontier. That is obsolete as a statement of classical mathematics. Katkova's finite-PF results already go far beyond it; the repository's conservative PF43 handling should retain its explanation of the printed indexing issue. Classical Jensen results include effective degree-dependent thresholds and a transfer from verified zero heights. [Katkova](https://arxiv.org/pdf/math/0505174), [effective Jensen paper](https://arxiv.org/pdf/1910.01227).

Combining the latter transfer theorem with the rigorously verified height \(3\cdot10^{12}\) yields classical Jensen hyperbolicity through degree \(9\cdot10^{24}\), for all shifts. This is an inference from published theorems, not a computation performed here, and applies to the correct classical coefficient normalization. [Platt–Trudgian](https://arxiv.org/pdf/2004.09765). Low-degree scans therefore have calibration/formalization value rather than mathematical novelty.

A 2026 preprint claims positivity of consecutive minors in the joint range \(k\ge10^{18}r^3\). It needs independent checking before use, but already changes the novelty comparison for a proposed uniform wedge. [Michałowski, cubic wedge](https://arxiv.org/html/2607.16795). A separate revised preprint reports a negative order-five minor of the continuous de Bruijn–Newman kernel, while withdrawing a broader asymptotic claim. The continuous kernel and discrete xi coefficient sequence must remain distinct. [PF5 paper, v2](https://arxiv.org/html/2602.20313v2).

The formal capstone still takes PF/ASW/LP/Pólya–Jensen and convergence inputs as hypotheses. Correct coefficient normalization and the entire xi target are essential repairs, but are not themselves new classical RH criteria. Completing a faithful Lean formalization can be worthwhile without claiming a new analytic breakthrough.

### 3. The Weil track has concrete, independently testable obstacles

The original checkout reports full-window certificates through multiplicative cutoff \(C=e^{1.6094}\approx4.9998104414\). This does not cover every C<5. Its rank-eight forcing-tail bound below \(9.491\cdot10^{-12}\) on 17≤C≤19 is useful but is not a bound on the full ground-state error. Support-based high-mode estimates leave a large intermediate block. The coupled-energy Lean theorem remains conditional on bounds for the actual energies/inverse.

The assembled prime-2 and prime-3 trial notes certify full-residual lower bounds above 0.00722377650 and 0.0001103574747 respectively. Those specific trials fail their sufficient trace-transfer gate. Their tiny boundary corrections do not cure the bulk error. These are reported repository certificates inspected here, not independently replayed during this audit.

Recent external work must be compared in matching support conventions: for f supported on [-a,a], multiplicative cutoff is C=e^(2a). Zhu v2 reports a certificate at a=0.8 and retracts the larger-window v1 claim. Liu's author-hosted preprint claims a=1 and a=17/16, the latter with prime powers through 8; it retains positive tail information and estimates an inverse of the compressed shift operator. Neither external certificate was replayed here, and Liu's submission status is not journal acceptance. [Zhu v2](https://arxiv.org/html/2608.24827v2), [Liu full paper](https://www.alphaxiv.org/abs/2609.weil-positivity-riemann-zeta-bounds.pdf).

The lesson is methodological: estimate the joint operator and its coupling. A smaller support-dependent norm of a compressed shift sum cannot simply replace a pointwise frequency bound inside a proof that needs the latter. Likewise, negativity of a weakened comparison form says nothing by itself about negativity of the genuine Weil form.

## Recommended next theorem: full-operator ground-state control

The target should be an explicitly defined arithmetic operator on a specified domain, with a certified simple even ground state, a full spectral isolation bound, and an error estimate for the observable actually needed. Finite matrix spectra alone do not provide this.

There is a useful strategic refinement. Connes–van Suijlekom's Theorem 6.1 connects real zeros of the ground-state Fourier transform to a lower-bounded operator with a simple isolated even minimum. Its precise hypothesis includes essential self-adjointness on the specified trigonometric domain. It does not require the minimum to be positive or separately require a nonzero endpoint trace. Verify these hypotheses for the chosen Weil realization; a form core is not automatically an operator core. [Theorem 6.1](https://arxiv.org/html/2511.23257).

Consequently, if the objective is Fourier-transform convergence, it may be more efficient to bypass endpoint-trace normalization. This is a proposed application of a known theorem, not a claim of a new theorem or a completed bridge.

For our convention \(\widehat u(z)=\int u(x)e^{-izx}\,dx\), functions supported in [-a,a] satisfy the elementary estimate

\[
 \sup_{z\in K}|\widehat u(z)-\widehat v(z)|
 \le\sqrt{2a}\,e^{aY}\|u-v\|_2,
 \qquad Y=\sup_{z\in K}|\Im z|.
\]

Proof: bound the exponential by e^(aY), then apply Cauchy–Schwarz. A weighted L1 bound is often sharper. At fixed support, L2 control therefore suffices for this observable, even though it cannot control endpoint traces. At growing support, plain o(1) in L2 is insufficient without tracking the expanding constant.

Let ψ_a be the genuine normalized ground state and k_a an explicitly constructed arithmetic/prolate candidate, expressed in the same additive coordinate. A sufficient target is

\[
 \sqrt{2a}e^{aY}\|c_a\psi_a-k_a\|_2\longrightarrow0
 \quad\text{for every }0<Y<1/2,
\]

with independently controlled nonzero scalars c_a and the appropriate Fourier convention. A direct compact-uniform Fourier estimate or weighted L1 convergence would suffice instead; the displayed L2 rate need not be optimal or necessary.

Connes–Consani–Moscovici provide an arithmetic/prolate candidate and a limiting Xi identification, while leaving comparison with the actual minimizing state open. Their framework is direct prior art, not an already completed proof. [Zeta Spectral Triples, §7](https://arxiv.org/html/2511.22755v1). If the actual ground-state transforms have only real zeros and converge locally uniformly to nonzero Xi in the critical strip in the z-coordinate, Hurwitz excludes nonreal zeros there. Both the ground-state hypotheses and this convergence remain substantial open work here.

For a self-adjoint A, a legal trial k, and a certified isolated eigenline with orthogonal projection P, the spectral theorem gives

\[
 \|(I-P)k\|\le\frac{\|(A-\mu)k\|}
 {\operatorname{dist}(\mu,\sigma(A|_{\operatorname{ran}(I-P)}))}.
\]

This only helps when the denominator bounds the **whole complement**, k belongs to the operator domain, and the numerator is the full residual. A structured Feshbach–Schur reduction is a plausible vehicle; it requires genuine complement-inverse bounds. [Dusson–Sigal–Stamm](https://arxiv.org/pdf/2105.02058). The repository's failed trials should be treated as baseline failures to improve, not reused as successful approximations.

## A staged research program with decision gates

1. **Establish the baseline.** Freeze exact source versions and normalize all support conventions. Reproduce one existing local full-window certificate, then independently inspect/replay the external method being used for comparison. State domain, finite block, complement, coupling, arithmetic error, and constants separately. Correct the status ledger so written, numerically certified, and Lean-checked claims are distinguishable.
2. **Prove a useful local spectral theorem.** First reproduce the prime-2/3 full-operator baseline, then target a carefully chosen support cell, such as the existing 17≤C≤19 experiment. Preserve joint prime-shift structure and positive tails; correct the trial's bulk error. A useful outcome is an unconditional isolated even ground state and an explicit error bound at that support, even without a positive lower bound for its eigenvalue. One support value is not a uniform cell certificate.
3. **Measure scaling before expanding the project.** Track the full residual, complementary gap, normalization, and Fourier-observable error as support grows. Identify the precise arithmetic cancellation needed for a useful rate. If the estimates deteriorate so fast that no growing-support theorem is plausible, publish or retain the obstruction and redesign the method before spending on larger matrices.
4. **Formalize the theorem actually obtained.** Verify the operator realization and quantitative bridge, then check compact certificates independently. Filling analytic library gaps is a valid formal-mathematics contribution; an axiom audit of a conditional theorem does not discharge its hypotheses.
5. **Keep the eigenvector branch bounded.** Consolidate the exact defect identity, the norm-product obstruction, multiplicity handling, and the toy model. Continue toward RH only once a precise Xi-specific estimate survives these tests. Merely shrinking the ordinary residual is not an advancement criterion.

If boundary values are needed for a separate spectral-triple construction, retain that as an additional problem. Logarithmic-operator boundary regularity suggests bounded or weighted forcing and renewal/Green estimates; it does not justify trace control from L2 graph norm. The exact symbol, domain, and prime-shift perturbations must be checked before importing a theorem. [Hernández-Santamaría–López Ríos–Saldaña](https://arxiv.org/html/2401.18033v2), [Grzywny–Ryznar](https://arxiv.org/pdf/1107.0745).

## What would qualify as frontier progress?

A defensible result would be a new uniform analytic estimate, an independently checked full-operator enclosure with a demonstrated improvement in range or complexity, or a formalization of a substantial previously unformalized analytic bridge. Each needs an explicit comparison with the closest literature. A new support endpoint alone is not evidence of a path to all supports; a certificate must include its infinite-dimensional transfer.

The broader analytic-number-theory frontier also advances through unconditional zero-density and Dirichlet-polynomial estimates, exemplified by Guth–Maynard. That is a possible long-term alternative, but it uses a different technical toolkit and is not the shortest route from this repository's strengths. [Guth–Maynard](https://arxiv.org/html/2405.20552).

No credible numerical probability of proving RH follows from this review. The recommendation ranks opportunities for rigorous, externally assessable progress. The immediate research objective should be **a quantitative theorem for genuine Weil ground states with controlled Fourier error**. It is narrower than proving RH, technically meaningful on its own, and addresses a named gap in the closest spectral literature.

## Documentation repairs indicated by the audit

The old README's “novel approaches” framing and near-coincidence derivative heuristic are not supported by the present evidence. The June review's order-three novelty claim is obsolete. The July statement that there is no RH-equivalent input should be checked against its all-rank positivity/hyperbolicity assumptions. A hypothesis need not be an axiom declaration to contain the entire unresolved difficulty. These historical files were not edited during this audit; a single current theorem-status ledger should supersede them before submission.

RH remains listed as unsolved by the [Clay Mathematics Institute](https://www.claymath.org/millennium/riemann-hypothesis/). This review does not change that status.
