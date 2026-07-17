# Publishability and Literature-Synthesis Review

**Date:** 2026-07-17
**Manuscript:** `paper/rh_two_routes_paper.tex`
**Scope:** arXiv readiness and peer-review readiness for a Lean/formalized
number-theory paper.  This review does not treat compilation or numerical
agreement as evidence that RH is proved.

## Executive verdict

The manuscript is suitable for an honest arXiv preprint after the synthesis
revision in the current working tree.  It is not a credible unconditional RH
paper: the two capstones still consume named open propositions, and the
classical analytic bridges are not formalized in this repository.

The most realistic peer-review positioning is a formalization/reduction paper,
not a number-theory breakthrough paper.  The strongest candidate venues remain
`Experimental Mathematics`, `Mathematics of Computation`, and the `Journal of
Automated Reasoning`; an interactive-theorem-proving venue would require a
separate paper centered on the Lean engineering rather than the RH narrative.
Top-tier RH journals are not realistic without a genuinely unconditional
mathematical theorem.

## Literature findings that must shape the paper

### 1. The Jensen route is an exact criterion, not evidence for RH

Griffin--Ono--Rolen--Zagier prove Hermite asymptotics and large-shift
hyperbolicity results for Jensen polynomials
([arXiv:1902.07321](https://arxiv.org/abs/1902.07321)).  The Xi-specific
effective paper makes the asymptotic statement effective
([arXiv:1910.01227](https://arxiv.org/abs/1910.01227)).  O'Sullivan gives a
different Hermite-combination criterion and detailed Xi coefficient
expansions ([arXiv:2007.13582](https://arxiv.org/abs/2007.13582)).

Farmer's published analysis explicitly argues that the Hermite/Jensen
phenomenon is not, by itself, a plausible RH attack and distinguishes useful
equivalences from information-losing reformulations
([Advances in Mathematics 411 (2022), 108781](https://doi.org/10.1016/j.aim.2022.108781)).
The manuscript must therefore describe Route B as a formal receptor and
classification of the remaining input, not as evidence that Jensen asymptotics
are close to proving RH.

The new 2026 analysis by Michel Planat is directly relevant: it proves an
asymptotic hyperbolicity regime and describes a finite-strip obstruction
([Mathematics 14 (2026), 1884](https://doi.org/10.3390/math14111884)).  It
supports the paper's distinction between an eventual fixed-degree theorem and
the all-degree/all-shift statement required by Pólya--Jensen.

### 2. The continuous PF route cannot be silently upgraded

Michałowski's certified computation exhibits a negative PF\(_5\) Toeplitz
minor for the de Bruijn--Newman translation kernel while lower orders remain
positive at the tested configuration
([arXiv:2602.20313](https://arxiv.org/abs/2602.20313)).  This does not refute
positivity of the discrete Xi moment sequence, but it rules out a continuous
kernel PF\(_\infty\) shortcut.  The manuscript should make the discrete-transfer
obligation explicit and keep the PF\(_5\) result in the falsification section.

### 3. Heat flow is a third conditional route, not a completed bridge

Rodgers--Tao prove the lower bound \(\Lambda\ge0\) for the de Bruijn--Newman
constant ([Forum of Mathematics Pi 8 (2020), e6](https://doi.org/10.1017/fmp.2020.6)).
The opposite inequality is equivalent to RH, so a heat-flow route still needs a
new rigidity theorem.  The paper should retain this as a named research target,
not as an achieved analytic input.

### 4. Formalization novelty must be stated comparatively

The Lean Millennium Prize Problems repository formalizes the statements of the
Millennium problems while explicitly leaving their proofs open
([repository](https://github.com/lean-dojo/LeanMillenniumPrizeProblems)).  Other
ongoing Lean RH projects also present conditional reductions with explicit
frontiers, for example the value-distribution route documented at
[riemann-hypothesis.dev](https://riemann-hypothesis.dev/) and the geometric
reduction repository at [beanapologist/RH](https://github.com/beanapologist/RH).

Accordingly, the defensible claim is not “the first Lean formalization of an RH
route.”  It is narrower: this repository formalizes a specific Fekete/Toeplitz
all-orders closure theorem, an exact-ready kernel-certificate assembly, and a
Schur--Szegő/Jensen receptor, with an axiom audit and falsification artifacts.
That claim should be checked against the final Lean commit and theorem ledger.

## Synthesis of all prior findings

The unified paper should contain four layers:

1. **Correct analytic object.**  The program is built on Riemann's entire
   \(\xi\)-function and its real slice \(\Xi(t)\), not the meromorphic
   completed-zeta variant \(\Lambda_0\).  This correction is a prerequisite,
   not a novelty claim.
2. **Formal reductions.**  Same-height fiber/energy criteria, Li and
   Hilbert--Pólya packages, zero-free threshold bridges, the 3--4--1 barrier,
   and the Fekete/Toeplitz/Jensen routes should be presented as a map of
   conditional interfaces.  Equivalent formulations must be labeled as
   RH-equivalent rather than progress toward RH.
3. **Closed algebraic core.**  The Grassmann syzygy, three-term identity,
   gap-shrinking induction, reversal symmetry, bounded-degree hyperbolic-limit
   theorem, and exact conditional capstones are the proved Lean contribution.
4. **Open analytic frontier.**  The remaining work is an effective positive
   remainder (Route A), a same-sign Schur--Szegő/finite-window certificate
   (Route B), or a heat-flow rigidity theorem.  Numerical scans are
   falsification diagnostics and do not discharge any of these obligations.

## Publishability checklist

- [x] Explicit non-claim: the paper does not prove RH.
- [x] Named hypotheses are separate from project axioms.
- [x] Axiom audit and safe verification commands are documented.
- [x] Numerical evidence is labeled as interval/falsification evidence.
- [x] The target-function correction is documented.
- [x] Recent Jensen criticism and finite-strip obstruction are now discussed.
- [ ] Add an immutable repository archive/DOI and exact Lean/mathlib commit to
  the final submission package.
- [ ] Add a theorem ledger mapping every headline theorem to its Lean file and
  status (`proved`, `external input`, or `open target`).
- [ ] Re-run `lake build`, `verify_axiom_clean.sh`, and `safe-verify.sh` on the
  exact submission commit and record their outputs.
- [ ] Obtain an independent analytic-number-theory review of the claimed
  Fekete theorem and the Xi coefficient normalization.

## Recommended submission language

Use “machine-checked conditional reduction,” “formalized algebraic closure,”
and “exact-ready receptor.”  Avoid “proof architecture for RH,” “RH-strength
theorem” without qualification, “evidence for RH” when referring to eventual
Jensen hyperbolicity, and any phrase suggesting that the open certificates are
routine.
