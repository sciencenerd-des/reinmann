# Submission Checklist

## Recommended positioning

Submit as a formalization / proof-search reduction paper, not as a proof of the
Riemann Hypothesis.

Current manuscript:

> Two Machine-Checked Conditional Routes to the Riemann Hypothesis: A Formalized
> Fekete Criterion, Effective Positivity Targets, and an Exact-Ready Receptor
> Architecture

Suggested arXiv categories:

- Primary: `math.NT`
- Cross-list: `cs.LO`

## Defensible contribution claim

The defensible contribution is the combination of:

- a Lean-verified generic Grassmann syzygy and Toeplitz gap-shrinking identity;
- an all-orders Fekete-style closure from strict contiguous minors to full PF;
- exact-ready effective-certificate and Jensen/HPSS receptor theorems;
- the corrected use of Riemann's entire `xi` function rather than `Lambda_0`;
- machine-checked falsification of the local Turán and continuous-kernel PF
  shortcuts;
- a synthesis of the same-height, Li, Hilbert–Pólya, 3–4–1, Jensen, PF, and
  heat-flow programs.

Do not claim that this is the first Lean RH reduction or the first
formalization of total positivity.  The claim is a specific, axiom-audited
closure and interface architecture.

## Do not claim

- Do not claim the paper proves RH.
- Do not claim same-height repulsion is established.
- Do not claim numerical convexity evidence supports the discarded global
  convexity target.
- Do not claim SafeVerify proves mathematical completeness beyond the active
  Lean theorem statements.

## Before submission

1. Run `./scripts/safe-verify.sh` and include the exact commit hash.
2. Compile the LaTeX PDF.
3. Add a repository archive or DOI if submitting to arXiv.
4. Add an appendix with Lean version, mathlib commit, and Lake manifest hash.
5. Add the exact theorem ledger mapping `proved`, `external input`, and `open
   target`.
6. Decide whether to include the negative convexity experiment as an appendix
   or supplementary note.
7. Obtain an independent analytic-number-theory review of the Fekete theorem
   and Xi coefficient normalization.
