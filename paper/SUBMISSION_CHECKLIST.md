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
- an explicit comparison with Katkova's classical Xi/PF criterion and the
  recent external cubic-tail preprint;
- the corrected use of Riemann's entire `xi` function rather than `Lambda_0`;
- machine-checked falsification of the local Turán and continuous-kernel PF
  shortcuts;
- an independently implemented Python/JavaScript/TypeScript bounded minor
  replication with exact controls and input/sign hashes;
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
2. Run `bash scripts/run_scan_48.sh` and
   `bash scripts/run_cross_language_toeplitz.sh 48
   research/cross_language_toeplitz/row48` on the final coefficient artifact;
   retain the row-30 run as a regression baseline.
3. Compile the LaTeX PDF.
4. Add a repository archive or DOI if submitting to arXiv.
5. Add an appendix with Lean version, mathlib commit, and Lake manifest hash.
6. Keep the theorem ledger split into `proved`, `external classical input`,
   `external recent preprint theorem`, and `open target`.
7. Decide whether to include the negative convexity experiment as an appendix
   or supplementary note.
8. Obtain an independent analytic-number-theory review of the Fekete theorem
   and Xi coefficient normalization.
9. Independently rerun or review the ancillary certificates for
   arXiv:2607.16795 before treating its cubic tail wedge as more than an
   external preprint result.
