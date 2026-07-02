# Submission Checklist

## Recommended positioning

Submit as a formalization / proof-search reduction paper, not as a proof of the
Riemann Hypothesis.

Suggested title:

> A Lean-Verified Same-Height Fiber Framework for the Riemann Hypothesis

Suggested arXiv categories:

- Primary: `math.NT`
- Cross-list: `cs.LO`

## Novelty claim

The defensible novelty is:

- Lean-verified equivalence between RH and same-height zero-fiber uniqueness.
- Lean-verified fiber-energy and cardinality sufficient criteria.
- Lean-verified zero-free-threshold equivalence.
- Lean-verified de la Vallee Poussin `3-4-1` zeta-product bridge.
- Documented rejection of the global horizontal convexity route.
- Sharpened next gap: prove a local same-height repulsion or componentwise
  horizontal critical-point exclusion principle.

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
5. Decide whether to include the negative convexity experiment as an appendix or
   supplementary note.

