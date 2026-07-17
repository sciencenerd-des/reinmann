# Release notes: conditional RH routes v0.1.0

This release is an immutable source-and-artifact snapshot of the Lean
formalization and the synthesized manuscript
`paper/rh_two_routes_paper.tex` / `paper/rh_two_routes_paper.pdf`.

## Scope

- The manuscript explicitly does **not** prove the Riemann Hypothesis.
- The active Lean surface is checked without `sorry`, `admit`, or project
  axioms; the theorem audit and status ledger identify the remaining external
  or open mathematics.
- The release includes the literature-backed publishability review, theorem
  ledger, submission checklist, cover letter, and numerical scan reports.

## Reproduction

```sh
lake build Reinmann
bash scripts/verify_axiom_clean.sh
bash scripts/safe-verify.sh
bash scripts/run_scan_48.sh
cd paper && tectonic -X compile rh_two_routes_paper.tex
```

The PDF is generated from the tracked TeX source. Numerical reports are
diagnostics and are not used as formal theorem inputs.

## DOI status

`CITATION.cff` and `zenodo.json` are prepared for an authenticated Zenodo
deposit. No DOI is asserted in this repository: the public repository URL,
license choice, and Zenodo deposition must be supplied by the maintainer.

## Review status

`research/INDEPENDENT_REVIEW_PACKET_2026_07_17.md` is a reviewer-ready packet
and question set. It is not an independent expert report. A human reviewer
must independently inspect the Fekete identities and Xi normalization before
the release is described as externally reviewed.
