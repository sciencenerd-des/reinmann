# Release notes: conditional RH routes

## v0.2.0 (2026-10-06)

- Zenodo: doi:10.5281/zenodo.23187646 (concept DOI for all versions:
  doi:10.5281/zenodo.21416394; v0.1.0 is doi:10.5281/zenodo.21416395).
- Manuscript revised: Katkova's Xi/PF criterion and the cubic tail-wedge
  preprint (arXiv:2607.16795, cited as external, not audited), Route A
  restated as a complementary finite-prefix wedge, row-48 minor scan with
  Python/JavaScript/TypeScript differential replication.
- Lean: `CurvatureControls`, `CoupledRankEnergy` and `WeilRankTail` are now
  imported by `Reinmann.lean` and audited; the axiom audit covers 122
  theorems. `WeilRankTail` previously failed to elaborate and was not built.
- Companion preprint, *Infinite Fourier Tails and High-Mode Coercivity for
  the Semilocal Weil Quadratic Form* (`paper/weil_infinite_rank_tail_paper`),
  deposited separately: doi:10.5281/zenodo.23187645.

## v0.1.0 (2026-07-17)


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

Zenodo: doi:10.5281/zenodo.21416395 (preprint and source archive, CC-BY-4.0).

## Review status

`research/INDEPENDENT_REVIEW_PACKET_2026_07_17.md` is a reviewer-ready packet
and question set. It is not an independent expert report. A human reviewer
must independently inspect the Fekete identities and Xi normalization before
the release is described as externally reviewed.
