# RH reduction manuscript preparation

This checklist is for `rh_reduction_paper.tex`, not the separate two-routes
manuscript covered by `SUBMISSION_CHECKLIST.md`.

Local revision: **1.0.1-draft, 10 October 2026**. The reserved manuscript DOI is
`10.5281/zenodo.20574510`. No remote deposit, upload or submission was performed
as part of this revision.

## Included in the manuscript

- Author name and existing correspondence email; no affiliation or ORCID invented.
- Abstract, keywords, scope, contribution statement and conclusion.
- Explicit entire xi definition, positive kernel and zero-extension conventions.
- Ordinary Taylor / exponential Jensen coefficient dictionary.
- Separate statements for arbitrary PF minors and contiguous determinants.
- Conditional theorem proofs and a theorem/dependency status ledger.
- Exact source commit, Lean version, Mathlib commit, manifest hash and data hash.
- Numerical trust boundary, finite domain, counts and replay commands.
- Regenerated figures with corrected moment and coefficient ratio thresholds.
- Classical sources and clearly qualified recent external preprints.
- AI-assistance disclosure and local metadata preparation.

## Review before submission

- [ ] Author approves the revised mathematics, wording, correspondence details
  and disclosure; add affiliation and ORCID only if supplied by the author.
- [ ] Independent number-theory/formalization reviewer checks the analytic
  identification behind the named bridges, normalization and theorem scope.
- [ ] Check the actual validation outcomes in
  `rh_reduction_revision_validation.json`; do not infer a full development build
  from the focused four-module build or the focused axiom audit.
- [ ] If presenting the entire archived development as verified, run the broader
  `scripts/safe-verify.sh` and `scripts/verify_axiom_clean.sh` at the source pin.
- [ ] Review or replay external preprint proofs and certificates before assigning
  them a stronger status than an external result or claim.
- [ ] Confirm the reserved DOI and related-record identifiers on the repository
  service, and upload a versioned source package with figures and supplements.
- [ ] Choose a venue and check its current formatting, disclosure and declaration
  requirements; funding, competing interests and data declarations require the
  author's actual information. None is fabricated here.

Suggested arXiv classification for author consideration: primary `math.NT`,
cross-list `cs.LO`. Keywords are supplied in the manuscript. The final page count
is recorded in the validation JSON; venue length limits are not assumed.

## Source package

Include the TeX source, PDF, three `figures/rh_reduction_*.png` images,
`generate_reduction_figures.py`, `certify_reduction_minors.py`,
`reduction_axiom_audit.lean`, the coefficient JSON or an immutable accessible
artifact, `rh_reduction_minor_certificate.json`, the revision validation record,
and the pinned formal source or a resolvable immutable Git link.

The source and data pins identify what was checked. They do not turn a
conditional reduction into an unconditional RH proof.
