# Version 3 candidate — local and unpublished

Prepared on 22 October 2026. The nine-page `main.pdf` and editable `main.tex`
extend the published version 2 with unconditional finite PF58 and PF97.
This candidate has no new DOI, upload, publication, or external submission.
The existing v1/v2 sources, PDFs and release receipts are unchanged.

## Verified for this local draft

- The current proof source is `b4ec4a3920973faae02d4d9f3a56456886df49c9`,
  on Lean/Mathlib 4.30.0. All 34 jobs of
  [run 39733278869](https://github.com/sciencenerd-des/reinmann/actions/runs/39733278869)
  passed, including no-rebuild assembly and actual public-theorem axiom audits.
- The complete source-bound CI packet is retained in documentation commit
  `ad30a35e93474981528c24d91ae93338ad34958f`. This draft re-verifies that packet;
  it does not claim a new kernel rebuild or CI coverage of manuscript prose.
- The revised theorem statements and constants are cross-checked against the
  source files bound by that packet. No new Lean proof or evaluator constant
  is introduced by the manuscript revision.
- The final source compiles with Tectonic and the desktop LaTeX compiler.
  No overfull boxes, unresolved references or citation warnings remain.
  All nine final pages were rendered and visually inspected.
- The checksum-bound local validation and visual receipt are in
  `research/prime_spectral/verification_2026_10_22_formal_pf97_draft/`.

## Conditions before any future publication

1. Obtain the author's instruction to release this candidate. The current
   instruction is to update the paper locally.
2. Retain the unreviewed status unless a substantive external human read actually
   occurs. No external human review is claimed or required by this local update.
3. Package the entire pinned proof source, all old and new numerical tile sources,
   dependency pins, upstream Apache-2.0 attribution, audit inputs and actual CI
   receipts. A version-3 release supplement has **not** been prepared or uploaded.
4. Rebuild and visually inspect any release-edited PDF. Bind the final TeX/PDF and
   supplement to fresh checksums; this local receipt does not cover later edits.
5. For a new version of the existing formalization record, download and verify
   every current draft file and the entire supplement before Publish. Afterward,
   anonymously download and verify the actual public files. Preserve older
   versions and do not modify the DH-controls record.

## Scope and submission notes

PF58 and PF97 mean nonnegativity of every ordered minor up to the stated rank
at every shift for ordinary folded-Xi coefficients. They are finite
formalizations of classical consequences, not RH or an unbounded-rank result.
The full critical strip is certified only through 14.1; the higher right-hand
boxes allow critical-line zeros. The DH atlas remains external to Lean.
The separate Lean 4.34.1 seven-eighths reproduction is not a theorem input.

Nine pages; approximately 4,600 extracted words including mathematics,
implementation names and references. Abstract: under 250 words.
Suggested categories remain math.CA, cross-listed cs.LO; no submission has been
made. Keywords: Toeplitz minors, total positivity, entire functions, certified
evaluation, finite-order positivity, Lean. Bibliography and assets are embedded
in the standalone TeX source. Paper CC-BY-4.0; proof code retains Apache-2.0 and
upstream attribution. AI assistance and lack of external human review are disclosed.
