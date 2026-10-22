# Version 3 release — published and anonymously verified

Prepared on 22 October 2026. The ten-page `main.pdf` and editable `main.tex`
extend the published version 2 with unconditional finite PF58 and PF97.
The author authorized publication on 22 October 2026. Version 3.0.0 is published
at [DOI 10.5281/zenodo.23561417](https://doi.org/10.5281/zenodo.23561417).
All four current draft files were downloaded and SHA256-verified before
publication; all four public files were then downloaded without authentication
and verified again, including every source-archive member.
The existing v1/v2 sources, PDFs and release receipts are unchanged.

## Verified proof and manuscript inputs

- The current proof source is `b4ec4a3920973faae02d4d9f3a56456886df49c9`,
  on Lean/Mathlib 4.30.0. All 34 jobs of
  [run 39733278869](https://github.com/sciencenerd-des/reinmann/actions/runs/39733278869)
  passed, including no-rebuild assembly and actual public-theorem axiom audits.
- The complete source-bound CI packet is retained in documentation commit
  `ad30a35e93474981528c24d91ae93338ad34958f`. The release re-verified that packet;
  it does not claim a new kernel rebuild or CI coverage of manuscript prose.
- The revised theorem statements and constants are cross-checked against the
  source files bound by that packet. No new Lean proof or evaluator constant
  is introduced by the manuscript revision.
- The final source compiles with Tectonic and the desktop LaTeX compiler.
  No overfull boxes, unresolved references or citation warnings remain.
  The release-edited PDF received a fresh ten-page visual receipt.
- The classical benchmark and the two seven-eighths bibliography entries were
  checked against the primary sources and the pinned replay packet. The
  benchmark is an inference from published computation, not a new Lean result.
- The previous nine-page draft receipt remains historical at `9e09d56`.
  The pre-release correction receipt remains at
  `research/prime_spectral/verification_2026_10_22_formal_pf97_release_fixes/`;
  fresh release evidence is stored separately in
  `research/prime_spectral/verification_2026_10_22_formal_pf97_release/`.

## Completed release conditions

1. Publication authorization: received from the author on 22 October 2026.
2. Retain the unreviewed status unless a substantive external human read actually
   occurs. No external human review is claimed or required for this authorized unreviewed release.
3. Package the entire pinned proof source, all old and new numerical tile sources,
   dependency pins, upstream Apache-2.0 attribution, audit inputs and actual CI
   receipts. The supplement and every downloaded file passed the new release verifier.
4. The final release-edited PDF was rebuilt and visually inspected. Its TeX/PDF
   and supplement are bound to fresh checksums; later edits require new receipts.
5. This is a new version of the existing formalization record, concept 23449489.
   Every draft file and the entire supplement were verified before Publish; all
   actual public files were then anonymously verified. Older versions and the
   DH-controls record are unchanged.

## Scope and submission notes

PF58 and PF97 mean nonnegativity of every ordered minor up to the stated rank
at every shift for ordinary folded-Xi coefficients. They are finite
formalizations of classical consequences, not RH or an unbounded-rank result.
The full critical strip is certified only through 14.1; the higher right-hand
boxes allow critical-line zeros. The DH atlas remains external to Lean.
The separate Lean 4.34.1 seven-eighths reproduction is not a theorem input.

Ten pages; approximately 5,000 extracted words including mathematics,
implementation names and references. Abstract: under 250 words.
Suggested categories remain math.CA, cross-listed cs.LO; no submission has been
made. Keywords: Toeplitz minors, total positivity, entire functions, certified
evaluation, finite-order positivity, Lean. Bibliography and assets are embedded
in the standalone TeX source. Paper CC-BY-4.0; proof code retains Apache-2.0 and
upstream attribution. AI assistance and lack of external human review are disclosed.

## Final publication evidence

The complete supplement contains 1,537 archive members, including all 1,192
proof-source/configuration bindings, the 840 numerical tile part source modules,
exact dependency pins, upstream attribution and complete CI/audit receipts.
The proof pin remains `b4ec4a3920973faae02d4d9f3a56456886df49c9`;
all 34 jobs of run 39733278869 passed at that exact pin. Manuscript/release
documentation changes are not advertised as a new proof-source CI run.

The immutable local package contains the prepublication gate snapshot; this
current note records the subsequent verified outcome. Actual DOI, public file
checksums and anonymous-download checks are retained in
`research/prime_spectral/verification_2026_10_22_formal_pf97_release/publication_receipt.json`.
No journal submission or completed external human review is claimed.
