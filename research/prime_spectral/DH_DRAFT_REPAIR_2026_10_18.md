# Controls draft supplement repair, 18 October 2026

Zenodo draft 23401370 remains unpublished. The designated Platt thread contains
only the sent request; no substantive human read has arrived. No follow-up,
Liu note or Publish action was sent. The existing quiet review monitor now
points to this repair receipt and retains the publication conditions.

## Complete supplement on the draft

A full-file browser transfer failed at 53%, after earlier CLI TLS/DNS errors.
Its incomplete zero-size file entry was removed. The remaining 18 small parts
were then uploaded through Chrome, completing the earlier 52 verified parts.
The draft now contains exactly 74 files:

- the unchanged current 19-page controls PDF;
- all 70 two-MiB parts (the last part is shorter);
- the per-part JSON checksum manifest;
- corrected reassembly instructions;
- the portable Python reassembly verifier.

Every part has a matching server size and MD5. Downloaded part bytes were checked
against their SHA256 values; previously verified downloads were reused only
with matching current server metadata and local SHA256. The downloaded parts
were reassembled and the entire archive checked:

    bytes:  145540103
    SHA256: 1a899aba7d560e41692fce94c6ad0352e75822545db128462af8607be272293c

The portable verifier independently accepted that downloaded part directory and
the reconstructed archive. The PDF and three reader files were downloaded and
matched byte-for-byte to their local sources. The PDF SHA256 is

    ea0908b5320226842791f9b732993c67138bc9c7762197cb45f3a2bc60224ed5

The archive matches the previously verified complete scientific capsule, with
1005 regular members and its manifest binding 1004 artifacts. The current formal
Lean development is also available separately in GitHub, beyond that capsule.

Only after these checks was the obsolete 15 October archive removed from the
draft. Its exact local backup was verified and retained in the historical
xi-eigenvector-reduction worktree. No unexpected file was deleted or found.
The final draft state is `unsubmitted`. A screenshot and checksum receipts are
in `verification_2026_10_18_draft_repair/`.

## Publication conditions remain

This fixes the supplement-transfer blocker; it does not complete human review
or authorize bypassing it. Before publication, address the substantive review,
rebuild the then-current PDF, and freshly verify both the PDF and complete
supplement on the draft. Historical checks do not certify future uploaded
bytes. The DOI is reserved, not a published release.

## Formal work and remaining mathematical obligations

Proof commit 83a728a is upstream and passed the full build and 313-theorem
standard-axiom audit. The Jacobi identity now transfers the finite-product
split-pair result to actual original-coefficient Toeplitz minors.
The Cauchy-tail, finite-theta and enclosure-rule components compile; the entire
extension and actual Xi zero-free rectangle certificate remain incomplete.

`SPLIT_PAIR_MIXED_REMAINDER_2026_10_18.md` gives a mathematical proof draft for
the missing mixed-row estimate. Repeated pole choices vanish, leaving decay at
rate |a_*|/R<1 instead of a potentially false rate obtained by repeating the
largest pole modulus. This draft is not yet a Lean theorem. Patching the pole
germs, deriving the actual coefficient decomposition and formalizing the mixed
row estimate remain to be done. No RH bridge acquires simplicity or no-ties
hypotheses.

The verification-ledger commits were retained locally after repeated Git and
GitHub API writes failed with TLS bad-record-MAC errors. The earlier requested
commits and the substantive Lean proof commit were already pushed. A failed
transfer is not reported as a successful push; the final session report records
whether a subsequent retry succeeds.
