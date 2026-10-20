# Unpublished second-version candidate

This folder is a revision candidate for the existing formalization preprint
[10.5281/zenodo.23449490](https://doi.org/10.5281/zenodo.23449490). The original
five-page paper and its release receipts are preserved in the parent folder
and their immutable verification directory. No new Zenodo version exists yet.

The added claims are the Lean actual-Xi evaluator, closed height-14.1 rectangle,
and unconditional ordinary-coefficient PF43, all formalizations of classical
facts. The source pin is `150537bf1d94eced1c22db7660f9c32936372831` on Lean/Mathlib
v4.30.0. The root audit has 2,608 rows; the rectangle and PF43 have separate
build and audit steps. The PNT+ backport retains its Apache-2.0 attribution.
The split-pair theorem keeps its simple-zero and isolated-tie assumptions.
There is no Lean DH instantiation, unconditional local PF58, or RH proof.

Release requires successful `build-and-verify`, `xi-rectangle-deps`, all eleven
tile shards, and `xi-rectangle-certificate` in
[run 39470397281](https://github.com/sciencenerd-des/reinmann/actions/runs/39470397281).
Until then, the PDF explicitly says the hosted rectangle check is pending.
After success, replace those pending labels with the actual receipt, rebuild
and inspect the PDF, bundle all source files at the pin (including all numerical
tile modules), and checksum-verify the complete downloadable PDF and supplement
before publishing a new version of the existing formalization record.

Do not update the DH-controls record or overwrite historical source/CI manifests.
The paper remains an unreviewed preprint and discloses AI assistance. A local
compilation or a passed root audit alone does not open the release gate.

Suggested submission: math.CA, cross-listed cs.LO; no arXiv/ITP/CPP submission
has been made. Keywords: Toeplitz minors, total positivity, entire functions,
certified evaluation, zero-free rectangle, Lean. Current PDF: seven pages.
