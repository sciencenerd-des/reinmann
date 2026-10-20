# Target B and PF43: CI closeout and formalization version 2

The complete sharded workflow passed at proof commit
`150537bf1d94eced1c22db7660f9c32936372831`:
[run 39470397281](https://github.com/sciencenerd-des/reinmann/actions/runs/39470397281).
All fourteen jobs succeeded: main build/guard, shared dependencies, eleven tile
shards and final rectangle assembly with its separate PF43 check. The final job
refuses missing tile artifacts with `--no-build`. The older serial run is
superseded and supplies no receipt for this closeout.

The current default build, 2,608-row standard-axiom guard, optional rectangle
and actual PF43 target also pass locally. Fresh type examples establish the
unconditional PF43 signature and the retained external hypothesis on PF58.
Five headline axiom checks use only `propext`, `Classical.choice`, `Quot.sound`.
The rectangle has its separate 1,700-declaration audit.

The exact historical README at proof checkpoint `40d4803` was saved and its
SHA256 matched the rectangle manifest before the current README was edited.
All earlier proof manifests remain unchanged. The historical-overlay replayer
passes the full chain through the PNT+ backport; the immutable DH research round
also replays. Historical logs saying product inputs were open describe their
own checkpoints and are not current scope statements.

The README four-track table and `RESEARCH_OBJECTIVE.md` now distinguish:

- Target A's proved standalone theorem, with its simple-zero and isolated-tie
  restrictions retained;
- Target B's proved closed height-14.1 rectangle;
- the proved actual folded-Xi genus-zero identity, inverse-zero summability and
  fixed-rank sector bridge, using the attributed PNT+ backport;
- unconditional ordinary-coefficient PF43 and conditional local PF58;
- the still-open unbounded-rank and RH-equivalent Green-budget obligations.

The newly published unreviewed formalization version is
[DOI 10.5281/zenodo.23516924](https://doi.org/10.5281/zenodo.23516924).
Its seven-page PDF was rebuilt and all pages visually inspected. All four draft
files were downloaded and SHA256-verified before publication. All four public
files were anonymously downloaded and verified afterward, including every
internal source-manifest binding in the complete supplement. The archive
includes all 308 tile source modules and the complete pinned proof source,
dependency configuration, explicit audit inputs, CI receipt and PNT+ attribution.
The original formalization version and the DH-controls record remain intact.

The release presents classical finite facts as formalization. It claims no
RH proof, height-32 certificate, Lean DH atlas, new window record or completed
external peer review. No reviewer email, follow-up or Liu note was sent.
The external 7/8 adapter has not been certified by this closeout.

All new receipts are in `verification_2026_10_20_target_b_closeout/`; the old
date in that folder identifies the proof round, while the client-facing
closeout and publication date is 21 October 2026. Run
`python3 experiments/prime_spectral/verify_target_b_closeout.py` to replay its
checksum-bound receipt and the frozen parent chain.
