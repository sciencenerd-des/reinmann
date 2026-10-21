# Default CI coverage, the DH half-plane control and build disk space

`CornerPowerSumCounterexample` and `FiniteHeightPFCalibration` are now imported
by `Reinmann.lean` and `Reinmann/AxiomAudit.lean`. The audit's module selector
also includes both. The existing `build-and-verify` job therefore builds and
audits them on the next push; no additional numerical job is needed. Their
project imports already belong to the default root, so neither introduces a
dependency on the optional numerical rectangle.

The local default build passed, followed by the root source/semantic guard.
The expanded audit has **2,619 rows**, up from 2,608: five public theorems and
six elaborator-generated helper theorems. All use only the standard axioms.
The full audit output is retained, including the five headline statements.
This round is locally verified; it has not acquired a new remote CI receipt.
The push is held with `b7848bd` while the external rebuild runs.

The preceding closeout run
[39512801397](https://github.com/sciencenerd-des/reinmann/actions/runs/39512801397)
was checked live: all 14 jobs passed at
`04964c00590d9cd8a697d95186470b6c698d56b2`, including the eight-second tile
no-rebuild check. This supplements the earlier successful proof-source run
39470397281 at `150537b`; neither run is advertised as checking this new round.

The DH register now includes a separate finite-strengthening control for the
**global** 7/8 half-plane statement. Titchmarsh (1986),
[§10.25, pp. 282–285](https://sites.math.rutgers.edu/~zeilberg/EM18/TitchmarshZeta.pdf),
establishes infinitely many zeros with Re(s)>1 for the same mod-5 coefficient
formula. Its displayed kappa matches the repository's control. This falsifies
the global DH analogue, even though the height-85.7 zero and height-340 atlas
do not. The register explicitly leaves the first numerical height and any
certified zero ball above Re(s)=1 unknown. The proof's Hecke/Mobius/Gauss-sum
arithmetic cannot be supplied by the DH mixture. This is no new positivity
inequality or RH-strength strategy.

The old external build-attempt directories contain only a few megabytes of
logs and receipts; their proof outputs are shared in the external project's
build directory. Deleting those attempts would save little and lose useful
provenance. They were retained. The main checkout's generated tile objects
were instead inventoried and checksummed before removal: **2,464 files,
7,961,018,368 allocated bytes** (about 7.4 GiB). All 312 tracked rectangle
source/configuration files were compared byte-for-byte with the successful
CI commit and preserved. No active compiler used this checkout's tile cache.
The other worktree's editor server and the external build were left running.

The tile objects were already filesystem-compressed; a second local archive
would recover little. Recovery uses the unchanged sources and
`experiments/prime_spectral/build_xi_rectangle.py`. Optional rectangle imports
will need restored or rebuilt objects. The default build and audit above
passed after eviction, demonstrating that they do not require that cache.
Free space rose to about 15 GiB; ongoing external compilation consumes some.

The retained external snapshot has 778 of 2,943 source modules completed and
no final proof receipt. Its standard-axiom audit remains mandatory. This note
does not assert the external 7/8 theorem has rebuilt or make local PF58
unconditional. PF97 retains its explicit height-32 width hypothesis.

All previous verification manifests and published files remain unchanged.
Exact preceding root/register bytes are saved under
`verification_2026_10_21_ci_coverage/historical_b7848bd/`. The new
`replay_ci_coverage_predecessors.py` uses those bytes in a temporary overlay
and successfully replays the complete closeout/research predecessor chain.
Current proof builds and audits are checked separately. Replay this round with:

```sh
python3 experiments/prime_spectral/verify_ci_coverage_round.py
```
