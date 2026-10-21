# Complete CI coverage after the external replay

All 14 jobs of [run 39563749171](https://github.com/sciencenerd-des/reinmann/actions/runs/39563749171)
succeeded at proof commit `a3ca706ff023830d0bc9890d662caa9964b015f7`:

- the default build and its 2,619-declaration standard-axiom audit;
- shared rectangle dependencies and all eleven tile shards;
- final rectangle assembly and the explicit `finitePF43` axiom audit.

The default build log explicitly records fresh builds of
`CornerPowerSumCounterexample` and `FiniteHeightPFCalibration`. Both are now
covered by the root import and audit. The final numerical job refused tile
rebuilds successfully in seven seconds. Its actual PF43 audit output contains
only `propext`, `Classical.choice` and `Quot.sound`.

The immutable receipt in `verification_2026_10_21_ci_complete/` retains the
actual run/job metadata, all job logs, their checksums and 644 proof/configuration
source bindings at the exact commit. The earlier pending snapshots and
verification manifests remain unchanged. This note and its receipt introduce
no Lean source, dependency or workflow change; their documentation commit is
separate from the proof commit checked by CI.

Verify the receipt, and optionally compare the current proof sources, with:

```sh
python3 experiments/prime_spectral/verify_ci_complete_2026_10_21.py
python3 experiments/prime_spectral/verify_ci_complete_2026_10_21.py --check-current-sources
```

This CI covers the Lean 4.30 development, the height-14.1 rectangle and
unconditional PF43. The [external seven-eighths replay](EXTERNAL_SEVEN_EIGHTHS_REPLAY_2026_10_21.md)
is a separate successful local Lean 4.34.1 run. The Lean 4.30 PF58 theorem
continues to require its named seven-eighths input; no compatible integration,
height-32 certificate, unbounded-rank PF theorem or RH proof is asserted here.

The already published formalization version and DH-controls record are
unchanged.
