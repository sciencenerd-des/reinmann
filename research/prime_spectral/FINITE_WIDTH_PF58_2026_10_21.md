# Finite-width PF58 certificate candidate

The conditional calibration core compiles on Lean/Mathlib 4.30.0:

```lean
finitePF58_of_two_bands
    (hlow : ZetaNoLowStripZero (141 / 10))
    (hband : LowHeightWidth (3 / 8) 19) : FinitePF XiMomentCoeff 58
```

It uses `angleBound_of_two_bands` with rank 58 and `Real.pi_gt_d2`.
The optional `XiFinitePFCertified.finitePF58_of_low_height_width` wrapper
supplies the already certified first-zero bound. It remains outside the
lightweight default import, since it imports numerical tiles.

The new bounds in `FiniteBandBounds` are proved through height 32, rather than
extrapolated from 14.1. They give a unit-circle Xi majorant of 1000 and hence
the ordinary Taylor coefficient bound. The proof uses
`exp(-1) ≤ 2/5`, derived from the quadratic lower bound for `exp(1)`.
The existing Gamma-factor norm and 4e-14 coefficient-error bounds have no
height restriction. The endpoint-27 regularized zeta model now has a separately
proved 1/5000 coefficient-error budget through height 32. The shifted principal
log uses scaling by 32 and 160 terms on a disk of radius 4/5; its error is
proved at most 1e-15.

The Arb planner accounts for these proved budgets. For PF58 it proposes nine
degree-16 balls covering `[7/8,1] × [14.1,19]`. The old certified rectangle
supplies the entire lower part. `FiniteBandGeometry` proves that this union,
conjugation and reflection imply `LowHeightWidth (3/8) 19`. The generated
`XiBand58` candidate then supplies the finite-width proof to the sector theorem.
It does not use the global seven-eighths theorem.

The default build and its 2,643-declaration standard-axiom audit passed locally.
One complete new tile, `Tile000`, has been checked in Lean and its nonvanishing
theorem uses only `propext`, `Classical.choice` and `Quot.sound`. Its fresh Gamma
module took 180 seconds; the remaining pilot stages, including a cached Gamma
check, took 235 seconds. Gamma modules are serialized within each runner
because the degree-16 pilot used several GB of memory.

**The complete PF58 assembly is still pending split CI at this snapshot.**
The workflow adds three shard jobs for the nine new tiles. Its final job must
refuse all old and new tile rebuilds, assemble both certificates, audit the
new band theorem closure, and check the unconditional PF58 entry point.
Together with the existing jobs this requires seventeen successful jobs.
The unconditional declarations in the candidate source are not a substitute
for their successful elaboration and audit.

`verification_2026_10_21_finite_bands/` retains both plans, the historical
predecessor receipt, exact pre-change source snapshots, the pilot timing table,
and checksum-bound raw logs inside `local-validation-logs.tar.gz`. The pilot
timing table records its original execution paths; the corresponding raw
bytes are preserved in that archive. The earlier immutable checkpoint chain
was replayed using the exact `bd12b0e` source overlay, without rewriting any
old manifest.

PF97 is the next finite extension. Its box is
`[29/40,1] × [14.1,32]`, again using the old rectangle below 14.1.
The same proved budgets give a 67-tile plan. This is a plan only; no PF97
certificate is claimed at this snapshot.

These are finite strengthening results. The DH all-rank failure register and
its first-tested-versus-globally-first distinctions remain unchanged. No new
arithmetic discriminator, all-rank theorem, or RH proof is asserted. The
separate successful OpenAI seven-eighths replay remains credited and retained;
no Lean 4.34 object is imported into this Lean 4.30 development. Published
Zenodo versions remain unchanged.

Source and historical-receipt checks:

```sh
python3 experiments/prime_spectral/verify_finite_band.py --rank 58
python3 experiments/prime_spectral/replay_finite_band_predecessors.py --output /tmp/new-parent-replay.json
```

The full live audit requires compiled tile outputs:

```sh
python3 experiments/prime_spectral/verify_finite_band.py --rank 58 --live-audit --output tmp/pf58-audit
```
