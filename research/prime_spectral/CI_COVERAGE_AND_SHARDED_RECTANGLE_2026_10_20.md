# CI coverage for the PF43 chain and a sharded rectangle job (20 October 2026)

This is an infrastructure change. It proves no new theorem.

## 1. The PF43 chain is now in the default target

Before this change, CI checked none of these: the sector-bridge modules
(`CanonicalZeroIndex` … `XiZeroCorrespondence`), `XiHadamardProduct`, and the
61 backported files under `Reinmann/PNTPlus/`. Neither CI job imported them.

- `Reinmann.lean` and `Reinmann/AxiomAudit.lean` now import the 14 modules.
  The 61 PNT+ files come in through `XiHadamardProduct`.
- `AxiomAudit.lean` lists every theorem constant in those modules (including
  all of `Reinmann.PNTPlus.*`) by a `run_cmd` loop, the same one as in
  `verification_2026_10_20_pnt_hadamard/Audit.lean`. It does not list them by
  name from source.
- The root guard now audits **2,608** theorems (it was 1,619), all using only
  `propext`, `Classical.choice` and `Quot.sound`. See `root_guard.log`.
- `XiFinitePFCertified` imports the optional `XiRectangle` library, so it stays
  outside the root. The rectangle CI job builds it and audits `finitePF43`.

## 2. The rectangle CI job is split across runners

The serial job (`--jobs 1`, about 18 GB of tile proof objects) would hit
GitHub's 6-hour limit. The new layout:

1. `xi-rectangle-deps` builds `Reinmann.RectangleModel`, `XiRectangle.Data`
   and `XiRectangle.Cover` once. It uploads `.lake/build` as a zstd tar.
2. `xi-rectangle-shard` runs 11 matrix jobs, each building four tiles with
   `build_xi_rectangle.py --jobs 2 --tiles …` and uploading only that shard's
   `TileNNN*` outputs. One tile is about 445 MB raw and about 144 MB compressed.
3. `xi-rectangle-certificate` restores the dependencies and unpacks the shard
   outputs one at a time. It then runs
   `lake build XiRectangle.Tile000 … Tile043 --no-build`, which **fails if any
   tile would be rebuilt**. Next it builds `XiRectangle` and
   `Reinmann.XiFinitePFCertified`, runs `verify_xi_rectangle.py --live-audit`,
   and checks the axioms of `finitePF43`.

Why relocated outputs are accepted: Lake traces are content hashes of sources,
options and dependency artifacts, not paths or modification times. Tested
locally: `Tile000` outputs copied into a separate worktree at a different path,
with fresh timestamps, were reported up to date. After a one-line edit to
`Tile000Terms0.lean`, `--no-build` exited with code 3. Cross-runner
reproducibility relies on deterministic `.olean` output for a fixed toolchain,
which is the same assumption Mathlib's shared cache relies on. The
`--no-build` step turns any violation into an immediate failure instead of a
silent serial rebuild.

A workflow-level `concurrency` group now cancels a superseded run on the same
ref. The workflow passes `actionlint` 1.7.7.

## Evidence and frozen checkpoints

`historical_bdbc051/` keeps the exact `Reinmann.lean`, `AxiomAudit.lean` and
`ci.yml` that earlier round manifests bind. Replay those manifests at their own
commits, or against these copies. Logs: `root_guard.log`, `default_build.log`.

The first green hosted run of this workflow is still pending. Until it exists,
Target B and PF43 remain locally verified only. Nothing here proves RH.
