# Unconditional finite-width PF58 on Lean 4.30

All seventeen jobs of [run 39730502820](https://github.com/sciencenerd-des/reinmann/actions/runs/39730502820)
succeeded at `1d97a061c5b983f853cf6ca861004e20bd84bf50`. The closed box
`[7/8,1] × [0,19]`, the existing first-zero bound 14.1 and the proved sector
bridge now yield:

```lean
Reinmann.XiFinitePFCertified.finitePF58 : FinitePF XiMomentCoeff 58
```

There is no theorem hypothesis. This means nonnegativity of all ordered
Toeplitz minors through rank 58, at every shift, for the ordinary folded-Xi
coefficient sequence. It is a fixed-rank statement, not the unbounded-rank
criterion or RH.

The requested conditional wrapper is also checked:

```lean
finitePF58_of_low_height_width
    (hband : FiniteHeightPFCalibration.LowHeightWidth (3 / 8) 19) :
    FinitePF XiMomentCoeff 58
```

The general two-band proof remains next to the PF97 calibration in the default
library. The wrapper supplies the actual numerical low-height theorem and
therefore belongs to the optional numerical library.

The default root audit covers 2,643 declarations. The separate band audit checks
47,896 distinct theorem constants, including generated/private implementation
theorems and the two public wrappers; every axiom list is contained in
`[propext, Classical.choice, Quot.sound]`. These are implementation declaration
counts, not a claim of that many new mathematical results. The final job
refused tile rebuilds before assembly. Cached outputs from successful preceding
shards were checked by Lake traces, with a fresh-build fallback.

The checksum-bound packet in `verification_2026_10_22_pf58_closeout/` retains
the exact run and jobs, complete raw logs, actual audit source/output, and
718 tracked source/configuration bindings at that proof commit. The original
failed uniqueness report and the corrected collector's pilot remain separately
recorded; the failed run is not relabelled as successful.

```sh
python3 experiments/prime_spectral/capture_finite_band_ci.py \
  --verify research/prime_spectral/verification_2026_10_22_pf58_closeout
```

The height-32 majorant and evaluator bounds used here were newly proved, not
extrapolated from height 14.1. The nine upper-box tiles supplement the existing
low rectangle. Critical-line zeros above 14.1 are allowed. The independent
OpenAI seven-eighths reproduction stays on record on its own toolchain; this
finite certificate imports no external proof. PF97 is the next separately
gated finite-width certificate. Published paper versions are unchanged.
