# Unconditional finite-width PF97 on Lean 4.30

All thirty-four jobs of [run 39733278869](https://github.com/sciencenerd-des/reinmann/actions/runs/39733278869) succeeded at
`b4ec4a3920973faae02d4d9f3a56456886df49c9`. This includes the root build and audit, shared
dependencies, eleven original-rectangle shards, three PF58 shards, seventeen
PF97 shards, and the final certificate assembly and semantic audits.

```lean
Reinmann.XiFinitePFCertified.finitePF97 : FinitePF XiMomentCoeff 97
```

There is no theorem hypothesis. Every ordered Toeplitz minor through rank 97,
at every shift, is nonnegative for the ordinary folded-Xi coefficient sequence.
This is finite strengthening of classical zero-location information; it does
not establish strict positivity, the unbounded-rank criterion or RH.

The 67 new degree-16 tiles prove nonvanishing on the upper-right box
`[29/40,1] × [14.1,32]`. Combined with the existing full rectangle through
height 14.1 and conjugation, they certify `[29/40,1] × [-32,32]`.
Reflection then proves `LowHeightWidth (9/40) 32`. The two-band angle bound
and proved fixed-rank sector bridge yield PF97. Critical-line zeros above
14.1 remain allowed: the full critical strip is not claimed zero-free to 32.

The shared height-32 inputs are proved on Lean/Mathlib 4.30, including the
unit-circle Xi majorant 1000, Gamma coefficient error at most 4e-14,
regularized zeta coefficient error at most 1/5000, and the 160-term logarithm
enclosure on a radius-4/5 disk. No old height-14.1 constant was extrapolated.
The conditional width-only PF58 and PF97 wrappers remain available alongside
the unconditional numerical applications.

The default root audit covers 2,643 declarations. The PF97 audit checks
363,579 distinct implementation theorem constants, including the public
entry points, using only `propext`, `Classical.choice` and `Quot.sound`.
The PF58 audit is separately retained in the same run. These implementation
counts include private generated theorems and are not counts of new results.
The final job refused tile rebuilds before assembly and checked the actual
no-hypothesis types and axiom dependencies of both canonical public theorems.

The immutable packet `verification_2026_10_22_pf97_closeout/` contains the
actual all-job receipt, complete raw run logs, audit sources and outputs,
and 1,192 proof/configuration hashes bound to the exact proof commit.

```sh
python3 experiments/prime_spectral/capture_finite_band_ci.py \
  --verify research/prime_spectral/verification_2026_10_22_pf97_closeout
```

Earlier pilot and pending-CI receipts remain historical, without rewriting
their manifests. The independent global seven-eighths reproduction remains
on its separate Lean 4.34.1 toolchain; no compiled object or external theorem
from that replay enters these Lean 4.30 certificates. The DH register retains
these ranks as shared finite strengthening, with no new arithmetic discriminator.
Stopped research directions and published paper versions are unchanged.
