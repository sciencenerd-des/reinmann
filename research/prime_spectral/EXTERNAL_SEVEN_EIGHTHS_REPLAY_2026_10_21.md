# Completed external seven-eighths replay

The exact external statement has now been rebuilt locally on Lean 4.34.1:

    forall s : Complex, 7/8 < Re(s) -> riemannZeta(s) != 0.

The one-file adapter is `bridges/openai-seven-eighths/SevenEighths.lean`.
It closes `Reinmann.ZetaZeroFreeRightOf (7/8)` directly using
`OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re`. Both theorem axiom reports
contain only `propext`, `Classical.choice` and `Quot.sound`.

This is a reproducibility result for the proof in
[OpenAI's source at 1581d4c](https://github.com/openai/math/tree/1581d4cbdd69a0faf34b2089614fe2a814316a6a).
The proof is credited to that project. It is not a new arithmetic argument
from this repository.

The build used `leanprover/lean4:v4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. It covers 2,924 OpenAI source
modules plus 19 dependency source modules, with Mathlib dependencies obtained
from the selected pinned cache roots. The exact upstream manifest and the
official PNT+ and Rellich–Kondrachov compatibility patches are retained.
No theorem proof source was locally repaired or replaced with an admission.

The terminal verifier checked 991 successful command records across the three
compatible build attempts. Their union covers all 2,943 source modules. It
also rechecked the input hashes, exact adapter, dependency revisions, patch
hashes and final axiom reports. The success packet contains:

- `result.json` and its checksum manifest;
- the complete source/configuration archive, including upstream licenses;
- the compressed build history, with every retained raw log and its hash;
- the complete module/input hash map and reproduction helpers.

The packet is under `verification_2026_10_21_external_seven_eighths/`.
Its source and history archives were read back and every internal file checked.
The earlier preflight receipts remain unchanged and correctly record the
unfinished state at their own snapshots. The standing DH register now points
to the completed replay; its preceding pending version is preserved separately.

**The local Lean 4.30 PF58 theorem still takes the named external input.**
No Lean 4.34 compiled object is imported into the Lean 4.30 development.
The exact external proposition has been independently replayed on its own
toolchain; a compatible local formal integration remains separate. No
unbounded-rank PF or RH theorem is claimed. The classical DH zeros with
Re(s)>1 continue to falsify its global seven-eighths analogue.

The main root and axiom-audit source are unchanged from `91c034d`, whose local
audit covers 2,619 declarations including the two newly imported modules.
Remote CI evidence must identify the pushed commit and the jobs that checked
it; the external build documented here is a local Lean 4.34.1 run.

Check the proof packet and the complete historical receipt chain with:

```sh
python3 experiments/prime_spectral/verify_external_seven_eighths_round.py
```

Packet integrity can also be checked without rerunning the kernel build:

```sh
python3 bridges/openai-seven-eighths/finalize_minimal_replay.py \
  --verify-packet research/prime_spectral/verification_2026_10_21_external_seven_eighths
```

A fresh kernel replay uses `prepare_minimal.py`, `minimal_replay.py` and then
`finalize_minimal_replay.py`, with a separately installed Lean 4.34.1 toolchain.
The finalizer refuses a pending build before writing a success packet.
