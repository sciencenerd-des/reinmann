# External seven-eighths proof replay

Upstream: https://github.com/openai/math/tree/1581d4cbdd69a0faf34b2089614fe2a814316a6a

Toolchain: `leanprover/lean4:v4.34.1`. All 2,943 source modules outside the pinned Mathlib cache are covered by the retained successful command history. The source archive contains the 2,924 OpenAI modules, 19 dependency modules, official compatibility patches, exact configuration and licenses.

The two kernel axiom reports cover the upstream theorem and the exact `Reinmann.ZetaZeroFreeRightOf (7/8)` adapter. The main Lean 4.30 project continues to carry the named external input in its PF58 theorem.

Verify packet integrity with:

```sh
python3 bridges/openai-seven-eighths/finalize_minimal_replay.py --verify-packet /absolute/path/to/packet
```

Packet verification checks retained evidence. A fresh kernel rebuild uses `prepare_minimal.py` and `minimal_replay.py` in a new external directory as described in the archived reproduction instructions.
