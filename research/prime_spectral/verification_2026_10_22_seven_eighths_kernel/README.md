# Additional fresh-kernel check of the external seven-eighths reproduction

This packet is separate from the completed 21 October source-build receipt.
Only a successful `result.json`, bound by `manifest.json`, records completion
of this additional check. A running process or an empty log is not success.

The exact adapter is `SevenEighths`, on Lean 4.34.1, for OpenAI source commit
1581d4cbdd69a0faf34b2089614fe2a814316a6a. The runner checks that its current
source/configuration inputs match the completed external build. It runs:

```text
leanchecker --fresh --verbose SevenEighths
```

`--fresh` loads the adapter and replays its imported constant environment into
an empty kernel environment. In Lean's terminology this checks safe,
non-partial declarations; unsafe and partial declarations are skipped.
Inductive constructors and recursors are compared with the ones regenerated
by the kernel. Axiom declarations are accepted as axioms, not proved by this
operation, so both headline theorem axiom reports are checked separately.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed in those reports.
The retained upstream `LeanChecker.lean` and `Replay.lean` describe these
semantics and preserve their Apache-2.0 copyright notices.
The matching upstream source is
[LeanChecker.lean at v4.34.1](https://github.com/leanprover/lean4/blob/v4.34.1/src/LeanChecker.lean).

This uses Lean's own kernel in a separate process. It is not a verifier with
an independently implemented kernel. It adds a check against corrupted or
improperly constructed declaration environments; it does not constitute
human review or establish the mathematical exposition of the source paper.

`compiled_objects.json` binds the exported/server/private compiled data files
available on the recorded search path, including cached dependencies and the
toolchain. This is a conservative superset, **not a count of modules actually
imported or replayed**. The runner hashes these inputs before and after the
fresh replay, rechecks source inputs, and records the checker binary hash.
It does not build targets, download caches or change proof sources.

Reproduce using the existing completed external project and a new output path:

```sh
python3 bridges/openai-seven-eighths/check_kernel.py \
  --project /absolute/path/to/completed-external-project \
  --output /absolute/path/to/new-kernel-receipt
```

`runner_at_start.py` preserves the executed runner. The source/build packet
under `verification_2026_10_21_external_seven_eighths` remains historical and
unchanged. Its remarks about the then-conditional local PF58 are historical:
the current local `Reinmann.XiFinitePFCertified.finitePF58` and `finitePF97`
have separate numerical certificates in Lean 4.30 and do not import this
external Lean 4.34.1 object. No new PF theorem, RH proof, cubic-family estimate,
DH separator, publication or reviewer response is claimed by this packet.
