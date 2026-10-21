# Minimal external seven-eighths replay

This is an alternative to `replay.py` for the exact same one-file contract.
It fetches only the OpenAI theorem's import closure, rather than the complete
OpenAI project and its unrelated packages. It uses Lean 4.34.1, not this
repository's Lean 4.30.0. Nothing imports external compiled objects into the
local PF58 theorem.

The OpenAI pin is `1581d4cbdd69a0faf34b2089614fe2a814316a6a`.
The minimal configuration keeps upstream's `autoImplicit = false` option,
the required direct dependencies and their exact resolved revisions. The full
upstream manifest is retained; only its root package name changes. Mathlib is
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

Two **upstream compatibility patches are required**. PNT+ is pinned at
`c39a751132c88b6e8080b74c74023fd95b3d8be0` and Rellich–Kondrachov at
`70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23`; their patches come from the
same OpenAI revision. In particular, the unpatched PNT+ Wiener file has two
admitted auxiliary lemmas. Upstream's patch replaces that file with its port
of the proved declarations used here. An inspection of the unpatched file
does not establish the axiom dependencies of OpenAI's theorem. The corrected
import closure passes the source admission scan; the final semantic axiom
audit remains mandatory.

With an installed `leanprover/lean4:v4.34.1` toolchain and at least 12 GiB free
at preparation time:

```sh
python3 bridges/openai-seven-eighths/prepare_minimal.py \
  --project /absolute/path/to/new-external-project
python3 bridges/openai-seven-eighths/minimal_replay.py \
  --project /absolute/path/to/new-external-project \
  --output /absolute/path/to/new-build-receipt --batch-size 2 --compact-setups
```

Preparation downloads source and dependencies; it does not certify a theorem.
The pinned import closure has 2,924 OpenAI modules and 19 non-Mathlib dependency
modules after patching. The runner selects 275 Mathlib-cache roots and builds
the other 2,943 modules in dependency order. It checks source hashes, the
manifest, dependency revisions and patch hashes before building, and checks
the inputs again afterward. It stops before another build command when free
space falls below 4 GiB. This check does not reserve space during a command.

Lake 4.34.1 also writes a large generated `*.setup.json` per compiled module.
On this closure these can exceed 10 GiB in total. The optional one-shot
`compact_setups.py` archives only scratch files belonging to completed,
checksum-bound OAI build commands, verifies each archive by decompression, and
retains recovery metadata before removing the generated originals:

```sh
python3 bridges/openai-seven-eighths/compact_setups.py \
  --project /absolute/path/to/external-project \
  --attempt /absolute/path/to/build-receipt \
  --output /absolute/path/to/new-compaction-receipt.json
```

`--compact-setups` invokes this helper between successful batches; it is also
available as the one-shot command above. Repeat `--attempt` for earlier compatible attempts when resuming. The helper
does not touch proof sources, compiled objects, dependency caches or unfinished
targets. `--restore /absolute/path/to/compaction-receipt.json` restores original
bytes and timestamps. An actual `lake --no-build build` probe accepted the
sampled completed modules after compaction. These scratch receipts do not
certify any mathematical result.

`--check-only` records the checked source graph without compiling.
`--resume /absolute/path/to/previous-attempt` accepts successful, checksum-bound
commands only when that attempt's source graph matches; repeat it to include
parent attempts. Their command snapshots are retained in `RESUME.json`. Lake still checks
and builds the complete final adapter dependency graph. A failed attempt has
no successful proof receipt, even if many earlier batches compiled.

The success receipt is written only after the adapter builds and Lean reports
the axioms of **both** `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re` and
`Reinmann.zetaZeroFreeRightOf_sevenEighths`. Only `propext`, `Classical.choice`
and `Quot.sound` are accepted. A lexical scan or a successful environment
check cannot replace these reports.

The original README and research-round receipts record the earlier prepared
state and remain historical. The existence of these new runners is not a
completed seven-eighths replay. Use an actual successful `receipt.json` and its
bound logs to claim completion. The result, if rebuilt, remains an unreviewed
external proof; unconditional PF58 in this repository would require a separate
compatible formal integration.
