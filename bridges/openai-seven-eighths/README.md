# Exact external seven-eighths contract

`SevenEighths.lean` is a one-file adapter to OpenAI's theorem, with the exact
definition used in `Reinmann/QuasiRHInputs.lean`. It contains no admission,
custom axiom or `native_decide`. It is intended to run in the upstream project,
not to import incompatible compiled objects into this repository.

Pinned source: [openai/math at 1581d4c](https://github.com/openai/math/tree/1581d4cbdd69a0faf34b2089614fe2a814316a6a),
Lean `leanprover/lean4:v4.34.1`; upstream's own Lake manifest and compatibility
patches govern its dependencies. The source theorem is
`OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re` in
`lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean`.

With an existing checkout of that exact revision and its dependencies:

```sh
python3 bridges/openai-seven-eighths/replay.py \
  --upstream /absolute/path/to/openai-math \
  --output /absolute/path/to/new-seven-eighths-receipt
```

The runner builds only the theorem's dependency closure, runs this file, checks
both axiom lists, and writes a checksum-bound receipt only on success. A first
build of that closure is substantial: the cited independent rebuild reports
2,924 modules. Do not confuse the short adapter with a small dependency proof.

**Current status:** prepared, not rebuilt locally on 4.34.1. The local PNT+
backport is a separate completed build; it does not verify OpenAI's arithmetic
argument. The [independent rebuild](https://github.com/tomoto0/quasi-riemann-hypothesis-7-8-verification/tree/b83a73c6cb626a391e551baafdb7d0cceafaa55a)
is external evidence, not this adapter's build receipt. `finitePF58` in this
repository continues to take the named external input. No external Lean proof
has been silently replaced by an axiom here, and the result remains unrefereed.
