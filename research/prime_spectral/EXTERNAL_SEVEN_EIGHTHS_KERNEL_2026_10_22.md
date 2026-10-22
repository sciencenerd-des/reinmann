# Fresh-kernel check of the external seven-eighths reproduction

The additional check completed successfully on 22 October 2026:

```text
Lean 4.34.1: leanchecker --fresh --verbose SevenEighths
exit code: 0
elapsed: 587.316 seconds
```

The adapter and imported safe, non-partial declarations were replayed in an
empty kernel environment. Both
`OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re` and
`Reinmann.zetaZeroFreeRightOf_sevenEighths` were then audited again and use
only `propext`, `Classical.choice` and `Quot.sound`.

This is Lean's own kernel, run separately from the original elaboration. It
is **not** a separately implemented external verifier. Lean's replay skips
unsafe and partial declarations; axiom declarations remain axioms. See the
[upstream checker](https://github.com/leanprover/lean4/blob/v4.34.1/src/LeanChecker.lean)
and the retained checker/replay sources for the exact semantics.

The new runner first checked current sources, manifests, dependency revisions,
upstream patches and adapter against the completed external build. It bound
22,830 compiled data files on the search path, totaling 6,263,069,552 bytes,
and checked source and compiled-input stability after the replay. This file
count is a conservative search-path inventory, **not a theorem count or an
exact imported-module count**. The checker executable is checksum-bound too.
The final saved receipt and all 13 packet bindings were independently read
back and verified after completion.

Evidence: [verification packet](verification_2026_10_22_seven_eighths_kernel/README.md),
[result](verification_2026_10_22_seven_eighths_kernel/result.json),
[commands and timings](verification_2026_10_22_seven_eighths_kernel/commands.json),
and [manifest](verification_2026_10_22_seven_eighths_kernel/manifest.json).
The reproducible runner is `bridges/openai-seven-eighths/check_kernel.py`;
its executed copy is retained in the packet.

This strengthens reproduction of the unrefereed OpenAI proof at commit
1581d4cbdd69a0faf34b2089614fe2a814316a6a. It adds no new arithmetic estimate
and is not an RH proof. The independent local Lean 4.30 PF58/PF97 numerical
certificates do not depend on this external Lean 4.34.1 object. The older
external-build packet is preserved, including its historical description of
the then-conditional PF58 wrapper.

No proof source, root import, numerical certificate, published version or old
verification manifest changed. This was a local checker run, not a new proof
CI receipt. Cubic development remains parked pending Dunn's review; no Weil
window computation, PF box extension or new RH route was started.
