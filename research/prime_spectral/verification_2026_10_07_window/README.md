# Window verification ledger, 7 October 2026

`checks.json` records executed commands, exit codes and local durations.
The full build and repository audit ran in the shared working tree, which
also contains unrelated uncommitted research. They are not a clean-checkout
validation of every file in this commit. The new window module imports only
Mathlib; its separate 22-statement audit is recorded in `window_axioms.log`.
The repository audit separately reports 240 statements. These counts should
not be mistaken for 262 distinct theorem declarations.

Both numerical certificate reports pin the certificate and verifier hashes.
Each report records four adaptive-integral entry comparisons and a geometric
constant check; these are independent of the Gauss assembly but share Arb.
They do not independently reconstruct every matrix entry. Replay commands
and the analytic proof boundary are in the accompanying proof document.

The Lean module proves conditional assembly, arithmetic and support lemmas.
The actual Weil functional, test-domain identification, analytic bounds and
Arb outputs remain explicit external inputs. No RH or novelty claim follows.
