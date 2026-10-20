# Attributed PNT+ Hadamard backport

These 61 source files are adapted from
[AlexKontorovich/PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/tree/127b50e33f6033e2147921167a117af96d9ba4ea),
commit `127b50e33f6033e2147921167a117af96d9ba4ea`, under Apache-2.0.
The original authors and copyright headers remain in each file; see `LICENSE`.
The Hadamard development and most local analytic helpers are by Matteo
Cipollina. This directory is a compatibility port, not a claim of authorship
or a new factorization theorem.

The upstream toolchain is Lean v4.35.0; this port targets the repository's
unchanged Lean/Mathlib v4.30.0. `UPSTREAM.json` binds every original source hash
and corresponding adapted source hash. Exact original bytes and the complete
adaptation patch are retained in
`research/prime_spectral/verification_2026_10_20_pnt_hadamard/`.

Changes include import-prefix rewrites, three Mathlib import relocations,
removing newer `using!` syntax, restoring older set/measure/continuity lemma
names, disambiguating constant integrability, and local proof adaptations for
function multiplication and the nonnegative pi norm. Trailing whitespace was
normalized. No replacement axioms or admitted proofs were introduced.

The target is
`Reinmann.PNTPlus.Mathlib.NumberTheory.LSeries.RiemannZetaHadamard`.
Its dependency closure includes the general Hadamard factorization, Jensen
summability, divisor products and Xi growth. It does not include or import
OpenAI's 7/8 proof. It remains outside `Reinmann.lean`'s root import; its audit
is separate from the unchanged root audit.
