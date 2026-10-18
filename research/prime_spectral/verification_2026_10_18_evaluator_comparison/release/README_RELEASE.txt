Finite and analytic split-pair oscillation and the Toeplitz-Jacobi bridge
Unreviewed formalization preprint, 18 October 2026

The theorem sources are pinned to Git commit
7376a2336c3fe9cceaa137b247962dde3ecfc6a3
https://github.com/sciencenerd-des/reinmann/tree/7376a2336c3fe9cceaa137b247962dde3ecfc6a3
Lean and Mathlib: v4.30.0. CI for this exact commit passed:
https://github.com/sciencenerd-des/reinmann/actions/runs/39113141784
The build and 364-declaration axiom audit use only propext, Classical.choice,
and Quot.sound. Source scanning found no unfinished proofs or project axioms.

1. Check each public file's SHA256 against FORMAL_SPLIT_PAIR_RELEASE.json.
2. Extract formal-split-pair-source-7376a23.tar.gz into a new directory.
3. Check the extracted files against SOURCE_MANIFEST.json (standard SHA256).
4. Install elan, enter source/, then run:
   lake exe cache get
   lake build
   bash scripts/verify_axiom_clean.sh
The lake manifest pins dependencies; cache/build commands need network access
on a first run. The code is Apache-2.0; the paper is CC-BY-4.0.

The revised manuscript is included separately from the pinned theorem sources.
It states simple selected zeros and an isolated boundary-pair hypothesis.
No general multiplicity/tie theorem, Lean DH zero atlas, low zero-free rectangle,
or RH proof is claimed. The published DH controls motivate the work but are
external numerical certificates, not a Lean instantiation of the theorem.
AI assistance is disclosed. No completed external human review is claimed.
