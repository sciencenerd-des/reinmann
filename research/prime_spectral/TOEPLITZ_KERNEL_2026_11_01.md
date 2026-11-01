# Direction E follow-up: the finite Toeplitz kernel corollary

The Lean module `Reinmann/ToeplitzKernel.lean` now proves the
finite corank-one kernel-root corollary, for arbitrary matrix size, without
assuming an atomic moment representation. This completes the kernel-root
target from Direction E. A subsequent
[follow-up](TOEPLITZ_ATOMIC_2026_11_01.md) proves the positive atomic
representation in the corank-one case. The later
[general representation](TOEPLITZ_GENERAL_2026_11_01.md) now covers arbitrary
rank as well, under the same explicit PSD/Toeplitz premises.

This is the known finite corollary stated in Connes–van Suijlekom,
[arXiv:2511.23257, Corollary 1.1](https://arxiv.org/html/2511.23257).
No novelty or arithmetic result is claimed. The earlier bounded B–E audit
correctly reported that no formalization had been completed in that round;
its identification of an atomic representation as the missing component
was one proof plan, not a necessary prerequisite to this corollary.
That sealed packet and all earlier evidence are preserved unchanged.

## Exact theorem and conventions

For every natural number n, let T be a complex matrix of size n+1. Assume:

1. `T.PosSemidef`, including Hermitian symmetry;
2. `T i.succ j.succ = T i.castSucc j.castSucc` for all indices i,j of size n;
3. `T.rank = n`;
4. v is a nonzero complex vector with `T * v = 0`.

Then every root z of

\[
p_v(X)=\sum_{j=0}^{n}v_j X^j
\]

has norm one. The nonzero-vector hypothesis is explicit. The n=0 case is
included; a nonzero constant polynomial has no roots.

The public vector theorem is
`Reinmann.ToeplitzKernel.kernel_polynomial_roots_unit_circle`, using
Mathlib's ordinary ascending-coefficient `Polynomial.ofFn`. The equivalent
polynomial statement is `root_norm_eq_one`: p is nonzero, has degree at
most n, and its first n+1 coefficients lie in the kernel. The supplementary
`natDegree_eq_of_kernel` proves that every such p has degree exactly n.

These are full Hermitian two-sided Toeplitz matrices, not the one-sided
Taylor-coefficient Toeplitz matrices used for Pólya-frequency certificates.
`isToeplitz_of_difference` checks the entry convention T_ij=c(j-i).
No PSD hypothesis for any zeta or DH coefficient matrix is asserted.

## Direct shift-energy proof

Write Q(u)=u* T u, conjugating the first slot. Toeplitz invariance gives
Q(Xq)=Q(q) whenever deg(q)<n, with both coefficient vectors padded to n+1.
No boundary coefficient is omitted: q_n=0 and (Xq)_0=0.

If p(z)=0, factor p=(X-z)q. Since p is nonzero,
q is nonzero and deg(p)=deg(q)+1. Kernel membership of p gives
T(Xq)=z Tq. Taking the Hermitian adjoint also gives
(Xq)* T=conjugate(z) q* T. Consequently

\[
Q(q)=Q(Xq)=|z|^2 Q(q).
\]

Q(q) cannot vanish. Positive semidefiniteness would then imply Tq=0;
rank-nullity makes the kernel one-dimensional, so q would be a scalar
multiple of p. That contradicts their different degrees. Cancelling Q(q)
therefore gives |z|=1.

For the full-degree statement, if a nonzero kernel polynomial had degree
less than n, shift isometry and PSD would put Xp in the same kernel.
One-dimensionality would make Xp a scalar multiple of p, again contradicting
degree. No representation theorem, arithmetic inequality or limiting step
is assumed in either proof.

## Research gate and remaining scope

The exact theorem, coefficient conventions and proof plan were recorded in
the DH register before implementation. It is shared finite linear algebra:
the same theorem applies to a DH-derived matrix whenever that matrix
satisfies the same PSD, Toeplitz and corank-one hypotheses. It therefore
supplies no arithmetic discriminator. A missing PSD or rank hypothesis is
not furnished by this formalization.

No spectral/DH scan, claim of a zeta kernel, unbounded-order passage,
continuous operator theorem, external 7/8 port or toolchain migration is
part of this follow-up. The arithmetic routes from B/C and the direct-side
endpoint remain uninstantiated. The standing gate still reports no active
RH strategy with a proved discriminator.

## Verification and reproduction

The module builds on pinned Lean/Mathlib 4.30. All three headline theorems
print only `propext`, `Classical.choice`, and `Quot.sound`. The source contains
no `sorry`, `admit`, custom axiom or assumed atomic representation.
A fresh Lean own-kernel replay passed with 5,303 import modules and 21,210
compiled/metadata files bound and unchanged. The five earlier packets replay
against historical inputs and all 1,837 earlier non-cache verification files
retain their hashes in that original standalone packet.

The integration follow-up imports this module into both `Reinmann.lean`
and `Reinmann/AxiomAudit.lean`, and adds four explicit axiom prints:
`root_norm_eq_one`, `kernel_polynomial_roots_unit_circle`,
`natDegree_eq_of_kernel`, and `isToeplitz_of_difference`. All project audit
imports are root imports; the existing Lean axiom-collection utility is in
the root's dependency closure. The default `lake build` succeeds (3,995
jobs), and `scripts/verify_axiom_clean.sh` passes with 2,647 audited theorem
reports, zero sorry and zero custom axioms. The dependency pins are unchanged.
These are local dirty-working-tree checks on HEAD `26da3df`, not a remote
CI receipt. No commit is created. The new integration packet preserves the
original standalone receipt and replays it against historical inputs.

```sh
lake build
bash scripts/verify_axiom_clean.sh
python3 experiments/prime_spectral/check_dh_research_gate.py
python3 research/prime_spectral/verification_2026_11_01_toeplitz_integration/validate.py
```

The integration packet binds its source, logs, register snapshots, prior
evidence hashes, and actual checkout HEAD. Its validator replays all six
earlier packets against their historical source bytes, preserving 1,862
previous verification files unchanged. The original standalone packet's
kernel replay script runs Lean's own
`leanchecker --fresh --verbose Reinmann.ToeplitzKernel` and records the
compiled import graph and input hashes; this is a Lean kernel replay,
not an independently implemented verifier. To repeat that check
without writing into a sealed packet, run
`lake env leanchecker --fresh --verbose Reinmann.ToeplitzKernel`.
The original standalone validator checks its historical root-import state;
the integration validator now replays that packet against its saved sources.
The record-generation script refuses to modify a sealed packet.
