# Prescribed atoms and the exact finite-data uniqueness boundary

The finite Toeplitz uniqueness boundary is now proved pointwise, not just
illustrated by a one-by-one counterexample. For every complex PSD Toeplitz
matrix T of size n+1:

\[
\text{positive finite supported atomic data for T are unique}
\quad\Longleftrightarrow\quad \operatorname{rank}(T)\le n.
\]

Every full-rank case has two positive rank-sized representations with
distinct supports. The stronger construction allows any prescribed
unit-circle point to be included in such a representation of a positive
definite Toeplitz matrix.

These are known shared finite-algebra facts. No new arithmetic PSD estimate,
RH discriminator or mathematical novelty is claimed. The singular uniqueness
checkpoint is commit `cbe9d77`; its proofs and sealed evidence are unchanged.

## Exact statements

`ToeplitzPrescribedAtom.exists_representation_containing` assumes T.PosDef,
Toeplitz invariance, and |z|=1. It constructs a finite support S and real
weights w satisfying:

- |S|=rank(T)=n+1 and z belongs to S;
- every node has norm one and every supported weight is strictly positive;
- T_ij=sum_(x in S) w(x)*conjugate(x^i)*x^j.

`ToeplitzFullRank.nonunique_of_full_rank` assumes PSD, Toeplitz invariance
and rank(T)=n+1. It returns two such rank-sized supports, proves they differ,
and proves both reproduce every matrix entry.

`HasUniquePositiveAtomicData` compares every pair of finite positive
unit-circle representations, with no cardinality bound. It requires equal
supports and equal weights on that support. It deliberately does not compare
arbitrary values of the weight functions elsewhere.
`unique_supported_data_iff_singular` proves the displayed equivalence under
only PSD and Toeplitz invariance. The existing general representation theorem
ensures the uniqueness property is not vacuous.

All statements use the original full Hermitian two-sided Toeplitz matrices,
ordinary ascending polynomial coefficients and original entry orientation.
The type is indexed by Fin(n+1), including the one-by-one case; empty
zero-by-zero matrices are not part of this statement.

## Prescribed-node downdate

For a chosen complex node z, let b_i=conjugate(z^i). This vector is nonzero
because b_0=1. The two Schur-complement identities with
D=bᴴ T^{-1} b show that there is a real a>0 such that

\[
A=T-a\,bb^{*}
\]

is PSD and singular. The nonzero vector T^{-1}b lies in its kernel.
This downdate statement holds for any complex z; unit norm is used later
to preserve Toeplitz invariance.

For a unit-circle node z, A is Toeplitz. Apply the singular representation
theorem to A, then add the positive atom at z, merging the weight if z was
already in the support. The rectangular rank bound and rank(T)=n+1 force
exactly n+1 nodes in the resulting representation. All steps are proved in
Lean; no prescribed-node representation is assumed.

## Nonuniqueness in every full-rank case

Start with any rank-sized representation of T. Its finite support cannot
exhaust the unit circle. An elementary injective parameterization

\[
x\longmapsto\frac{\overline{x-i}}{x-i},\qquad x\in\mathbb R,
\]

proves the existence of a unit-circle point outside that support. Its norm
is one, and cross multiplication proves injectivity. The prescribed-node
construction produces a second support containing this new point, so the
supports differ. This is an exact existence proof, not a scan or a sampled
numerical argument.

Combine this with the preceding singular-case uniqueness theorem to obtain
the exact rank criterion. This checkpoint concerns positive finite data.
The subsequent [measure follow-up](TOEPLITZ_MEASURE_2026_11_01.md) proves
uniqueness among all finite positive unit-circle Borel measures in singular
rank, without assuming that a competitor is atomic. No continuous-operator
theorem is claimed.

## Integration, evidence and research scope

Both new modules are imported by the root and AxiomAudit. Four explicit
axiom checks cover the node downdate, prescribed-node representation,
universal full-rank nonuniqueness and the exact uniqueness criterion.
Project audit imports remain root imports. The default build passes
(4,003 jobs); axiom-clean passes with 2,671 audited theorem reports,
zero sorry and zero custom axioms. These are local dirty-working-tree
checks over `cbe9d77`, not a remote CI receipt.

The exact target and DH analogue were preregistered. The result holds for
DH-derived matrices under the same premises, supplies no arithmetic PSD
estimate and activates no RH strategy. Earlier sealed evidence is preserved.

```sh
lake build
bash scripts/verify_axiom_clean.sh
python3 experiments/prime_spectral/check_dh_research_gate.py
python3 research/prime_spectral/verification_2026_11_01_toeplitz_full_rank/validate.py
```

The packet replays all ten earlier packets against historical sources and
verifies that 1,972 earlier verification files are unchanged. Fresh replay
passes for 5,561 modules, binding 22,226 compiled and metadata files. It uses
Lean's own kernel, not an independently implemented verifier.
