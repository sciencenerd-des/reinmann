# Uniqueness of finite positive Toeplitz atoms and the rank boundary

`Reinmann/ToeplitzUniqueness.lean` proves singular-case uniqueness of the
finite support and its supported weights. It also proves weight recovery
on a fixed support and gives a full-rank counterexample to unconditional
support uniqueness. These are known shared finite-algebra facts, not new
arithmetic estimates or an RH discriminator.

The general representation checkpoint is commit `d9c3c79`. Its proof
modules and all earlier sealed evidence are preserved unchanged.

## Singular-case statement

For a complex PSD Toeplitz matrix T of size n+1 with rank(T)<=n,
`exists_unique_atomic_representation_singular` supplies the existing
rank(T)-atom representation and proves its support and supported weights
unique among **all positive finite competing representations** of T.

The competitor needs no rank-sized atom-count assumption. Its nodes need
not even be separately assumed to lie on the unit circle: the proof forces
them into the reference support. The existence part retains the original
unit-circle, strictly positive real weights and entry convention

\[
T_{ij}=\sum_{z\in S}w(z)\,\overline{z^i}\,z^j.
\]

The support is a finite set of distinct complex nodes. Weight functions
are compared only on this support; their arbitrary values elsewhere are
not asserted equal. The result concerns finite representations, not a
formal uniqueness theorem for arbitrary measures or continuous operators.
Zero rank is included and forces the empty support.

## Fixed-support recovery

`weights_eq_on_support` proves that, for a fixed support S with
|S|<=n+1, equality of the atomic matrices determines every weight on S.
This statement needs neither positivity nor unit-circle assumptions.
The Lagrange polynomial at z has degree at most n, and applying the matrix's
first row to its coefficient vector returns exactly w(z).

Thus a prescribed full-rank support can have uniquely determined weights
even though the support itself is not unconditionally unique.

## Why singularity gives support uniqueness

For every polynomial q of degree at most n, the atomic energy identity is

\[
Q(q)=\sum_{z\in S} w(z)|q(z)|^2.
\]

It is proved directly from the finite coefficient sums. Strictly positive
weights imply that every kernel polynomial vanishes at every support node.

If the reference support S has at most n nodes, its monic nodal polynomial
fits inside the available coefficient vector and lies in the matrix kernel.
In any positive competing representation, every node must therefore be a
root of that polynomial, hence lie in S. Lagrange weight recovery then
excludes dropping any node of S, since every reference weight is positive.
It also identifies the weights after the supports agree. No cardinality
bound on the competing support is assumed.

The raw theorem `representation_unique_of_card_le` proves this statement
for equal atomic matrices with one reference support of size at most n.
`representation_unique_singular` translates rank-sized reference data to
that bound. The final existence-and-uniqueness theorem combines it with
the previously proved general representation.

## Full-rank boundary

`full_rank_counterexample` proves an explicit failure of unconditional
support uniqueness. The one-by-one identity matrix is PSD, Toeplitz and
has rank one. It has both the positive one-atom representation supported
at +1 and the one supported at -1, each with weight one. Both nodes have
norm one, the supports differ, and both atom counts equal the matrix rank.

This is an exact formal counterexample, not a scan. No claim that **every**
full-rank matrix has multiple representations is proved in this follow-up.
No globally minimal-order search or empirical threshold is claimed.

## Build, audit and research scope

The exact target and DH analogue were recorded before implementation.
The result is shared finite algebra and holds for DH-derived matrices
under the same hypotheses. No arithmetic PSD estimate or active RH route
is added.

The module is imported by both the root and AxiomAudit. Seven explicit
axiom checks cover kernel vanishing, support recovery, fixed-support weights,
the stronger finite-competitor uniqueness, its singular-rank wrapper,
existence-and-uniqueness and the full-rank counterexample. Project audit
imports remain root imports. The default build passes (4,001 jobs), and
the axiom-clean script passes with 2,667 audited theorem reports, no sorry
and no custom axioms. These are local checks on dirty sources over
`d9c3c79`; no remote CI job is claimed.

```sh
lake build
bash scripts/verify_axiom_clean.sh
python3 experiments/prime_spectral/check_dh_research_gate.py
python3 research/prime_spectral/verification_2026_11_01_toeplitz_uniqueness/validate.py
```

The packet preserves all 1,940 earlier verification files and replays the
nine preceding packets against historical source snapshots. Fresh replay
passed with 5,559 modules and
22,222 compiled/metadata files bound and
unchanged. It uses Lean's own kernel, not an independently implemented verifier.
