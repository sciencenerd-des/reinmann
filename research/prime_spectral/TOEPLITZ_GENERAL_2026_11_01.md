# General finite Toeplitz atomic representation

`Reinmann.ToeplitzRepresentation.exists_atomic_representation` proves the
finite positive atomic representation for arbitrary rank, including zero
and full rank. Its only hypotheses are positive semidefiniteness and the
existing Toeplitz shift identity. No kernel vector, singularity hypothesis,
rank value, roots, weights or representation is supplied as an extra input.

This formalizes a known finite Carathéodory–Fejér theorem. It is shared
linear algebra, not a new arithmetic theorem or RH discriminator.
The corank-one checkpoint is commit `dd3d2ea`; its proof modules and sealed
evidence remain unchanged.

## Exact statement and conventions

For every n and every complex matrix T indexed by `Fin (n+1)`, assume
`T.PosSemidef` (which includes Hermitian symmetry) and
`T i.succ j.succ = T i.castSucc j.castSucc`. Then there exist a finite
set S of complex numbers and real weights w with

\[
|S|=\operatorname{rank}(T),\qquad |z|=1,\quad w(z)>0\quad(z\in S),
\]

\[
T_{ij}=\sum_{z\in S} w(z)\,\overline{z^i}\,z^j
\qquad(0\le i,j\le n).
\]

This is the existing `ToeplitzAtomic.HasAtomicRepresentation T T.rank`.
Finite-set membership gives distinct nodes. Zero rank uses an empty support;
full rank uses n+1 nodes. The n=0, one-by-one case is included.
The matrices are full Hermitian Toeplitz matrices, not Taylor-coefficient
Pólya-frequency matrices. Kernel polynomials retain ordinary ascending
coefficients and explicit support/degree bounds.

## Singular matrices: extension and induction

`ToeplitzExtension.extension_unique` proves the following finite extension
principle. If two PSD Toeplitz matrices agree on the leading block, and that
block has a short kernel polynomial q with q(0) nonzero, then the larger
matrices agree. Zero energy lifts the kernel relation from the leading
block. Toeplitz invariance already fixes every new last-row entry except
the far corner. The last-row kernel equation, with q(0) nonzero, fixes that
corner too; Hermitian symmetry fixes its conjugate.

`exists_atomic_representation_singular` proceeds by induction on matrix
size. The corank-one case is the earlier theorem. Otherwise the leading
block is singular, so induction gives positive atoms there. Their nodal
polynomial has nonzero constant term because all nodes have norm one.
The atomic matrix extends the block and is PSD/Toeplitz; extension uniqueness
identifies it with T. A rectangular factorization bounds its rank by the
number of atoms, while submatrix rank gives the reverse bound. Thus the
number is exactly rank(T), not an unspecified upper bound.

## Full rank: Schur-complement downdate

`ToeplitzDowndate.exists_constant_downdate` proves that for a positive definite
matrix T there is a real a>0 such that A=T-aJ is PSD and singular,
where J has every entry equal to one. Let B be the all-ones column and
D=Bᴴ T^{-1} B, a positive definite one-by-one matrix. The two
Schur-complement identities show A=T-B D^{-1} Bᴴ is PSD. D^{-1} is a positive real scalar, giving a.
The nonzero vector T^{-1}1 lies in the kernel, proving the rank drop.

The constant matrix preserves Toeplitz invariance. Apply the singular
representation to A, then add the positive atom at z=1, merging its weight
if it was already present. Rectangular rank bounds force exactly n+1
nodes in the full-rank case. This completes the arbitrary-rank theorem.

No square-root factorization, unitary extension, spectral diagonalization,
measure representation or arbitrary-rank representation is assumed in
these new proofs. The Schur-complement results are Mathlib theorems.
This representation module alone does not assert uniqueness. The subsequent
[uniqueness follow-up](TOEPLITZ_UNIQUENESS_2026_11_01.md) proves uniqueness of
singular finite positive data and fixed-support weight recovery, and gives
an explicit full-rank counterexample to unconditional support uniqueness.
The later [full-rank follow-up](TOEPLITZ_FULL_RANK_2026_11_01.md) proves
nonuniqueness for every full-rank case and the exact supported-data criterion.

## Research scope and validation

The target and DH analogue were recorded before implementation. The same
finite theorem holds for any DH-derived matrix satisfying the same PSD and
Toeplitz hypotheses. No such arithmetic PSD hypothesis is proved here.
The standing arithmetic routes remain uninstantiated and no active RH
strategy with a proved discriminator is claimed.

The three new modules are imported by both the root and AxiomAudit. Five
explicit axiom checks cover extension uniqueness, the atomic rank bound,
the downdate, singular representation and the general representation.
Project audit imports remain a subset of root imports. The default build
passes (4,000 jobs), and the axiom-clean script passes with 2,660 audited
theorem reports, no sorry and no custom axioms. These are local checks on
dirty sources over `dd3d2ea`; no remote CI job is claimed.

```sh
lake build
bash scripts/verify_axiom_clean.sh
python3 experiments/prime_spectral/check_dh_research_gate.py
python3 research/prime_spectral/verification_2026_11_01_toeplitz_general/validate.py
```

The new packet preserves all 1,911 earlier verification files and replays
all eight preceding packets against historical source snapshots. Fresh
replay passed with 5,558 modules and
22,220 compiled/metadata files bound and
unchanged. It uses Lean's own kernel, not an independently implemented verifier.
