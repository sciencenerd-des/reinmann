# Finite Borel representing measures and their exact uniqueness boundary

The finite positive atomic representation now gives an actual finite positive
Borel measure on C. Uniqueness is proved among **all** finite positive Borel
measures concentrated on the unit circle, including competitors not assumed
atomic. For a PSD Toeplitz matrix T of size n+1:

\[
\exists!\,\mu\text{ representing }T
\quad\Longleftrightarrow\quad \operatorname{rank}(T)\le n.
\]

In full rank there are distinct representing measures. These are known shared
moment-problem facts; no mathematical novelty, arithmetic PSD estimate or RH
separator is claimed. The finite-data checkpoint is commit `dd0eb15`; its proof
modules and sealed evidence remain unchanged.

## Exact meaning of representation

`ToeplitzMeasure.Represents T mu` requires:

- mu is a positive countably additive Borel measure on C with finite total mass;
- norm(z)=1 for mu-almost every z;
- for all i,j in Fin(n+1),

\[
T_{ij}=\int_{\mathbb C}\overline{z^i}\,z^j\,d\mu(z).
\]

The definition imposes no finite support, atom-count or density hypothesis.
The ambient type includes the one-by-one case. Empty zero-by-zero matrices
are outside this statement. Original Hermitian two-sided Toeplitz matrices
and ordinary ascending polynomial coefficients are retained.

`atomicMeasure S w` is the sum of Dirac measures with masses
ENNReal.ofReal(w(z)). For positive supported weights these are exactly w(z),
with no normalization to a probability measure. The zero matrix uses the
zero measure. Finite sums of Dirac integrals reproduce the existing atomic
matrix entry convention. `exists_representing_measure` then applies the
previous arbitrary-rank atomic theorem, retaining a rank-sized atomic witness.

## Why non-atomic competitors are covered

`integral_pairing` proves, for polynomials p,q of degree at most n,

\[
\int \overline{p(z)}q(z)\,d\mu(z)
=\overline{\operatorname{coeff}(p)}^tT\operatorname{coeff}(q).
\]

Continuity and compactness of the unit circle establish integrability.
The proof expands both polynomials as finite sums and applies the entry
identities. It does not assume this integral pairing as a new hypothesis.

`eval_zero_ae_of_kernel` takes a polynomial q of degree at most n with
T coeff(q)=0. The integral of |q| squared is zero. Nonnegativity implies
q(z)=0 almost everywhere. If T has a reference representation on S with
|S|<=n, use the nodal polynomial product_(x in S)(X-x). It is a kernel
polynomial, and its zeros are precisely S. Thus every competing measure is
concentrated on S. This also covers empty S, where the nodal polynomial is 1.

Mathlib's `Measure.ae_mem_finset_iff` then identifies the measure with the
finite sum of its singleton masses. The earlier fixed-support Lagrange
recovery theorem determines those masses from the matrix entries. The result
`measure_eq_atomic_of_card_le` proves equality of measures. No finite-support
hypothesis was placed on the competitor.

For singular T, the existing rank-sized reference has at most n atoms, giving
`exists_unique_representing_measure_singular`. In full rank, the earlier
pointwise nonuniqueness theorem gives distinct positive supports. Evaluation
on singleton sets proves their measures differ. Combining these results gives
`unique_representing_measure_iff_singular` without vacuous uniqueness.

## Integration and scope

Both new modules are imported by `Reinmann.lean` and `Reinmann/AxiomAudit.lean`.
Nine explicit axiom checks cover the measure bridge, existence, polynomial
pairing, kernel vanishing, support confinement, mass recovery, singular
uniqueness, full-rank nonuniqueness and exact criterion. Project audit imports
remain a subset of the root imports. The default build passes (4,005 jobs),
and axiom-clean passes with 2,680 audited theorem reports. The nine probes
use only propext, Classical.choice and Quot.sound. These are local checks on
dirty sources over `dd0eb15`, with no remote CI receipt.

The exact target and DH analogue were recorded before implementation. The
same result holds for DH-derived matrices under the identical premises.
It supplies no arithmetic PSD bound, actual arithmetic probe, RH discriminator,
infinite-sequence representation, or continuous-operator theorem. The stopped
arithmetic routes and scans remain stopped.

```sh
lake build
bash scripts/verify_axiom_clean.sh
python3 experiments/prime_spectral/check_dh_research_gate.py
python3 research/prime_spectral/verification_2026_11_01_toeplitz_measure/validate.py
```

The evidence packet preserves 2,003 earlier verification files and replays
eleven preceding packets against their historical sources. Fresh replay uses
Lean's own kernel, not an independently implemented verifier. It passes
for 5,563 modules, binding 22,230 compiled and metadata files; all bound
inputs remain unchanged.
