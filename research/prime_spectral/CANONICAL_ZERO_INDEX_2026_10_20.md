# Canonical folded-Xi zeros: multiplicities, conjugation, and strip correspondence

The actual folded-Xi application no longer asks the caller to supply a
conjugation involution or a correspondence with strip zeros. These data are
constructed from the function's analytic orders. Two substantial analytic
inputs remain: inverse-zero summability and the normalized canonical-product
identity. Neither is proved in this round.

## Indexing all zeros with their actual multiplicities

`CanonicalZeroIndex` works for an entire function f with f(0) nonzero. Its index
is the subtype of pairs (z, k) satisfying

    k < analyticOrderNatAt f z.

`order_ne_top` uses the analytic identity theorem on the connected complex
plane to rule out infinite order everywhere. Thus conversion of analytic order
from the extended naturals does not silently discard an infinite-order zero.
`exists_value_iff` proves that the values of this index are exactly the zeros.
The explicit equivalence `fiberEquiv` identifies the fiber above z with
`Fin (analyticOrderNatAt f z)`, and `fiber_card` proves the exact cardinality.
The construction assumes neither simplicity nor an enumeration of the zeros.

For a real-type entire function, conjugation commutes with every iterated
derivative. The derivative characterization of analytic order then proves
equality of orders at z and conj(z). The index involution is simply

    (z, k) ↦ (conj(z), k).

It preserves the multiplicity label and squares to the identity. A real zero
is fixed at each of its labels; a multiple non-real zero is paired with the
same number of labels at its conjugate. No strict modulus gaps are used.

## Actual Xi zeros, including the endpoints

`XiZeroCorrespondence.xi_zero_iff` proves the exact equivalence

    xiCompleted s = 0 ↔ IsCriticalStripZero s.

On Re(s) ≥ 1 it uses Mathlib's zeta nonvanishing and the actual completed-Xi
product formula, treating s=1 separately with its value 1/2. The functional
equation gives nonvanishing on Re(s) ≤ 0, including s=0. Inside the open strip,
the nonvanishing gamma factor relates completed zeta to zeta in both
directions. The pole-subtracted entire function is never substituted as the
zero-set target.

`folded_zero_iff` consequently proves that a zero z of folded Xi is exactly a
square `(s - 1/2)^2` for some critical-strip zeta zero s. The chosen lift
`1/2 + sqrt(z)` is proved to lie in that strip. No continuity or analyticity of
the square-root branch is needed: only its pointwise square identity is used.
These statements are unconditional and make no RH or simplicity assumption.

## Reduced conditional bridge

`XiCanonicalProductSector` specializes the index to actual `foldedXi`, using
the already proved positive centre and conjugation symmetry. It supplies its
nonzero values, multiplicities, conjugation involution and strip lift to the
previous sector assembly. The theorem
`katkovaSectorBridge_of_canonical_product` requires only

    Summable (fun i : Index => ‖(value i)⁻¹‖)

and, for every complex z,

    foldedXi z = (XiMomentCoeff 0 : ℂ) *
      ∏' i : Index, (1 - (value i)⁻¹ * z).

For every positive rank m these two inputs yield the named
`KatkovaSectorBridge m`. The result is still conditional: it does not establish
either analytic input, and therefore does not establish unconditional
`finitePF43`. Finite multiplicity bookkeeping is not a canonical-product
factorization theorem.

## Next analytic obligation

A source search in this checkout found the analytic-order and Jensen-formula
APIs, but no ready-to-use Hadamard factorization theorem. This is a local API
inventory, not a literature novelty claim. A classical completion would need
actual growth bounds for folded Xi, zero-counting estimates strong enough for
inverse-zero summability, and a factorization argument proving the quotient by
the zero product is constant with the stated normalization. The new index
allows those statements to be formulated using actual zeros with their
multiplicities rather than additional abstract indexing hypotheses.

The earlier real-approximant and polynomial-sector checkpoints remain useful
and unchanged. Target A stays standalone; there is no PF-to-RH rewiring under
genericity hypotheses. No height increase, unbounded-rank PF, RH, or Green-form
budget is claimed. Published versions are unchanged.

## Verification

The 24 public theorems in the three new modules have a separate standard-axiom
audit. Checks include fresh source elaboration of every new module, the
explicit `Reinmann.XiCanonicalProductSector` target, the default build and the
unchanged 1619-declaration root guard. The new modules remain outside the root
import and are not counted in that root audit.

Evidence is in `verification_2026_10_20_canonical_zero_index/`. Its checker
replays the immutable real-approximant checkpoint and all earlier parents,
then checks these sources, declaration selection, command receipts and
checksums. Existing manifests are not rewritten. Large build logs are stored
losslessly compressed, with raw-output hashes and byte counts retained.

Rebuild with `lake build Reinmann.XiCanonicalProductSector`; replay saved
evidence with `python3 experiments/prime_spectral/verify_canonical_zero_index.py`.
Receipt replay is not a fresh build or hosted-CI claim. At preparation,
proof-source CI run 39425081613 still had its rectangle job running; the default
job had passed. The CI-gated Target B closeout remains pending, and that older
run does not cover these new modules.
