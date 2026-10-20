# Target B closeout and the next finite-PF obligation

Proof-source checkpoint: `40d48033f14842c88486c257d6cfe39c496bbf66`.
Target B is proved and audited locally. Hosted CI run
[39425081613](https://github.com/sciencenerd-des/reinmann/actions/runs/39425081613)
is still running at preparation of this note. The requested README table and
research-objective status updates are prepared in `ci_closeout.patch` and must
not be applied until both jobs in that run conclude successfully.

## Target A is already formalized

The heading and final obligation list in the historical
`SPLIT_PAIR_MIXED_REMAINDER_2026_10_18.md` describe an earlier draft state.
Subsequent code supersedes that status; the old note is retained unchanged
because it belongs to an immutable verification checkpoint.

The actual dependency chain is:

1. `SplitPairMixedRows.repeated_pole_zero` cancels repeated pole rows, even
   when the other rows are row-dependent analytic errors.
2. `ordered_subset_product_bound`, `choice_weight_bound`, and
   `coefficient_determinant_bound` prove the ordered product and geometric
   determinant-error estimate, with an explicit constant independent of n.
3. `AnalyticSplitPair.normalized_determinant_error_tendsto` applies that estimate
   to actual coefficient errors and proves decay; it does not assume determinant
   decay as a new premise.
4. `entire_split_pair_of_boundary` obtains oscillation after constructing the
   patched analytic remainder and its coefficient identity.
5. `AnalyticToeplitzJacobi.entire_original_both_signs` transfers it to the actual
   original ordinary Taylor-coefficient minors.

Fresh source replays and a six-declaration dependency audit are recorded in
`verification_2026_10_20_sector/`. The selected zeros must still be simple, with
one isolated cross-boundary modulus tie and the stated strict gaps. This remains
standalone; it is not a replacement for the general PF-to-RH bridges and is not
an assertion of new mathematics.

## Selected next hypothesis: KatkovaSectorBridge 43

Target A's proposed next estimate is no longer open. The next genuine obligation
from the user's two candidates is `KatkovaSectorBridge 43`. Proving it would make
`XiRectangle.finitePF43` unconditional. No higher Xi rectangle is required.

The first completed step is `Reinmann.finitePF_of_tendsto` in
`Reinmann/FinitePFLimits.lean`: along a nontrivial filter, coefficientwise limits
of eventually PF-r sequences are PF-r. It proves convergence of every arbitrary
Toeplitz minor using determinant continuity and closedness of the nonnegative
reals. It includes rank zero and is not restricted to contiguous minors. The
filter's `NeBot` condition is essential. This module is checked as an explicit
Lake target, with its own axiom audit; no claim that it has been added to the
root audit is made.

The remaining tasks are substantive:

- Formalize the polynomial sector sufficiency theorem for real polynomials with
  positive constant term. The forbidden open sector is
  `|arg z| < m*pi/(m+1)`. Apply it with m=43; do not reproduce the printed PF44
  versus angle-43*pi/44 indexing inconsistency in Katkova's proof.
- Construct suitable real polynomial approximants to the folded Xi function:
  use conjugation-stable zero multisets, prove the genus-zero product and its
  coefficient convergence, and identify the ordinary coefficients with
  `XiMomentCoeff`. Multiplicities and ties must be allowed; Target A's simplicity
  hypotheses cannot be imported into this route.
- Apply the proved coefficientwise closure theorem, positive normalization and
  the existing angle bound, then supply the actual bridge to `finitePF43`.
  Do not rename any of these open facts as a newly assumed certificate.

This follows the polynomial/product/limit structure in
[Katkova, pp. 5–6, Theorem B and the proof of Theorem 1](https://arxiv.org/pdf/math/0505174).
Katkova attributes the sufficiency theorem to Schoenberg's *A Note on Multiply
Positive Sequences and the Descartes Rule of Signs*, Rendiconti di Palermo 4
(1955), 123–131, reference [29]; the similarly dated Annals paper is [28].
The original Schoenberg proof has not been obtained in this round, so this is
not a claim that its details or a complete formalization have been audited.

## Release decision and boundary

Keep the current Zenodo versions unchanged for this round. After CI, the new
GitHub theorem and its checksum-bound certificate can be cited as the finite
low-height result. A revised formalization preprint can consolidate this result
with the next completed sector milestone rather than publishing a new archive
for each transport lemma. No upload or publication is performed by this note.

The four-track RH obligations remain as before. In particular the Green paired
budget remains equivalent to RH. The additional finite-status matrix must not
mark action symmetry, relative budgets, all-order PF or RH as proved. Height
14.1 is fixed; forecasting, window scans and the stopped experimental programs
remain stopped.
