# Independent-review packet (pending external reviewer)

This packet is intentionally a request for scrutiny, not a certificate. No
independent human expert review has been obtained in this repository.

## Materials

1. `paper/rh_two_routes_paper.pdf` and its source
   `paper/rh_two_routes_paper.tex`.
2. `research/THEOREM_STATUS_LEDGER_2026_07_17.md`.
3. `Reinmann/GrassmannSyzygy.lean`, `Reinmann/FeketeAllOrders.lean`, and
   `Reinmann/ToeplitzFullPF.lean` for the Fekete closure.
4. `Reinmann/JensenProgram.lean`, `Reinmann/XiMomentKernel.lean`, and the
   effective/Jensen receptor modules for the Xi conventions.
5. The exact reproduction commands in `RELEASE_NOTES.md`.

## Questions for an analytic-number-theory reviewer

### Fekete/Toeplitz leg

- Does the Grassmann three-term identity have the stated index and sign
  conventions for the one-sided lower-triangular Toeplitz matrix?
- Does the order/dispersion induction really propagate strict contiguous
  initial-column minors to every finite Toeplitz minor, including zero gaps and
  repeated indices?
- Are the reversal and dominance steps valid over the stated ordered field,
  or do they require an omitted positivity, nonzero, or orientation lemma?
- Is the passage from full finite total positivity to the stated
  Laguerre--Pólya/Pólya--Jensen conclusion using exactly the required analytic
  hypotheses?

### Xi analytic leg

- Is `XiCoeff n = Xi^(2n)(0)/(2n)!` the correct normalization for the real
  function `Xi(t) = xi(1/2 + i t)` used by the Lean development?
- Do the moment-kernel representation, sign choice, and factorial rescaling
  agree with the cited Pólya and O'Sullivan formulas?
- Does the normalized order-three ratio/determinant certificate have the
  stated direction and positivity margin?
- Which published theorem, if any, supplies the all-degree/all-shift Xi
  Jensen-window input in the exact coefficient convention used here?
- Are the claims correctly limited to conditional reductions rather than a
  numerical or asymptotic proof of RH?

## Requested report format

Please return (i) a line-by-line list of any false statements or missing
hypotheses, (ii) corrected theorem statements where needed, (iii) a verdict on
whether the Fekete closure is publishable as a standalone formal lemma, and
(iv) a verdict on whether the Xi normalization is consistent with the cited
literature. The report should identify the reviewer and date and should be
kept separate from this repository until permission to publish it is given.

## Current internal status

The repository's own audit establishes only Lean kernel checking and the
absence of custom axioms. It is not independent expert validation. External
coordination is still required before an expert-review claim or DOI record
can truthfully include that status.
