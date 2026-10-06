# Updated literature review: Xi coefficients, total positivity, and formal RH reductions

**Search date:** 2026-08-11  
**Manuscript:** `paper/rh_two_routes_paper.tex`  
**Scope:** literature that can change the status or positioning of the paper's
Toeplitz/Pólya-frequency route, Jensen route, heat-flow route, numerical
methodology, or Lean contribution.

## Review method

The search prioritized original journal pages, arXiv records, and active
formalization repositories. Search clusters combined “Riemann Xi” with
“Toeplitz minors”, “total positivity”, “Pólya frequency”, “Jensen
hyperbolicity”, “de Bruijn--Newman kernel”, and “Lean formalization”. Claims
were retained only when the source stated a theorem, a certified computation,
or an explicit experimental limitation relevant to a named interface in the
repository. Survey pages and search-result summaries were used only to locate
primary sources.

The evidence labels below are deliberate:

- **established:** peer-reviewed theorem or classical result;
- **preprint theorem:** a theorem claimed in a public preprint, not independently
  rechecked in this repository;
- **certified computation:** a finite computer-assisted result with described
  interval/error control;
- **experiment/conjecture:** bounded numerics or an explicitly conjectural bridge.

## Findings that materially change the paper

### 1. A new explicit all-order tail wedge closely matches Route A

Michałowski's July 2026 preprint proves, in its coefficient normalization,
strict positivity of every consecutive Xi-coefficient Toeplitz minor

\[
  D_{r,k}=\det[a_{k+j-i}]_{i,j=0}^{r-1}>0
  \quad\text{for }r\ge2,\ k\ge10^{18}r^3.
\]

The source describes a certified saddle-point estimate, an exact
\(q\)-Pascal algebra, and directed-rounding Arb certificates with a regression
suite. It also states the correct limitation: the complementary region remains
open and contains the RH difficulty. **Evidence label: preprint theorem with
computer-assisted certificates.**

This is the closest known result to the manuscript's “uniform all-order
remainder scheme.” After transposition, its matrix matches the repository's
consecutive block. In the preprint's normalization
\(G(z)=\xi(1/2+\sqrt z/2)/8\), one has
\(a_n=\mu_n/(8\,4^n)\), so an order-\(r\) minor at shift \(k\) differs by
the positive factor \(8^{-r}4^{-rk}\). Thus its \(D_{r,k}\) is the same sign
problem as the repository's \(D_r(k)\). If the preprint and ancillary
certificates survive independent review, it supplies an explicit tail cutoff
\(N(r)=10^{18}r^3\); it does not supply the prefixes below that cutoff, does not
instantiate the Lean interface by itself, and does not prove RH.

Primary source: [Michałowski, *An explicit uniform cubic wedge for consecutive
Toeplitz minors of the Riemann xi coefficients*, arXiv:2607.16795
(2026)](https://arxiv.org/abs/2607.16795).

### 2. Katkova already established the Xi-specific multiple-positivity context

Katkova's work treats the Xi generating function through Schoenberg's
multiply-positive/Pólya-frequency classes and includes the strict
consecutive-minor criterion used by later work. **Evidence label: established.**
The manuscript should cite this source directly and position its contribution
as a machine-checked, Toeplitz-specialized proof and receptor architecture, not
as discovery of the classical criterion itself.

Primary source: [Katkova, *Multiple positivity and the Riemann zeta-function*,
Comput. Methods Funct. Theory 7 (2007), 13--31](https://arxiv.org/abs/math/0505174),
doi:10.1007/BF03321628.

### 3. Jensen asymptotics still leave the information-bearing region open

The effective Xi-specific Jensen theorem proves large-shift hyperbolicity and
relates bounded-height information about derivatives of Xi to Jensen
polynomials. It explicitly cautions that detecting hypothetical violating zeros
is inefficient without all degrees and shifts. Farmer's later analysis makes
the same epistemic point more sharply: Hermite universality is interesting but
does not by itself provide evidence for RH. **Evidence label: established.**

Primary sources:

- [Griffin, Ono, Rolen, Thorner, Tripp, and Wagner, *Jensen Polynomials for the
  Riemann Xi Function*, arXiv:1910.01227](https://arxiv.org/abs/1910.01227).
- [Farmer, *Jensen polynomials are not a plausible route to proving the Riemann
  Hypothesis*, Adv. Math. 411 (2022), 108781](https://doi.org/10.1016/j.aim.2022.108781).

Planat's May 2026 article proposes a finite-strip description and a later July
article reports parity-dependent onset numerics, Hankel positivity through
order 30, Padé recovery of 14 zero ordinates, and a conjectural Stieltjes
bridge. The later paper explicitly labels these as experiments and
conjectures. **Evidence label: mixed theorem/experiment/conjecture.** These
papers motivate additional falsification tests, but their conjectural bridges
must not be promoted to external inputs or claimed as progress toward RH.

Primary sources:

- [Planat, *Asymptotic Hyperbolicity of Jensen Polynomials and the Finite-Strip
  Obstruction to the Riemann Hypothesis*, Mathematics 14 (2026),
  1884](https://doi.org/10.3390/math14111884).
- [Planat, *Parity Bifurcation, PIII(D6) Topology, and a Stieltjes Framework to
  Jensen Polynomial Hyperbolicity*, Mathematics 14 (2026),
  2240](https://doi.org/10.3390/math14132240).

### 4. Continuous-kernel and discrete-coefficient total positivity remain distinct

Michałowski's February 2026 preprint gives a certified negative \(5\times5\)
Toeplitz minor for the continuous de Bruijn--Newman kernel at one explicit
configuration. The paper carefully says that global PF\(_4\) remains open and
that the result is about the continuous translation kernel. **Evidence label:
preprint theorem with certified computation.** It blocks a continuous
PF\(_\infty\) shortcut but does not contradict the July coefficient-tail
result or the repository's discrete Xi-coefficient scans.

Primary source: [Michałowski, *On the Pólya Frequency Order of the de
Bruijn--Newman Kernel*, arXiv:2602.20313](https://arxiv.org/abs/2602.20313).

### 5. Heat flow still stops exactly at the RH-equivalent inequality

Rodgers and Tao prove \(\Lambda\ge0\), while RH is equivalent to
\(\Lambda\le0\). **Evidence label: established.** The manuscript's proposed
`HeatFlowRigidity` remains a named open target; numerical heat-flow behavior
cannot fill it.

Primary source: [Rodgers and Tao, *The de Bruijn--Newman constant is
non-negative*, Forum Math. Pi 8 (2020), e6](https://doi.org/10.1017/fmp.2020.6).

### 6. Formalization novelty must be comparative and theorem-level

Loeffler and Stoll document the Mathlib formalization of zeta and Dirichlet
L-functions, including the formal statement of RH and the analytic foundations
on which this repository builds. **Evidence label: established formalization.**
The present manuscript should claim its particular checked artifacts---the
Grassmann identity, gap-shrinking Toeplitz closure, exact conditional
receptors, axiom audit, and falsification tests---rather than priority for
formalizing RH or its statement.

Primary source: [Loeffler and Stoll, *Formalizing zeta and L-functions in
Lean*, Annals of Formalized Mathematics 1 (2025),
43--56](https://doi.org/10.46298/afm.15328).

## Consequences for the current manuscript

1. Replace the claim that a uniform tail theorem is wholly missing with a
   precise account of arXiv:2607.16795: it supplies a claimed explicit tail
   wedge, while the complementary prefixes and Lean transport remain open.
2. Add Katkova 2007 to the PF related work and narrow novelty language to the
   formalization and exact interfaces.
3. Keep Farmer's warning central to Route B and add Planat's July experimental
   follow-up only as a source of hypotheses, not as a theorem consumed by the
   proof chain.
4. Report the Python/JavaScript/TypeScript replication as bounded
   falsification evidence with an input hash and exact uncertainty model.
5. Correct the scientific-notation half-ULP bug in the historical Python scan
   before quoting row-48 counts. The old inconclusive counts are not valid
   under the stated “last displayed decimal place” model.
6. Preserve the four-way status ledger: Lean-checked theorem, external
   classical theorem, externally claimed computer-assisted theorem, and open
   RH-strength target.

## Remaining review risks

- The cubic-wedge paper is recent and unrefereed. Its ancillary certificates
  were not independently executed during this review, so the manuscript must
  say “the preprint proves/claims,” not silently absorb the result as checked
  local mathematics.
- Normalization transport is sign-preserving but should be written out before
  a future Lean theorem consumes the external result.
- The Planat Stieltjes bridge is conjectural, and finite Hankel/Padé numerics do
  not imply the all-order statement.
- The repository still lacks independent expert review of the analytic
  coefficient normalization and the claimed novelty of the formalized Fekete
  proof.
