# Readiness decision for a paper on the Weil trace/prime-entry results

Checked 7 October 2026 against commit 26bf3da and the continuation recorded
below. Decision: **not yet cleared as a novel research paper**. Continue
the mathematics and validation. This is not a finding that the proposed
trace theorem is false. It is a distinction between a promising application,
established ingredients, numerical verification, and a defensible original
contribution.

## 1. What can and cannot be the contribution

| Candidate headline | Readiness finding |
|---|---|
| Positivity including primes 2 and 3 | Not a first-result claim. Existing public preprints claim larger windows. Their claims are not accepted here merely because they are online. |
| A certified simple, even ground state | Already a headline of Zhu's Theorem 6.2 at another fixed scale. The two threshold-specific gap enclosures are useful instantiations. |
| The logarithmic boundary scale or renewal Green factorization | Established potential theory. It must be cited, not advertised as our discovery. |
| Lowest-eigenvalue continuity and spectral projection convergence | Suzuki and standard compact-resolvent perturbation theory are prior art. |
| Actual normalized Weil endpoint traces, their uniform forcing error, and the \(\delta/\log(1/\delta)\) newly active prime coefficient | Candidate application. No exact matching theorem was located in this targeted check, but that alone does not settle priority or correctness. |
| Leading prime entry on a multiple limiting ground eigenspace | New proposed continuation in this repository, recorded below; not yet a cleared novelty claim. |

A new endpoint record is not necessary for a worthwhile original paper.
Conversely, Lean scalar lemmas, a different implementation, or a new pair
of local constants do not by themselves establish a new mathematical idea.
The possible paper should be about the actual trace-to-activation theorem,
with the certificates as applications.

## 2. Primary-source comparisons

1. [Zhu, arXiv:2608.24827v2](https://arxiv.org/html/2608.24827v2),
   abstract and Sections 6–7. The current revision retains its smaller
   compact-window theorem and certifies a simple even ground state.
   The additive-support-2.38 claim is explicitly retracted; the whole
   revised paper is not withdrawn. Its total support length 1.6 means
   multiplicative \(C=e^{1.6}\), not \(C=1.6\).
   This review did not replay its supplementary certificate.

2. [Suzuki, arXiv:2606.09096v2](https://arxiv.org/html/2606.09096v2),
   Theorems 1.3–1.4 and Section 4.4. Continuity and small-support
   simplicity are already structural theory. Our common-domain
   resolvent argument is not a new RH equivalence.

3. [Kim et al., arXiv:2607.24830v3](https://arxiv.org/html/2607.24830),
   Sections 5.2–5.4. The authors report unreliable fitted boundary
   exponents and leave analytic Wiener–Hopf boundary analysis open.
   This motivates an analytic trace calculation, but a stated open
   problem in one paper does not establish global novelty.

4. [Grzywny–Ryznar, arXiv:1107.0745](https://arxiv.org/pdf/1107.0745),
   Proposition 3.2 and Lemma 4.3, and their fluctuation-theory references.
   Renewal monotonicity and the half-line Green factorization are
   established inputs. Their exponent differs by a factor two from
   our comparison operator; the \(\sqrt2\) renewal normalization is
   retained.

5. [Kuberwastaken, CONTINUATION, Section 5](https://raw.githubusercontent.com/Kuberwastaken/riemann/main/CONTINUATION.md).
   The author-maintained working note already factors prime entry
   through shrinking endpoint layers. It is prior disclosure of that
   geometry, not a reviewed proof of our normalized trace coefficient.
   Schur continuation and its margin obstruction also appear there.

6. [Dusson–Sigal–Stamm, arXiv:2105.02058](https://arxiv.org/abs/2105.02058).
   The Feshbach–Schur method and its eigenvalue/error estimates are
   established perturbation theory. The proposed continuation below
   makes no method-priority claim.

7. [AMRAL, RH-W-11](https://amral.evemisslab.com/en/riemann/autonomous/p/w11-v0.1/).
   This primary project page describes activation exponents for
   prescribed B-spline test families and explicitly distinguishes them
   from infinite-dimensional positivity. This is an additional reason
   not to claim discovery of the general idea that boundary regularity
   controls prime activation. Its artifact package was not audited here;
   the checked page does not establish our actual-eigenfunction trace law.

8. [Liu, author preprint](https://www.alphaxiv.org/abs/2609.weil-positivity-riemann-zeta-bounds)
   and [frozen source README](https://raw.githubusercontent.com/luciferyu666/certified-weil-positivity/b6cd2183c1e79c6c27a34267812a7b2d73ed1b59/README.md).
   A competing larger-window claim remains relevant to endpoint
   positioning. The full analytic proof and original numerical package
   have not been audited here. It is neither accepted nor silently
   dismissed. See the earlier dedicated window prior-art report.

Queries combined Weil positivity/quadratic form with renewal, endpoint
trace, prime activation, boundary, threshold, degenerate cluster and
rank two. Broader searches used logarithmic Schrödinger operators,
geometric stable processes, boundary Martin theory, and Feshbach–Schur
perturbation theory. Primary texts/pages above were opened; search-only
leads and unrelated nonlinear logarithmic Schrödinger equations were
not treated as evidence for the theorem. This was a targeted review,
not an exhaustive citation-network or monograph search.

## 3. Proof and numerical audit

The trace proof has substantive written steps: signed forcing, the
zero-resolvent Green identification, localization of the full Weil
operator, uniform boundedness without a positive Weil semigroup,
normalized renewal asymptotics, and convergence of both minimizing
states. Those steps are not replaced by the scalar Lean audit.
No decisive counterexample to them was found in this review.

The continuation now supplies
[an explicit form-core proof](WEIL_LOG_FORM_CORE_2026_10_07.md), by
support contraction and mollification in the logarithmic Fourier norm.
It distinguishes form density from an operator-core assertion.
The analytic notes still need consolidation with the test-space kernel
identity and all renewal/trace dependencies checked together.
The closest potential-theory and spectral results
need comparison beyond their headlines before claiming an original
transfer theorem. Expert review would be valuable; lack of prior peer
review is not by itself a mathematical defect or a requirement that
every analytic argument be formalized in Lean.

The previous numerical verifiers independently integrated only four
low entries per certificate. This continuation reassembles **all 16,000
matrix entries**, including both parity sectors, with different
Gauss orders and 512-bit arithmetic:

| Threshold | Entries compared | Original / alternate order | Result |
|---|---:|---:|---|
| 2 | 3,200 | 64 / 80 | All comparisons and full-gap bound pass |
| 3 | 12,800 | 80 / 96 | All comparisons and full-gap bound pass |

Every entry difference is below the sum of the two rigorous quadrature
operator-error allowances. Repeating the full-complement min–max
calculation preserves the weakened gaps \(0.00857\) and \(6\cdot10^{-9}\).
The output is retained in
[all_entry_reassembly.json](verification_2026_10_07_cluster_readiness/all_entry_reassembly.json).
This uses the same generator, Arb library, and analytic bound formulas;
it is **not an independent implementation or mathematical review**.
No positivity-minor scan or new support endpoint was introduced.

Tight actual trace intervals and trace nonvanishing remain unproved.
They would strengthen a numerical application. They are not logically
necessary to state a valid asymptotic theorem whose coefficient may be
zero, and should not be invented as a prerequisite for all publication.
No claimed positive-window increase is made in this continuation.

## 4. Work continued instead of drafting a paper

[The degenerate-cluster note](DEGENERATE_CLUSTER_PRIME_ENTRY_2026_10_07.md)
proposes the more general reduction

\[
 \lambda_j(A_\delta^1)=
 \lambda_j(H_\delta+W_\delta\mathcal B)+o(W_\delta),
 \qquad
 \mathcal B_{ij}=-w_q(\overline{\tau_{-,i}}\tau_{+,j}
                   +\overline{\tau_{+,i}}\tau_{-,j}).
\]

Here \(H_\delta\) retains the entire actual ground-cluster splitting.
The boundary matrix has rank at most two. In a parity basis its even
part is negative rank at most one and its odd part positive rank at
most one.

The main additional estimate is that the full Schur correction is
\(o(W_\delta)\), rather than merely \(O(W_\delta)\). The proposed
proof combines endpoint localization with the compact complementary
resolvent. A fixed inverse-gap estimate alone is insufficient.
This removes the simple-ground-state restriction from the matrix
reduction, without falsely selecting a common individual vector or
dropping a larger background splitting.

Four scalar Lean lemmas expose these two error inputs as named
hypotheses. Their audit does not certify the operator analysis.
The candidate matrix theorem needs a focused prior-art and proof audit
of its own before it becomes the central claim of a manuscript.

## 5. Concrete next readiness gates

- Consolidate and adversarially check the operator-domain, renewal and
  trace arguments as one exact theorem. A mathematics paper need not
  be fully Lean-formalized, but named assumptions cannot be counted
  as proved analytic discoveries.
- Compare the normalized Weil trace and cluster activation statements
  against the complete closest potential-theory and spectral sources,
  including their cited predecessors. State a narrow original
  application rather than priority for renewal or Schur methods.
- For a quantitative application, bound the localized complementary
  resolvent factor and validate a boundary-adapted actual profile.
  Current coarse trace intervals cannot support a nonzero coefficient
  or a useful numerical neighborhood.
- If an endpoint record is to be a headline, first audit the competing
  full-window claims and source-to-matrix packages. The local threshold
  work alone does not surpass them.

Once the theorem and contribution are clear, a focused math.NT/math.SP
manuscript on normalized Weil traces and prime-entry matrices may be
appropriate. The present decision is to continue research, not to
package an unverified novelty claim as a new paper.
