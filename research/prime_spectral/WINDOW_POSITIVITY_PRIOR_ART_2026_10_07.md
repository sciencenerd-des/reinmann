# Dedicated prior-art check: compact-window Weil positivity

Checked 7 October 2026. Purpose: prevent a first-result or record claim
based on the assumption that the literature ends at C=2.

## Parameter dictionary

This repository uses C with logarithmic test-function support of total
width `log(C)`. In a paper using support `[-a,a]`, **C=exp(2a)**.
An additive autocorrelation radius s corresponds to **C=exp(s)**.
These are three different numerical measures. In particular, Zhu's
additive support 2.38 is not multiplicative cutoff C=2.38.
At a prime-power endpoint the L2 correlation at the full support width
is zero, so only q<C are active.

## Located sources and dispositions

| Source | Normalized range and content | Disposition |
|---|---|---|
| Yoshida, *On Hermitian forms attached to zeta functions*, AS Pure Math. 21 (1992), 281--325, [DOI](https://doi.org/10.2969/aspm/02110281) | Foundational local variational theory, small-support positivity and finite-codimension statements. | Original DOI/full text could not be retrieved in this pass. Consult before attributing an exact numerical endpoint to Yoshida. |
| Connes--Consani, *Weil positivity and trace formula, the archimedean place*, Selecta Math. 27 (2021), 77, [primary full text](https://arxiv.org/html/2006.13771), [author PDF](https://alainconnes.org/wp-content/uploads/Selecta.pdf) | Test support `[2^-1/2,2^1/2]`, hence C=2; no active primes. Theorem 1 and the surrounding discussion impose transform-vanishing conditions and compare with a Sonin trace. | Established published baseline; state its test class and constraints rather than identifying every version of the form without qualification. |
| Suzuki, *Weil's quadratic form via the screw function*, [arXiv:2606.09096](https://arxiv.org/html/2606.09096) | Local closed-form/operator framework. Theorem 1.4 gives positive simple even lowest eigenvalue for sufficiently small a, with a small-a asymptotic. | Relevant structural prior art; the checked theorem does not provide a larger explicit numerical endpoint. |
| Zhu, *Weil positivity in compact windows*, [arXiv:2608.24827v2](https://arxiv.org/html/2608.24827v2), revised 2 September 2026 | Claims `Q>=8.9e-18 ||f||^2` on `[-0.8,0.8]`, including arbitrary complex tests; **C=exp(1.6)≈4.9530**, prime powers 2,3,4. Section 7 retracts an earlier additive-support-2.38 claim because the comb inequality was used in the wrong direction. | The revision is not a withdrawal of the smaller theorem. Read the reduction and error budget; no complete independent replay performed here. Section 17 describes supplementary proof files, but no explicit archive URL was located in the checked HTML. |
| Liu, *Certified Weil Positivity Beyond the Unit Window*, [author's alphaXiv preprint](https://www.alphaxiv.org/abs/2609.weil-positivity-riemann-zeta-bounds), submitted 15 September 2026 | Claims bounds `2^-151` at a=1 and `2^-49162` at a=17/16; **C=exp(2)≈7.3891** and **C=exp(17/8)≈8.3729**. The latter includes 2,3,4,5,7,8. | Author abstract and linked release checked. This is a preprint, not journal acceptance; source materials are available, but mathematical proof and full certificate have not been independently audited here. The identifier is an alphaXiv custom identifier, not a numeric arXiv accession. |
| Liu, [frozen release v1.0-mcom-submission](https://github.com/luciferyu666/certified-weil-positivity/releases/tag/v1.0-mcom-submission) | Identifies commit `b6cd2183c1e79c6c27a34267812a7b2d73ed1b59` and complete original artifact ZIP separately from the automatic source archive. | Release exists and explicitly says external reproduction is incomplete. Do not substitute the smaller source archive for its full numerical package. |
| Kuberwastaken, [working note on truncated Weil functionals](https://github.com/Kuberwastaken/riemann/blob/main/experiments/weil_positivity/NOTE.md), dated 23 July 2026 | Reports ball-certified 14-dimensional families at a=0.60 containing 2 and 3, and a 22-dimensional example at a=0.62. | The note explicitly labels these **subspace** results and leaves the whole-window problem open. Relevant to numerical-method priority, not a full-window endpoint. |
| Tao Lin, *The Range of a Finite-Scale Weil Positivity Method*, DOI `10.5281/zenodo.21856509` | Search discovery describes a first-prime-window result at a=0.35 and a method-specific failure in the second window. | The primary DOI could not be retrieved. Discovery lead only; neither accepted as proof nor dismissed. A surrogate negative is not a negative of the genuine Weil form. |

The Connes--Consani--Moscovici Fourier-span form core and finite matrices
are already attributed in this repository. They do not turn finite
compression positivity into full-window positivity. The present new
certificate uses frequency truncation and an entire polynomial complement
bound, so its broad method overlaps the compact-window reduction in Zhu.
We make no method-priority claim.

## Search scope and conclusion

Queries covered "Connes Consani Weil positivity support interval 2 Zhu
2.38 retracted", "Weil quadratic form positivity bounded support log 2
primes 2 3", "Weil positivity certificate github Zhu", "finite-scale
Weil positivity", "Certified Weil Positivity Beyond the Unit Window",
and the exact constants/half-width of Liu's claim. Primary arXiv pages,
the Connes--Consani author text, Liu's author abstract and frozen release,
Suzuki's text, and the numerical working note were inspected.
Search summaries alone were not treated as proofs. One search result
misattributed Zhu's paper to Marcus Chuk; the primary arXiv record names
Xuefeng Zhu, which is the attribution used here.

**Decision:** the unrestricted assertion "the literature stops at C=2"
is not defensible as a description of public claims. The largest directly
located explicit full-window claim in this pass is C=exp(17/8), not a
verified world record. Distinguish published classical theorems, claimed
preprint extensions, independently replayed certificates, and global
novelty. No exhaustive novelty clearance is claimed.

Our separately generated theorem at C=exp(6/5) includes 2 and 3 but is
inside Zhu's and Liu's claimed ranges. Its defensible role is a compact,
reproducible local proof and a basis for extension. To claim a new endpoint,
one must audit the competing claims and then either exceed the applicable
range or explain a substantive new theorem/method with appropriate credit.
The user's excluded fixed-order minor scans, low-degree Jensen/Turan
numerics and de Bruijn--Newman bound attempts were not run.
