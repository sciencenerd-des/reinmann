# Publication review and literature map — 6 October 2026

**Recommendation: revise before publication.** The manuscript has a useful,
carefully delimited result: an infinite omitted-index forcing estimate for
a finite-rank ground vector, uniform on a specified support cell. Its main
scope statement correctly excludes an RH proof and an all-rank ground-state
convergence theorem. However, the displayed certified enclosures contain
errors, the bibliography misses directly relevant work, and the public
replay package is not identified sufficiently for an external reader.

Reviewed artifact: [the 16-page PDF](../../paper/weil_infinite_rank_tail_paper.pdf)
and [its source](../../paper/weil_infinite_rank_tail_paper.tex). The manuscript
was preserved. PDF SHA-256:
`7f86e72fde9604856615ab513f4fb5577d9ff38ccce8d23243e1015052f17696`;
source SHA-256:
`1a019df59999f27df7697619e25ec32e24d8cd540c7ed03476f0586e16cb5f3a`.
All pages were rendered and inspected as a contact sheet; the certificate
table was also inspected at page resolution. No clipping or unreadable
overlap was apparent. This is a research review, not journal acceptance or
an independent formal proof of the complete manuscript.

## 1. Corrections required in the certified numerical presentation

Table 2, page 13, says each contribution is an outward upper bound and each
moment interval encloses the exact value throughout its subcell. Four
intervals and four upper bounds do not enclose the corresponding saved
certificate quantities. The comparisons below are exact rational comparisons,
not conclusions inferred from displayed floating-point digits.

| Table entry | Printed value | Saved certificate, approximately | Safe replacement at comparable precision |
|---|---|---|---|
| lower endpoint of `m1` | `−6.317e−8` | `−6.317142498164785e−8` | `−6.318e−8` |
| upper endpoint of `m3` | `−7.419e−2` | `−7.418763055284217e−2` | `−7.418e−2` |
| upper endpoint of `nu0` | `−4.750e−10` | `−4.749654098300769e−10` | `−4.749e−10` |
| lower endpoint of `nu2` | `−1.5124e−3` | `−1.5124328857041291e−3` | `−1.5125e−3` |
| boundary contribution | `2.465e−12` | `2.4651011474156716e−12` | `2.466e−12` |
| `m2` contribution | `1.252e−12` | `1.2524546188635837e−12` | `1.253e−12` |
| `nu0` contribution | `1.219e−12` | `1.219100423975696e−12` | `1.220e−12` |
| total | `9.4900e−12` | `9.490046557499695e−12` | `9.4901e−12` |

The other displayed Table 2 intervals and contribution bounds passed the
comparison, including the grouped higher moments. Preserve the original
certificate inputs when reproducing the total: the coarsened intervals in
the printed table are explanatory enclosures, not necessarily the inputs
from which its contribution bounds are recomputed. If the displayed wider
intervals become the computational inputs, recompute every contribution.

In the proof of Corollary 8.1, page 14 / source line 968, the inequality
`(9.49005e−12)^2 < 9.0061e−23` is false: the square is
`9.00610490025e−23`. Replace the first number by the theorem's
`9.4900466e−12`, whose square is strictly below `9.0061e−23`.
The final coarser conclusion `<9.007e−23` survives this correction.
Both numerical assertions have now been checked by Lean's kernel in
`rounded_forcing_energy_bound` and
`coarse_forcing_rounding_exceeds_energy_bound`.

Table 1, page 9, calls the values of `P` and `E` outward enclosures but
displays decimals followed by ellipses. These are approximations, not
interval enclosures. Supply actual lower/upper endpoints or change those
two rows' labels to approximate values. The explicit strict upper bounds
in the remaining rows have a different, valid meaning.

Reproduce the presentation audit with:

```sh
python3 paper/audit_weil_tail_rounding.py
```

The [saved audit](weil_paper_rounding_review_2026_10_06.json) pins the
manuscript and certificate hashes and distinguishes presentation comparison
from mathematical certification. It refuses a changed transcription.

## 2. Mathematical and proof-scope review

The paired omitted-mode identity has the correct orthonormal even-basis
normalization: the full coefficients are `c_{±i}=u_i/sqrt(2)` and the
omitted even component is `sqrt(2)(Ac)_n`. The leading term contains the
signed boundary sum, not the sum of absolute coordinates. The arbitrary
geometric expansion includes order zero correctly. Its two remainders have
powers `n^(−2R−3)` and `n^(−2R−2)` after denominator majorization. These
algebraic ingredients are now formalized, as specified in Section 5 below.

The integral-test and Minkowski argument is an actual infinite-index
argument. It does not require computing matrices up to the coercivity
threshold. The rank-eight certificate supplies the finite signed moments;
it does not certify the infinite ground eigenvector. Likewise, the
far-block Schur energy estimate controls only the far block, not the
intermediate inverse or the low spectral gap. Keep this distinction in
the abstract, theorem statements, conclusion, and any announcement.

Two proof clarifications are advisable:

1. Section 3.1 / source line 356 invokes Tonelli for a complex integrand.
   Use absolute Fubini instead. For `Re z>0`,
   `sum_k integral_0^infinity |t exp(−(k+z)t)| dt =
   integral_0^infinity t exp(−Re(z)t)/(1−exp(−t)) dt < infinity`.
   The integrand is bounded near zero and decays exponentially at infinity.
   Tonelli justifies this nonnegative absolute-value calculation; Fubini
   then justifies the complex interchange.
2. The commutator remark in Section 2.2 should identify its codomain and
   domain. As an entrywise identity, or for every finite compression,
   `[A,J]=e b^T−b e^T` is correct. An identity of Hilbert-space operators
   needs additional domain conditions: `e` is not in `ell^2`, and `JAc`
   need not be in `ell^2` for an arbitrary finitely supported `c`. Do not
   infer a bounded operator commutator from the matrix identity.

The Fourier form-core citation is **verified, not a defect**:
[CCM, Proposition 3.4](https://arxiv.org/html/2511.22755v1#S3.SS1)
states precisely the Fourier-span core property. When extending a
compressed far-block inequality, explicitly say the closure of that
compressed form, or explain why projecting a core approximation to the
far subspace preserves form convergence. Finite compressions used in the
paper do not require that additional extension.

The digamma integral actually displayed is
[DLMF 5.9.12](https://dlmf.nist.gov/5.9.E12), whereas the present citation
lists 5.9.16. Add 5.9.12; 5.9.16 is a related but different representation.
The series citation 5.7.6 is appropriate.

## 3. Literature review and attribution

The following map separates established results from recent unrefereed
claims. Discovery dates and version numbers matter here; a search hit or
preprint abstract does not constitute independent verification.

| Source | Relevance and required treatment |
|---|---|
| [Bombieri, *Remarks on Weil's quadratic functional … I* (2000)](https://www.bdim.eu/item?id=RLIN_2000_9_11_3_183_0) | Classical variational and explicit-formula context; already cited. Finite positivity alone does not give universal Weil positivity. |
| [Connes–Consani, *Spectral triples and zeta-cycles*, Enseign. Math. 69 (2023), 93–148](https://doi.org/10.4171/LEM/1049) | Earlier prolate spectral construction. Add when discussing the proposed prolate-wave candidate and spectral convergence. |
| [Connes–Consani–Moscovici, *Zeta zeros and prolate wave operators*, Ann. Funct. Anal. 15 (2024), 87](https://doi.org/10.1007/s43034-024-00388-z) | Semilocal prolate and closed-form background. Add as a direct predecessor. [Author's full text](https://alainconnes.org/wp-content/uploads/Zeta-zeros-and-prolateproofs-final-2024.pdf). |
| [Connes–Consani–Moscovici, *Zeta spectral triples*](https://ems.press/books/elm/323/6477) | Now published as a 2026 EMS chapter, DOI `10.4171/ELM/37/3`; retain the [2025 arXiv version](https://arxiv.org/abs/2511.22755) for proposition numbering. Its core and displacement formulas are prior results. Xi convergence is an identified missing step. |
| [Connes–van Suijlekom, *Quadratic Forms, Real Zeros and Echoes of the Spectral Action* (2025)](https://arxiv.org/abs/2511.23257) | Published in Comm. Math. Phys. 406, 312, DOI `10.1007/s00220-025-05493-1`. Proposition 4.1 gives the divided-difference matrix structure. Theorem 6.1 gives real Fourier zeros under its precise essential-selfadjointness, simple isolated minimum, and parity hypotheses. Add this direct attribution; it supplies no identification with Xi. |
| [Slepian–Pollak, *Prolate Spheroidal Wave Functions, Fourier Analysis and Uncertainty — I* (1961)](https://doi.org/10.1002/j.1538-7305.1961.tb03976.x) | Established concentration theory. A concentration optimizer is not thereby a Weil ground state; retain the separate residual and spectral-gap gate. |
| [Bañuelos–Kwaśnicki, *On the l^p-norm of the discrete Hilbert transform*](https://arxiv.org/abs/1709.07427) | Modern primary reference for discrete Hilbert norms. Their `1/pi` normalization must be converted to the manuscript's kernel `1/(m−n)`; the `ell^2` norm here is `pi`. HLP already provides classical context. |
| [Johansson, *Arb: Efficient Arbitrary-Precision Midpoint-Radius Interval Arithmetic*](https://arxiv.org/abs/1611.02831) | Supports the numerical inclusion-method background. It does not turn a Python run into Lean verification. Retain the stated arithmetic trust boundary. |
| [Haagerup–de la Harpe, *The numerical radius of a nilpotent operator on a Hilbert space* (1992)](https://access.archive-ouverte.unige.ch/access/metadata/2e3d55fc-f7d2-42af-95ae-6c06df864dbb/download) | Classical support-sensitive translation bounds through nilpotency. The concrete two-, three-, and five-point inequalities used in the new refinement are independently proved in Lean. |

Directly relevant 2026 preprints should also be discussed:

* [Groskin, arXiv:2607.02828v3](https://arxiv.org/html/2607.02828v3),
  *A finite Guinand–Weil dictionary and archimedean tail order for the
  truncated Weil quadratic form*. It treats the archimedean **integration
  cutoff** at fixed Fourier rank and derives an ordered Cauchy–Stieltjes
  correction with an explicit budget. Our tail is instead the **omitted
  Fourier-index forcing** of a retained vector. State that difference;
  the shared word “tail” does not make the theorems equivalent. Its
  total-positivity assertion concerns the isolated correction, not the
  complete prime-plus-archimedean Weil matrix. It is a relevant preprint,
  not a theorem imported into this project's Lean development.
* [Zhu, arXiv:2608.24827v2, 2 September 2026](https://arxiv.org/html/2608.24827v2),
  *Weil positivity in compact windows: a finite reduction, certified
  two-sided bounds, and a Landau–Widom decay law*. Its finite reduction,
  coupling bounds, and spectral-envelope estimates overlap the high-mode
  motivation. Compare methods and normalize support carefully: its
  interval `[-L,L]` corresponds to our `log(C)=2L`. Section 7 retracts
  an earlier positivity claim at support 2.38 because of an invalid
  envelope substitution. Cite the revised version, and do not adopt its
  computational claims without replay and proof review.
* [Suzuki, arXiv:2606.09096](https://arxiv.org/abs/2606.09096),
  *Weil's quadratic form via the screw function*. Provides a current
  independent operator-theoretic perspective and links earlier
  positivity and semilocal results. Useful context, not a replacement
  for our constrained-gap or Xi-identification obligations.

The defensible contribution is the signed omitted-index moment reduction
and its support-uniform, machine-validated rank-eight realization. The
displacement formula is prior work; the Hilbert commutator estimate is a
classical consequence of a Hilbert-transform norm; the equivalent digamma
entry formulas are an evaluation choice, as the manuscript itself says.
Do not claim a first general coercivity theorem, a new spectral realization
of Xi, or novelty of all signed expansions. The searches above identify
close predecessors but cannot certify global novelty.

## 4. Replay and publication package

The manuscript's seven-test command was executed with Python 3.12 and
`python-flint==0.8.0`: **7 tests passed**, including regeneration of the
saved 32-subcell infinite-tail cover. The independent mpmath command with
cutoff 20,000 also completed with `ALL CHECKS PASSED`.

The independent script checks matrix entries against direct quadrature
and profiles at `C=17,18,19`. Its first four categories are high-precision
floating checks; only its constant evaluation uses mpmath intervals. It
does **not** independently regenerate the entire certified continuum
cover. Revise any abstract wording suggesting independent replay of all
certified finite-dimensional quantities. The two verification scopes are
different and useful.

Appendix B identifies only a local directory, not an immutable accessible
release. Before submission, prepare a versioned archive with a public URL
or DOI, exact source snapshot, dependency versions, commands, all five
certificate stages, and a complete SHA-256 manifest. Include the spatial
input hash as well as Taylor and even-input hashes. The generator's source
and input-chain checks were inspected and are present; lack of a public
archive is the issue, not an invented absence of hash checking.

The listed full-suite count of 147 is historical. The earlier current
regression run passed 158 tests, followed by five focused common-shift
tests after the additional helper was edited. Do not report that as a
single full 159-test run. Pin the release snapshot and record its own
actual discovery count and execution log instead of chasing a changing
number in the manuscript.

## 5. Lean verification ledger and next theorem targets

[WeilRankTail.lean](../../Reinmann/WeilRankTail.lean) proves the paired
displacement identity, the exact boundary-preserving even-tail identity,
arbitrary-order denominator and weighted-moment remainders, a uniform
scalar geometric-remainder bound, and the two decimal-arithmetic facts.
The general identities quantify over all finite index sets and all orders;
they are not finite sampled tests.

[CoupledRankEnergy.lean](../../Reinmann/CoupledRankEnergy.lean) proves
Galerkin increment orthogonality, exact energy and pairing increments,
the cumulative Cauchy bound, endpoint-energy telescoping, and absolute
summability over infinitely many ranks when both endpoint energies are
uniformly bounded. The conclusion has mathematical content beyond its
hypotheses: no rank summability is assumed. However, the hypotheses have
not been instantiated for the infinite Weil family.

Neither module formalizes the entire Weil distribution, its digamma
analytic bounds, the interval enclosure stack, the infinite `ell^2`
Minkowski theorem specialized to these coefficients, or the rank-eight
certificate values. The paper's blanket statement “analytic arguments
not formalized” should eventually be replaced by this precise partial
ledger. It must not say the main computer-assisted theorem is Lean-proved.

The next meaningful Lean targets are:

1. Complete the analytic tail theorem from the signed expansion: obtain
   summability and the quantitative `ell^2` integral-test majorant.
2. Instantiate the positive energy geometry for a closed Weil form and
   isolate the finite intermediate constrained block using high-mode
   coercivity. A finite low-mode matrix certificate needs a rigorous
   complement/coupling allowance; its positivity alone is insufficient.
3. Prove constrained-gap and origin/boundary controls before using the
   abstract absolute-rank theorem. The generic boundary functional does
   not have bounded dual energy in the logarithmic form norm.
4. Keep the Xi minor route separate. The later
   [real-zero extraction deduction](../STRICT_FINITE_PF_FROM_REAL_ZEROS_2026_10_06.md)
   supplies written all-shift strict contiguous positivity through rank 43
   from classical analytic inputs. Its determinant transport and analytic
   limit bridge are now proved in Lean; the Xi inputs themselves are not.

The active Lean Xi-input and intermediate-mode goals are therefore not
complete. The present review supplies actionable corrections and a formal
starting point for the actual missing estimates.

## 6. Refinement discovered during this review

The [support translation-chain proof](SUPPORT_TRANSLATION_CHAIN_BOUND_2026_10_06.md)
improves the prime-form allowance to `<6.597411`, preserving the finite
chains created by zero extension on the support interval. In the existing
high-mode argument this gives conservative starts `117259` (even) and
`383530` (full), about 159 times smaller than those in the manuscript.
This is a proposed strengthening for a revision, not a correction to a
false original operator estimate. Its Hilbert-space and integrated L² lemmas,
support-to-fiber decomposition, full complex autocorrelation normalization,
complete prime-power enumeration through 19, and uniform prime integral bound
are Lean-proved. The archimedean coercivity specialization is not formalized.
The decimal allowance and threshold endpoints remain Arb computations; Lean
proves the exact logarithmic-square-root expression and its integral bound.

Final verification of the three new modules is recorded separately from
the seven-test Arb certificate replay and mpmath cross-check. No claim
that the complete paper is Lean-verified follows from these checks.

The initial review snapshot's `lake build` completed successfully (3528 jobs). The shortcut scan passed
for all 78 active project Lean files; selected Lean verification passed
for all three new modules. The axiom audit passed for all 141 audited
theorems, including the 19 new results, with only `propext`,
`Classical.choice`, and `Quot.sound`. There are no project `sorry`,
`admit`, or custom axiom declarations. These counts describe this
initial review snapshot, not an immutable published release. Subsequent
Lean continuation results have their own verification ledger; the original
snapshot is retained for provenance.

The [continuation ledger](verification_2026_10_06_lean_continuation/manifest.json)
records 25 additional proved statements: 17 positive-factor transport lemmas,
four analytic PF-limit lemmas and four integrated L² chain lemmas. Its full
build passed 3530 jobs, all 166 axiom-audit statements passed, and the shortcut
scan covered 80 Lean files. Direct checks of all three continuation modules
passed. These improvements do not remove the publication corrections above
or formalize the paper's entire computer-assisted theorem.

The subsequent support-integral continuation is recorded in its own
[verification ledger](verification_2026_10_06_support_translation/manifest.json).
`SupportTranslation` proves actual energy and correlation disintegration on
finite support and the resulting integral inequalities. `SupportPrimeForm`
proves conjugation and shift conventions, completeness of the active prime
powers, exact agreement of the allowance with the evaluated expression, and
the uniform bound for every supported L² function and every `0<C<=19`.
At a disjoint boundary shift the correlation is zero almost everywhere;
the endpoint trace is not assumed zero or bounded. This continuation closes
a previously unformalized analytic input, but does not prove the intermediate
Weil gap, uniform boundary dual energy, Xi identification, or model curvature.
The full build passed 3534 jobs, the axiom audit passed all 205 statements,
and the shortcut scanner covered 82 Lean files. There are 39 new proved
statements: 16 in `SupportTranslation` and 23 in `SupportPrimeForm`. The
earlier ledgers are preserved as separate snapshots.

The next independent Xi continuation proves the actual entire folded function
and its ordinary coefficient identity in `XiTaylorIdentification.lean`.
Its 24 statements include a global square-root formula, infinite convergence
radius, conjugation symmetry, transfer of critical-line zeta zeros to negative
folded zeros, and instantiation of the analytic PF-limit bridge without a
Taylor-identification premise. The
[Xi Taylor ledger](verification_2026_10_06_xi_taylor/manifest.json) records a
3536-job full build, all 229 axiom-audit statements, and direct verification.
Canonical products, center positivity, the sector theorem and Hardy infinitude
remain unformalized. This does not prove order-three strictness in Lean or
change the publication corrections to the Weil manuscript.
