# PNT+ Hadamard backport and a locally proved PF43 theorem

The external Hadamard lead is valid. The required PNT+ dependency closure has
been backported to this repository's unchanged Lean/Mathlib v4.30.0, and its
factorization and growth results now discharge both analytic inputs for actual
folded Xi. `Reinmann.XiFinitePFCertified.finitePF43` has no theorem hypotheses.
This is a formalization of the classical finite-order baseline, not a new
analytic result or an RH proof. The new modules are optional explicit targets;
they are outside the unchanged root import and its audit.

## Pinned upstream and actual port size

Source: [PrimeNumberTheoremAnd at 127b50e33f6033e2147921167a117af96d9ba4ea](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/tree/127b50e33f6033e2147921167a117af96d9ba4ea),
whose toolchain is v4.35.0. The complete transitive local source closure of
`HadamardFactorization.Order` and `RiemannZetaHadamard` is **61 files and 14,306
original source lines**, larger than the supplied estimate based on 21 core
files. All upstream copyright and author headers are retained under Apache-2.0;
see `Reinmann/PNTPlus/LICENSE` and `UPSTREAM.json`. Matteo Cipollina authored the
Hadamard development and most analytic helpers. The credit for those proofs
remains upstream.

The compatibility changes are recorded in a complete patch against archived,
checksum-bound original bytes. They adapt imports, newer `using!` syntax,
renamed set/measure/continuity lemmas, constant-integrability ambiguity,
function-product rewriting and a pi-norm proof. No axioms, admitted proofs,
`native_decide`, toolchain changes, or root-import changes were introduced.
The prior local search covered installed Mathlib and missed this external
factorization development; it was not evidence that no Lean version existed.

## How the actual folded-Xi obligations are discharged

`XiHadamardProduct.riemannXi_eq_xiCompleted` proves exact equality of PNT+'s
entire Xi and our normalization by algebra. The pole-subtracted completion is
not substituted for the actual zero-set target.

The imported order-one bound for actual Xi, evaluated with epsilon=1/2, gives
a bound with exponent 3/2. Applying `foldedXi_eq_sqrt` and
`norm(sqrt(z))^2 = norm(z)` yields

    norm(foldedXi(z)) ≤ exp(K * (1 + norm(z))^(3/4)).

`foldedXi_order` packages this as `EntireOfOrderAtMost (3/4) foldedXi`.
A fixed exponent strictly below one suffices; exact order 1/2 is unnecessary.
No differentiability of the square-root branch is asserted or used.

`divisor_multiplicity` identifies the meromorphic divisor's natural
multiplicity with `analyticOrderNatAt`. `zeroIndexEquiv` then identifies PNT+'s
nonzero divisor index with the repository's canonical index, retaining every
multiplicity label. Nonvanishing at the origin and finite analytic orders are
already proved. No simple-zero, distinct-modulus, or gap hypothesis appears.

PNT+'s finite-order Jensen summability theorem gives
`XiHadamardProduct.summable_inverse_zeros` on this exact index. Its Hadamard
theorem has genus `floor(3/4)=0`, so its exponential polynomial is constant.
Evaluating at zero identifies that constant with `XiMomentCoeff 0` and proves
`XiHadamardProduct.foldedXi_product`, the actual normalized product identity.
These are conclusions, not repackaged hypotheses.

The preceding canonical-index, real-approximant, polynomial-sector and analytic
limit modules then prove `XiHadamardProduct.katkovaSectorBridge` for every
positive fixed rank. This is an implication from the existing angle bound; it
does not assert the angle bound at every rank.

Finally `XiFinitePFCertified.finitePF43` combines that bridge with the already
proved height-14.1 rectangle. It proves nonnegativity of all ordered Toeplitz
minors through rank 43 for the actual **ordinary** sequence `XiMomentCoeff`.
It is not a strict-positivity statement or merely a contiguous-minor scan.
`finitePF58` in the same module takes only the external 7/8 proposition.
Unbounded-rank PF, the Green-form budget and RH remain unproved.

## The external OpenAI 7/8 theorem: verified source and reported rebuild

At OpenAI source commit
`1581d4cbdd69a0faf34b2089614fe2a814316a6a`, the [solution module](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean)
states `riemannZeta_ne_zero_of_seven_eighths_lt_re` for Mathlib's actual
`riemannZeta`, with precisely the half-plane used by
`QuasiRiemannHypothesisSevenEighths`. Its body invokes the unconditional final
assembly. The [scope note](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/docs/003.md)
identifies the companion papers and distinguishes the zeta/Dirichlet and Hecke
statements. The comparator file is a challenge template containing `sorry`;
it is not the solution proof.

The [independent rebuild report at b83a73c6cb626a391e551baafdb7d0cceafaa55a](https://github.com/tomoto0/quasi-riemann-hypothesis-7-8-verification/tree/b83a73c6cb626a391e551baafdb7d0cceafaa55a)
reports a source rebuild of 2,924 OAI modules on v4.34.1, and publishes standard
axiom output for the zeta and Dirichlet results. It pins a different upstream
OpenAI commit, `adc7f1241b42`; this receipt is not a rebuild of the later pinned
source used for our statement inspection. The report explicitly did not build
the Hecke challenge, and stopped its full-closure `leanchecker` replay before
completion. Those limitations should remain attached to the report.

We inspected the pinned sources and saved the report/axiom output, but **did
not replay OpenAI's large proof locally** or import it into v4.30. Suitable
wording is: externally formalized with an exact statement match and a reported
independent rebuild; unrefereed. Our named proposition remains an input.
Existing comments already identify the external kernel-checked theorem and
lack of a local import. Frozen proof-source files and published PDFs were not
rewritten just to change wording.

## Katkova citation and Holland's Jensen result

The 2007 Katkova citation is valid: *Multiple positivity and the Riemann
zeta-function*, Computational Methods and Function Theory 7 (2007), 13–31,
DOI [10.1007/BF03321628](https://doi.org/10.1007/BF03321628). The author's
[faculty publication list](https://www.math.umb.edu/people/faculty_publications_by_year.php?id=289)
confirms those journal details. [The arXiv preprint](https://arxiv.org/abs/math/0505174)
is from 2005; it reproduces Schoenberg's sufficient polynomial criterion as
Theorem B. These dates are different versions of the same work. The known
printed PF44/angle-43*pi/44 mismatch still warrants our conservative rank 43.
No correction to the year in the repository bibliography is needed.

[Jonathan Holland, arXiv:2608.08682](https://arxiv.org/abs/2608.08682), submitted
9 August 2026, gives a joint degree/derivative hyperbolicity region
`n^3 log^2(n+2) ≥ K d^5` and a semicircle limit. Its coefficient convention is
`xi(1/2+z) = sum gamma(n) z^(2n)/n!`, hence gamma(n) equals `n! * XiMomentCoeff n`
in our convention. This is an asymptotic Jensen-route result with an
unspecified absolute K; it supplies neither the genus-zero identity nor a
finite numerical certificate here. It belongs in the current literature
review as a tail result, without expanding our novelty claims.

## Verification and CI scope

The explicit target `Reinmann.XiFinitePFCertified` builds. A separate semantic
audit enumerates the imported theorem declarations owned by all 61 port
modules and both new application modules: **825 distinct theorem declarations**,
including helpers, have only the standard axioms `propext`, `Classical.choice`
and `Quot.sound` (or no axioms). Six headline statements also have explicit
`#print axioms` checks, and the PF43, conditional PF58 and sector-bridge types
are checked separately. Source scanning rejects admissions and custom axioms.

The evidence directory `verification_2026_10_20_pnt_hadamard/` retains all 61
fresh source elaborations, the two new source elaborations, explicit/default
builds, the unchanged 1619-declaration root guard, semantic/type checks,
original sources and the port patch. The new verifier replays the complete
canonical-index parent checkpoint without rewriting any earlier manifest.
Some upstream style warnings remain in the port logs; they are not admissions.

This is local Lean verification. The older hosted run 39425081613 covers the
rectangle proof source, not this backport or new PF43 module. Its numerical
job was still running at preparation. CI-gated README/objective edits and the
held commit push remain pending. Published versions and height 14.1 remain
unchanged. No external messages or Liu note were sent.
