# Useful next theorems for the Weil-window route

Date: 7 October 2026. This plan accompanies a committed local certificate
and a conditional Lean interface. It supersedes no other uncommitted work.

## What actually moved in this change

We now have two replayed full-window certificates at `C=exp(6/5)` and
22 Lean-proved statements. The second certificate reduces the polynomial
count from 160 to 124 by charging coupling quadratically. Its two blocks
are 62-dimensional; it retains both pole signs and both prime terms.
The Schur certificate succeeds where the linear `ell-B` bound fails.
The **support endpoint has not increased**. This is verified progress in
the proof machinery, not a new numerical frontier or a proof of RH.

The named Lean inputs are:

| Input | Exact open obligation |
|---|---|
| `CertifiedExpSixFifthsHypothesis` | Identify Q with the actual Weil form and establish its full-window lower bound; presently backed by the written/Arb proof, not a Lean proof. |
| `WindowBlockHypotheses` | Supply analytic source domination, actual orthogonal energy splitting, finite-block bounds, whole-complement coercivity and full coupling for the chosen Q. |
| `Polynomial124SchurHypothesis` | Instantiate those same obligations with the explicitly rounded constants of the new 124-mode run. |
| `CofinalWindowBoundsHypothesis` | Produce full-form nonnegative bounds for arbitrarily large supports. No fixed finite collection of certificates supplies this. |

`certified_exp_six_fifths_of_blocks` and
`certified_exp_six_fifths_of_schur_blocks` are proved implications with
these inputs visible in their types. The module does not assert an
analytic Weil criterion or silently instantiate Q with zeta. The cofinal
lemma assembles all-window positivity only from an explicitly unbounded
input; it is not a new approach to RH by itself.

## Priority 1: preserve positive tail directions and certify their Schur cost

The target is a **direction-sensitive inverse-energy bound**, not a
replacement of the prime-comb supremum by a support-shift norm. For a
retained space P and complement S, write a genuine reduced form in blocks
`A, B, D`, with `D>=d I>0`. The decisive finite inequality is

\[
       A-\epsilon I-B(D-\epsilon I)^{-1}B^*\succeq0.
\]

The current scalar certificate replaces the inverse energy by
`||B||^2/(d-epsilon)`. The next theorem should bound the actual matrix
`B(D-epsilon I)^-1 B*`, preserving signed source directions or certified
spectral bands. This connects with the existing coupled-energy and signed
omitted-index work without treating a ground-vector forcing bound as an
operator bound over all retained vectors.

Concrete experiment: compute interval coupling allowances separately for
the smallest retained eigenspace and its orthogonal complement at the
already replayed window. Certify the retained change of basis and charge
the omitted block only once. Success is a strictly stronger certified
matrix lower bound or a smaller required N, with all source terms intact.
Failure is a rigorous budget excess that identifies the responsible
direction. Do not label an approximate eigenbasis as a certified one.

This is standard Schur theory. Our new result is its verified instantiation
in this local code, not priority for the method. Compare with Liu's retained
tail and block-Schur construction before claiming any method novelty.

## Priority 2: reduce the frequency cutoff without an invalid comb substitution

A pointwise envelope based on the full comb mass is rigorous but expensive.
A useful next source-side theorem is an interval-certified lower bound for
the **complete** symbol on `[T0,Tglobal]`, followed by the classical analytic
envelope above `Tglobal`. This can justify a smaller initial cutoff T0 if
the symbol stays positive there. It must cover the entire band; checking
a grid is insufficient. If an interval-certified negative symbol value
appears, that rejects this particular scalar reduction, not Weil positivity.

This finite-band refinement is already suggested in Zhu's
[Section 7 and discussion](https://arxiv.org/html/2608.24827v2); do not
claim it as a newly discovered strategy. Combine any successful cover with
the Schur assembly and re-certify both parity blocks and the complement.

The support-dependent prime-shift allowance belongs to an operator on a
time-limited space. It is **not** a pointwise upper bound for the prime
comb on the frequency line. Multiplication by a frequency cutoff also
does not preserve compact time support. Any proof that uses the stronger
shift allowance must explicitly control these projections and their
cross terms. Otherwise it repeats the sign/localization problem behind
the retracted claim.

## Priority 3: isolate the jump contributions rather than hiding them in norms

Truncating a translated supported function introduces interior jump
locations. A global smooth polynomial basis can lose its rapid convergence
there. For the *finite retained sources*, subtract their explicitly known
jump jets and bound the smoother residual. The desired theorem is a
quantitative bound on the residual coupling energy after adding these
known directions to the retained block. Preserve every prime-power weight
and the indefinite pole term.

Two cautions matter. Boundary evaluation is not bounded in the generic
logarithmic form norm, as the existing repository audit shows. Also shifts
by log(2) and log(3) do not admit a common finite invariant partition:
their irrational ratio rules out that simplistic basis claim. A finite
list of low-vector jump sources is a different, testable construction;
it does not solve the complement problem automatically.

Success must be expressed as a bound on the complete form or an operator
Schur energy. An improved tail for one chosen vector does not certify
positivity of the whole window.

## Prior-art gate before a larger endpoint claim

Audit Liu's frozen `b6cd2183c1e79c6c27a34267812a7b2d73ed1b59` release.
Its [reproduction instructions](https://raw.githubusercontent.com/luciferyu666/certified-weil-positivity/b6cd2183c1e79c6c27a34267812a7b2d73ed1b59/REPRODUCIBILITY.md)
distinguish clean reconstruction of Theorem B from retained-proposal
verification of Theorem A. Read the manuscript/domain/proof dependencies
and verify source-to-matrix reconstruction as well as integer residuals;
archive integrity alone is not a proof. That audit was not executed here.

Until then, treat `C=exp(17/8)` as a competing **claim**, not as a
verified record or an ignorable preprint. A concrete endpoint challenge
would be `C=19/2=9.5`, including prime power 9, with every omitted-mode and
coupling term certified. It is a target, not an achieved result. A result
at `C<5` is a useful replication and engineering milestone but does not
surpass that claim.

The follow-up search also located Desogus,
[*The Three Gates*, arXiv:2609.20367v2](https://arxiv.org/abs/2609.20367v2),
which claims all-window induction and RH. Only its primary abstract was
checked here. No analytic proof, induction transfer or certificate was
audited or accepted. Keep it on the audit list; do not import its conclusions
or treat a claimed RH proof as established prior art.

## What would constitute progress toward RH

There are three distinct levels: removing external Lean inputs improves
verification; increasing the rigorously certified support endpoint improves
finite mathematical coverage; proving scale-dependent estimates that
produce a cofinal family addresses the unbounded problem. Finite margins
may tend to zero. A uniform positive scalar gap is neither supplied nor
necessary for all-window positivity, but every scale still needs valid
complement and coupling control.

Continue with these analytic targets. Do not resume fixed-order minor
scans, low-degree Jensen/Turan experiments, de Bruijn--Newman bound attempts,
or scalar Cauchy budgets that discard the source alignment by orders of
magnitude. Those directions are excluded for this task.
