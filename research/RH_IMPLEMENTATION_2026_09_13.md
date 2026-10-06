# RH research implementation — 2026-09-13

The six requested work packages now have concrete code, mathematical interfaces,
replay commands and stated proof boundaries. This is a research infrastructure
milestone, not a solution of RH. The principal new research target is a
quantitative inequality for contiguous Toeplitz determinants that would
propagate positivity through all orders.

## 1. Mathematical interfaces and classifiers

`Reinmann/JensenProgram.lean` now defines the entire completion as
`xi(s)=1/2+s(s-1)/2 completedRiemannZeta₀(s)`. Lean proves that it is entire,
that xi(0)=xi(1)=1/2, and that it equals the classical product away from the poles.
The critical-line identity is retained with the repaired definition.

The old Jensen polynomial built directly from ordinary Taylor coefficients is
retained as an explicitly labeled diagnostic. The actual folded classical
Jensen interface uses `gamma_n=n! (-1)^n XiCoeff(n)`. The main Jensen witness,
closure and approximation interfaces now use `ClassicalJensenPoly`.
`PolyaJensenBridge` is still a hypothesis requiring proof; its correct type is
not itself a formalization of the analytic theorem.

The finite-product witness now requires local uniform convergence on the
complex plane. Pointwise convergence on the real axis was too weak for the
intended analytic closure argument. The HPSS route explicitly records that its
coefficient-hyperbolicity input already contains the legacy output, so it is
not counted as an independent discovery mechanism. Lean also proves that the
legacy `KernelEffectiveCertificates` predicate is equivalent to the strict
ladder itself; its existential cutoff encodes no effective error estimate.

The Hadamard cancellation predicates are indexed by one specified height.
Their former universal versions forced the derivative of a nonconstant entire
function to vanish along a whole line. The freely chosen `canonical : Prop`
tag has been removed: it imposed no relation on the approximants. This remains
a generic derivative-transfer construction involving Lambda₀, not an arithmetic
spectral construction or a substitute for Xi's zero set.

Six diagnostic scripts now distinguish sampled numerical behavior from a
theorem. Repairs include factorial Jensen weights, root-solver outcomes rather
than a quartic discriminant classifier, the backward-heat sign and factorial
coefficient factors, mirror-paired particle perturbations, seeded independent
spacing toys, and honest cross-precision labels. The quartic `X^4+1` is a
regression control: positive discriminant, no real roots.

Historical paper/figure outputs were not regenerated. Their old claims and
normalizations are not validated by the repaired generators. The original audit
JSON is retained; `diagnostics_after_repairs.json` records the current replay.

## 2. Certified coefficients

`experiments/certified_xi/coefficients.py` generated 121 positive ordinary
coefficients, n=0 through 120, using python-flint 0.8.0 at 4096 working bits.
The least accurate coefficient has **2317 relative bits**. Each coefficient is
serialized with exact rational lower and upper endpoints.

Nine coefficients, n=0 through 8, have separate theta-integral enclosures at
the requested 128-bit accuracy. Those integrate twelve theta terms on [0,4],
include the quadrature enclosure and explicit bounds for both omitted terms
and the infinite spatial tail. All nine overlap the Taylor enclosures.

The Taylor route uses rigorous special-function series rather than Cauchy
sampling with an unbounded aliasing error. The theta route's normalization and
tail inequalities are derived in `experiments/certified_xi/README.md`.
FLINT/Arb correctness and those classical analytic identities remain the trust
boundary. These are rigorous numerical balls, **not Lean-checked coefficient
certificates**. Independent formulas reduce the chance of a convention error;
shared arithmetic means they are not independent implementations of Arb.

## 3. Established positivity baseline

`research/FINITE_PF_BASELINE_2026_09_13.md` records the source, coefficient
convention, transpose convention and quantifiers. Katkova states PF44, but the
sector and theorem as printed support PF43 directly; this implementation uses
the conservative PF43 consequence and flags the discrepancy.

`Reinmann/FinitePFBaseline.lean` proves finite-rank monotonicity, scalar transport,
transpose equivalence, transport to Xi entries and contiguous minors, and the
equivalence of full PF with finite PF at every rank. The analytic Xi PF43 result
is **not formalized here** and remains an explicit premise. No axiom was added.

Consequently, rank-3/rank-4 sign scans should serve as calibration and quantitative
margin measurements. They do not reveal a previously unknown global positivity
phenomenon. Finite PF nonnegativity also must not be promoted to strictness.

## 4. Theta deficit laboratory

For positive mu define

```
q_n = mu_n mu_(n+2)/mu_(n+1)^2,    delta_n = 1-q_n.
D3(n+2)/mu_(n+2)^3 = delta_(n+1)^2 - q_(n+1)^2 delta_n delta_(n+2).
```

`Reinmann/TuranDeficit.lean` proves the five-coefficient algebraic identity and
a sufficient positive-slack lemma. This accommodates decreasing coefficient
ratios and does not rely on the old increasing-ratio sufficient conditions.

The ball laboratory certifies **117** Taylor-based deficit windows and **five**
windows using only the independent theta enclosures. Every tested margin is
positive. The normalized Taylor margin goes from approximately 0.0781556 at
n=0 to 4.21082e-6 at n=116. The corresponding relative safety at n=116 is about
0.0254808. These decimals are explanatory approximations; the JSON contains
outward-rounded rational bounds.

When q and delta are positive, the exact target can also be written

```
log(delta_n)-2 log(delta_(n+1))+log(delta_(n+2)) < -2 log(q_(n+1)).
```

This separates a discrete curvature cost from a positive budget. To prove an
all-offset estimate, bound the two sides from the theta integral with errors
smaller than their difference. A fit to sampled margins cannot close the tail.

## 5. Unbounded-order search: a concrete quantitative candidate

Normalize `e_n=mu_n/mu_0`, extend it by zero at negative indices, and set
`D_r(m)=det[e_(m+i-j)]`, `D_0(m)=1`. Desnanot–Jacobi gives

```
D_(r+1)(m) D_(r-1)(m) = D_r(m)^2-D_r(m-1)D_r(m+1).
```

Positive adjacent determinants alone do not control the subtraction. The
candidate to investigate is the stronger quantitative inequality

```
(m+r) D_r(m-1)D_r(m+1) <= m D_r(m)^2       (r,m >= 1).
```

Equivalently, wherever the center is nonzero,
`eta_r(m)=1-D_r(m-1)D_r(m+1)/D_r(m)^2 >= r/(m+r)`.
The constant has an algebraic reference, not just a numerical fit. For the
exponential sequence `e_n=1/n!`, row scaling turns the determinant into a
Vandermonde determinant of monic falling-factorial polynomials, giving

```
P_r(m) = product_{j=0}^{r-1} j!/(m+j)!,
P_r(m-1)P_r(m+1)/P_r(m)^2 = m/(m+r).
```

Thus the proposed bound is exactly log-concavity in m of `D_r(m)/P_r(m)`.
The exponential reference saturates it, and a separate regression test checks
this normalization. For r=1 this specializes to the factorial-strengthened Turan inequality. For
higher ranks it asks for a corresponding curvature bound on rectangular
Toeplitz determinants. This is a **candidate**, not a claimed new theorem or
an assertion of originality.

The implemented sweep certifies:

- 4,680 positive contiguous minors for 1<=r<=48 and 0<=m<=121-r.
- 4,512 positive recurrence margins for 1<=r<=47 and 1<=m<=120-r.
- The proposed lower bound in all 4,512 tested windows.
- 72 bounded dual Jacobi–Trudi consistency checks, exchanging rank and shift.

The smallest tested slack above r/(m+r) is approximately 0.00442017, at r=1,
m=119. The test includes ranks beyond the conservative PF43 baseline, but
neither arbitrary minors nor all shifts at those ranks have been checked.

Given the recurrence, positive base and boundary, and this inequality uniformly
in r,m, induction would propagate strict contiguous positivity. A separate
valid contiguous-to-full-PF theorem and the analytic Xi identification are
still needed for the RH route. Lean proves the single-step quantitative
condensation implication, without assuming that Xi satisfies its input bound.

A second representation is available without fitting zeros: define h by
`H(z)E(-z)=1`, then use dual Jacobi–Trudi to exchange determinant rank and shift.
The recurrence defining h contains alternating subtraction; the dual identity
alone does not create a nonnegative factorization. A productive next attempt
is to derive the quantitative bound, or a positive path/Gram representation
that implies it, directly from the theta integral after factorial weighting.

The adversarial kernel `3 cos(t)+cos(2t)` prevents false generalization from
positive kernel weights or a short ladder. It has an off-real zero and passes
the sampled ranks 1–5, yet its rank-6, shift-2 raw determinant is exactly
`-26968264743653/74568823160832000`. The certified laboratory rejects it.

## 6. Independent arithmetic spectral program

`experiments/prime_spectral/weil_matrix.py` implements a finite Weil-form matrix
from primes and prime powers with an analytic archimedean tail. It uses no zeta
zero input. The source formulas and remaining gates are documented alongside it.

Nine runs cover prime-power support cutoffs 3,5,13 and mode cutoffs 2,4,8.
Five smallest-eigenvalue diagnostics are unresolved at the observed refinement
scale; four exceed that scale but are still uncertified. None is called a
zeta ordinate. This is not yet the source paper's perturbed scaling operator.

The next gate is rigorous control of the smallest eigenspace, followed by its
simplicity, parity, normalization, omitted-mode error, and eventually locally
uniform convergence of normalized entire determinants. Increasing matrix size
before resolving the current error scale would produce less reliable evidence.

## Validation and replay boundaries

Commands and trust boundaries are in the two experiment READMEs. The active
Lean library builds; the axiom audit covers the reduction chain and new
transport/deficit lemmas. Regression suites cover classifier counterexamples,
heat coefficients, interval failures, independent formulas, exact control
determinants, recurrence identities, prime powers, analytic tails and matrix
refinement. Completed validation:

- `lake build`: passed, 3,524 jobs.
- `bash scripts/verify_axiom_clean.sh`: passed, 96 audited theorems, no
  `sorry`/`admit` or project-declared axioms.
- `scripts/safe-verify.sh` on all eight modified/new mathematical modules:
  passed; the source shortcut scan covered 74 Lean files. This was not a fresh
  direct typecheck of every unchanged module.
- `lake env lean research/rh_discovery_audit_2026_09_13/SemanticChecks.lean`:
  passed, six regression/algebra lemmas.
- Python unittest suites: 5 classifier tests, 6 certified-coefficient/laboratory
  tests, 4 prime-spectral tests passed. Existing pytest uncertainty suite:
  4 passed. Total: 19 tests.
- Coefficient generation, rank-48 lab and nine-run prime sweep completed;
  source/input hashes match. Six modified diagnostic generators parse.
- `git diff --check`: passed.

Not run: full historical plot/log regeneration, manuscript build, or the entire
cross-language row scan. Existing dirty manuscript and row-scan work was
preserved. No commit or push was performed.

The most useful next mathematical work is the uniform quantitative recurrence
bound, beginning with a theta-derived proof at rank 2 and with errors explicit
in shift. The finite scans calibrate that work. They do not substitute for it.

## Continuation on 2026-09-14

The [recurrence continuation](RH_RECURRENCE_CONTINUATION_2026_09_14.md) now gives
an abstract all-rank induction theorem, a more specific sufficient rank-two
condition, an exact counterexample to lifting rank-one information alone, and
new independent theta-based finite checks. It supersedes the single-step-only
status above; the Xi analytic hypotheses remain unproved.
