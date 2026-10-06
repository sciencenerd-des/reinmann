# Certified Xi coefficients and finite recurrence laboratory

The coefficient convention is

`xi(1/2+z) = sum mu_n z^(2n)`, `Xi(t)=sum (-1)^n mu_n t^(2n)`.
Thus `mu_n=(-1)^n XiCoeff n` in Lean. The classical folded Jensen coefficients
are `gamma_n=n! mu_n`, not `mu_n`. These two normalizations must stay separate.

## Replay

Use the isolated pinned numerical dependency; no global installation is required:

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/coefficients.py --max-n 120 --bits 4096 --accuracy 128 --theta-max-n 8 --output research/certified_xi/coefficients_120.json
uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/laboratory.py --coefficients research/certified_xi/coefficients_120.json --max-rank 48 --output research/certified_xi/laboratory_120.json
uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/certified_xi -v
```

The output contains **exact rational endpoints**, not decimal approximations
with guessed error bars. The Taylor calculation uses FLINT's rigorous
`acb_series` zeta, gamma and exponential algorithms on
`s(s-1)/2 pi^(-s/2) Gamma(s/2) zeta(s)` about `s=1/2`.
The truncation order specifies which coefficients are calculated; omitted
higher powers cannot contribute to lower powers of a formal Taylor series.
The underlying special-function algorithms enclose their own numerical errors.
Odd coefficients and imaginary parts must contain zero; positive even
coefficients must meet a requested relative accuracy. Otherwise the program
increases precision within its budget, then fails if unresolved.
See [FLINT's series algorithms](https://flintlib.org/doc/acb_poly.html) and
[rigorous zeta derivative computation](https://arxiv.org/abs/1309.2877).

## Independent theta enclosure and tail proof

The classical normalization used here is

```
Phi(u) = sum_{j>=1} (4 pi^2 j^4 exp(9u/2) - 6 pi j^2 exp(5u/2))
                    exp(-pi j^2 exp(2u))
Xi(t) = 2 integral_0^infinity Phi(u) cos(tu) du
mu_n = 2/(2n)! integral_0^infinity u^(2n) Phi(u) du.
```

This is the theta representation in Pólya's 1926 paper, *Bemerkung über die
Integraldarstellung der Riemannschen ξ-Funktion* (Acta Mathematica 48,
305–317). The coefficient identity follows by differentiating the cosine
transform; the double exponential provides domination for every derivative.
It is also consistent with the conventional kernel with coefficients `2,3`
when the leading integral factor is `4`. Mixing those conventions loses a
factor of two. The regression suite deliberately rejects that error.

The finite integral over `0<=u<=U`, `1<=j<=J`, is evaluated by `acb.integral`
on an entire integrand. Its returned ball includes quadrature error. For real
`u>=0`, each summand of Phi is positive, since `2 pi j^2 exp(2u)>3`, and bounded
above by `4 pi^2 j^4 exp(9u/2-pi j^2 exp(2u))`.

Write `C=8 pi^2/(2n)!`, `j0=J+1`, and
`qJ=16 exp(-pi(2j0+1)/2)`. The successive ratios of
`j^4 exp(-pi j^2/2)` are at most qJ. Splitting the exponential into two equal
parts and using `j^2>=1`, `exp(2u)>=1` gives the finite-interval omitted-term bound

```
B_terms = C U^(2n+1) exp(9U/2-pi/2)
          j0^4 exp(-pi j0^2/2)/(1-qJ).
```

For the spatial tail set `E=exp(2U)`, `qU=16 exp(-3 pi E)` and
`a=2 pi E-9/2-2n/U`. For `u=U+v`, use
`(U+v)^(2n)<=U^(2n)exp(2nv/U)` and `exp(2v)>=1+2v`.
The sum over j at U is bounded by `exp(-pi E)/(1-qU)` using the same
ratio comparison. Integration over v then gives

```
B_space = C U^(2n) exp(9U/2-pi E)/((1-qU) a).
```

All three required inequalities `qJ<1`, `qU<1`, `a>0` are checked with balls.
The finite integral is enlarged symmetrically by `B_terms+B_space` (conservative
although these tails are nonnegative). The exact endpoints, both tail bounds,
cutoffs and achieved precision are serialized. Failure of two formulas to
overlap aborts generation. Agreement is a cross-check, not a substitute for
either formula's error proof.

## Trust boundary and interpretation

These are rigorous numerical enclosures conditional on FLINT/Arb correctness,
the classical identities, and the explicit tail argument above. They are **not
Lean certificates**. Hashes identify replay inputs and source, not authenticity.
The loader checks interval order, indices, positivity and theta overlap; it
cannot establish that arbitrary third-party JSON was honestly generated.
The legacy decimal/half-ULP cross-language scans remain a separate experiment.

The lab uses normalized contiguous determinants
`D_r(m)=det[(mu_(m+i-j)/mu_0)]`, with negative indices zero and `D_0=1`.
It records sign enclosures, the exact-algebra deficit expression, and bounded
checks of Desnanot–Jacobi and dual Jacobi–Trudi identities. A ball residual
containing zero is a consistency check, not a proof of an identity.
The rank-48 sweep does not check arbitrary minors, all shifts, or all ranks.

## Rank-two continuation

[The continuation note](../../research/RH_RECURRENCE_CONTINUATION_2026_09_14.md)
derives the scaled-deficit factorization and its precise theta variance target.
Run `rank_two.py` with the same `--coefficients` input and an `--output` path to
replay the separate rank-two and first-shift boundary checks. It reports finite
evidence, not a proof of the continuous curvature estimate or its tail.

## Continuous parameter checks

[The continuous theta note](../../research/RH_CONTINUOUS_THETA_2026_09_14.md)
derives logarithmic-moment tails and monotone interval bounds.
`continuous_theta.py` produces certified pointwise curvature results;
`continuous_cover.py` attempts a finite continuum cover with explicit budgets.
Use `verify_cover.py INPUT --output SUMMARY` to check the exact partition and
extract fully certified subintervals. An incomplete cover does not certify its
entire requested domain.

## Coupled derivative cover

`coupled_cover.py --lo 1 --hi 2 --output OUTPUT` uses a third logarithmic moment
and a mean-value enclosure of the entire curvature numerator. It certifies
[1,2] with 512 cells, where the direct cover exhausted 10,000 cells.
See [the derivation and comparison](../../research/RH_COUPLED_CURVATURE_2026_09_14.md).
The shared moment APIs retain order 2 by default and accept `max_order=3`.
`verify_cover.py` additionally checks serialized mean-value witnesses for these
outputs. The unbounded theta estimate remains open.

## Normalized rank transport

`normalized_recurrence.py --laboratory LAB --coefficients COEFFICIENTS --output OUTPUT`
checks the exact curvature transport induced by exponential-reference
normalization. The current 4,230-window run keeps every total curvature positive,
while detecting 13 negative correction curvatures. A fresh determinant
calculation reproduces the first negative case. See
[the recurrence note](../../research/RH_NORMALIZED_RECURRENCE_2026_09_14.md)
for the compensation inequality that an unbounded proof must control.

## Eventual discrete tail and cumulative budgets

[The tail and rank-budget note](../../research/RH_EVENTUAL_TAIL_AND_RANK_BUDGET_2026_09_14.md)
derives a non-effective eventual discrete result from published coefficient
asymptotics, without differentiating unknown remainders.
`tail_and_rank_budget.py --coefficients COEFFICIENTS --laboratory LAB --output OUTPUT`
calibrates its saddle scale and tests cumulative negative-correction budgets
on contiguous finite rank prefixes. Neither the sampled comparisons nor the
conditional Lean deduction supplies a continuous theta tail or a uniform Xi
rank budget.

## Effective omitted-theta remainder and shift-one boundary

[The effective remainder and boundary note](../../research/RH_EFFECTIVE_REMAINDER_BOUNDARY_2026_09_14.md)
proves explicit relative bounds for replacing Phi by phi_1 in moment orders
0..4, uniformly for every real parameter beyond each declared threshold.
`effective_theta_remainder.py` evaluates those constants. This is separate
from the still-missing first-summand saddle approximation error.

`boundary_budget.py` checks the shift-one reciprocal-coefficient band and
uses B_r(0)=1 in the cumulative boundary correction. `dual_rank_budget.py`
tests higher ranks using small dual determinants. These finite rank checks
supply no uniform Xi cumulative-loss bound. Replay commands, exact scopes,
and trust boundaries are in the note.

## Uniform boundary certificate and curvature error transfer

[The uniform boundary note](../../research/RH_UNIFORM_BOUNDARY_CURVATURE_2026_09_15.md)
proves the shift-one strengthened inequality for every rank and positive
boundary correction curvature for every rank, under an explicit
analytic-numerical trust boundary. `pole_boundary.py` certifies two zeros
inside a bounded disk, bounds the reciprocal-series remainder by Cauchy's
estimate, checks decreasing tail bounds and joins them to finite bridges.
It assumes neither RH nor a global zero table. It is not a Lean certificate.

`curvature_error.py` supplies a conditional error-transfer bound from model
moments to log-epsilon curvature. Effective saddle errors must still be
proved by the caller; sampled model agreement is not accepted as a bound.
The interior all-rank cumulative budget remains open.

## Effective localized saddle integration

`localized_saddle.py --output OUTPUT` encloses first-summand logarithmic
moments with a saddle-centered finite integral and explicit tangent bounds
on both infinite tails. It combines these errors with the omitted-theta
remainder and propagates them into true log-epsilon curvature. The supplied
run certifies negative curvature at x=257, 4097, 65537 only.
[The localized saddle note](../../research/RH_LOCALIZED_SADDLE_2026_09_15.md)
proves the tail bound, records the remaining uniform-parameter obligation,
and explains why extending the pole method one fixed shift at a time does
not establish a uniform all-shift budget. No unbounded curvature claim is made.

## Uniform quadratic saddle remainder

`uniform_saddle.py --output OUTPUT` evaluates explicit relative errors for a
truncated quadratic first-summand model, uniformly for every real x above each
threshold. It includes central phase error, amplitude error and infinite tails.
[The uniform quadratic note](../../research/RH_UNIFORM_QUADRATIC_SADDLE_2026_09_15.md)
gives the proof and acceptance conditions. The bounds are too coarse for
curvature; a fixed standardized window also leaves a nonzero error floor.
The output is classified as a uniform moment bound, not a curvature certificate.

## Higher-order saddle with a growing window

`high_order_saddle.py --output OUTPUT` retains the exact amplitude, expands
the phase through degree 16, and uses L(x)=sqrt(32u), u=W(2x/pi)/2. The
analytic moment-error bounds hold for every real x beyond the stated threshold;
both central and tail errors now vanish in the tail. The supplied curvature
evaluations certify x=100000001 and leave x=1000001 unresolved.
[The higher-order note](../../research/RH_HIGH_ORDER_SADDLE_2026_09_15.md)
gives the inequalities and the remaining uniform model-curvature obligation.
This does not establish uniform curvature negativity or an interior rank budget.

## Leading-model sign theorem and scope controls

`lambert_curvature.py --output OUTPUT` evaluates the endpoint constant in
an analytic proof of negative curvature for the leading Lambert model at
every real x>=256. This is a different model from the degree-16 moment
integrals. [The proof and literature audit](../../research/RH_LAMBERT_SIGN_AND_SCOPE_2026_09_15.md)
give the exact coupled remainder conditions needed to transfer the sign.
They are not yet verified for Xi. The note also gives an exact real-zero
counterexample to deducing normalized-deficit concavity from double-Turan
inequalities alone. `Reinmann.CurvatureControls` checks the algebraic controls.

## Common-remainder derivative bounds

`common_remainder.py --output OUTPUT` freezes the degree-16 reference at an
anchor and uses it unchanged for all neighboring parameters. Complex-disk
domination and Cauchy's estimate give uniform derivative bounds through order
four for the true Xi log remainder, including theta and spatial tails.
[The proof](../../research/RH_COMMON_REMAINDER_2026_09_15.md) shows zero exclusion
before taking logarithms and preserves second-difference cancellation.
This resolves the formerly inconclusive curvature evaluation at a=1000001.
Uniform sign as the anchor varies and the interior all-rank budget remain open.

The [decaying-remainder refinement](../../research/RH_DECAYING_COMMON_REMAINDER_2026_09_15.md)
replaces the fixed theta-error floor with an anchor-dependent bound.
`scaled_derivative_bound(X,a)` proves an explicit envelope proportional to
`(u(a)/u(X))^16 (X/a)^(7+j/2)` for remainder derivative order j. It applies
uniformly beyond a checked threshold; it does not establish the reference sign.

### Gaussian cancellation and a conservative unbounded tail

Current result: the [exactly shifted Gaussian proof](../../research/RH_SHIFTED_GAUSSIAN_CURVATURE_2026_09_20.md)
establishes reference and true theta curvature negativity for every real
anchor a>=10^6, the full domain of the common-reference construction.
The combined relative error is <0.229338. The earlier thresholds below
record the intermediate estimates. Parameters below 10^6 and the
uniform interior all-rank budget remain unproved; RH is not proved.

The [low-anchor reference certificate](../../research/RH_LOW_ANCHOR_REFERENCE_COUNTEREXAMPLE_2026_09_23.md)
shows why the unchanged degree-16 reference cannot simply be extended to
every anchor with the same sign: its curvature is strictly positive at
`a=1` and `a=6`, whereas the true theta curvature is negative at `a=1`.
The compact-domain bridge must use the true integral or a different model.

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/reference_low_anchor.py --output research/certified_xi/reference_low_anchor.json
```

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/shifted_gaussian_curvature.py --output research/certified_xi/shifted_gaussian_curvature.json
```

`gaussian_curvature.py` verifies exact Gaussian cumulant identities and the
endpoint budget for the [written curvature tail proof](../../research/RH_GAUSSIAN_CURVATURE_TAIL_2026_09_19.md).
The proof retains the square of the cubic correction and controls the
analytic remainder on one common complex disk before differentiating.
It establishes negative frozen-reference and true Xi curvature for all
real anchors with W(2a/pi)/2 >= 2000. The threshold is deliberately very
large; negativity at all lower anchors and the interior all-rank budget
remain unproved. The JSON checks algebra and the final budget, not the
entire analytic proof, and carries no RH completion claim.

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/gaussian_curvature.py --output research/certified_xi/gaussian_curvature.json
```

`gaussian_tail_bound.py` sharpens that tail to u>=80 using explicit
monotone envelopes. The [effective proof](../../research/RH_EFFECTIVE_GAUSSIAN_TAIL_2026_09_19.md)
and `research/certified_xi/gaussian_tail_bound.json` record all sufficient
conditions and the relative error budget (<0.009502). This is still a
large-tail result, not all-anchor curvature or an all-rank RH argument.

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/gaussian_tail_bound.py --output research/certified_xi/gaussian_tail_bound.json
```

The [integrated Gaussian error proof](../../research/RH_INTEGRATED_GAUSSIAN_TAIL_2026_09_19.md)
further lowers the sufficient threshold to u>=40. It integrates the error
polynomials against absolute Gaussian moments and enlarges the complex disk
while retaining the full tilt penalty. The uniform relative curvature
error is below 0.038351 of the negative leading margin.

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/gaussian_tail_bound.py --threshold-u 40 --integrated-errors --disk-divisor 2 --output research/certified_xi/integrated_gaussian_tail_bound.json
```

The [direct derivative proof](../../research/RH_GAUSSIAN_JET_TAIL_2026_09_20.md)
now lowers the curvature tail threshold to u>=14. `gaussian_jet_bound.py`
integrates derivative errors first and controls the logarithm with a finite
Taylor-jet norm. The combined reference/true relative error is <0.274447.
The lower-anchor bridge and the interior all-rank budget remain open.

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/gaussian_jet_bound.py --output research/certified_xi/gaussian_jet_tail.json
```

The [cubic cancellation proof](../../research/RH_CUBIC_GAUSSIAN_TAIL_2026_09_20.md)
reduces that sufficient tail threshold to u>=7 (a>=7*pi*exp(14)).
`cubic_gaussian_tail.py` keeps the third-order logarithm polynomial exactly
and bounds the fourth-order remainder. Its combined relative curvature
error is <0.742183<1, sufficient for strict negativity. It still leaves
the lower-anchor bridge and all-rank head conditions unproved.

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/cubic_gaussian_tail.py --output research/certified_xi/cubic_gaussian_tail.json
```

The [coefficientwise refinement](../../research/RH_COEFFICIENTWISE_CURVATURE_2026_09_20.md)
further lowers the threshold to u>=6 (a>=6*pi*exp(12)). It bounds each
derivative separately and retains the reference deficit in the curvature
sensitivities. The combined relative error is <0.468174. The interval
10^6<=a<6*pi*exp(12) and the uniform interior all-rank budget remain open.

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/coefficientwise_curvature.py --output research/certified_xi/coefficientwise_curvature.json
```

### Conditional rank-tail bootstrap

An [exact all-rank control](../../research/RH_REPEATED_ROOT_RANK_CONTROL_2026_09_20.md)
shows that the positive-slope criteria below are stronger than real-rootedness:
for `(1+z/N)^N`, the admissible interior curvatures stay positive but grow
only logarithmically with rank. Every finite slope budget is positive and
its limiting margin is zero. This is a limitation of the sufficient method,
not a Xi counterexample or a failure of either conditional theorem.

The [logarithmic comparison](../../research/RH_LOGARITHMIC_RANK_TAIL_2026_09_20.md)
has exact rational head tests and a conditional infinite-rank proof, but
does not solve this limitation: its neighboring-factor hypotheses create
a persistent positive slope surplus after one step. Its finite Xi heads
are later than the compensated heads. The result identifies why this
scalar workaround still needs stronger growth, rather than certifying
new unconditional Xi ranks.

The [two-sided comparison](../../research/RH_TWO_SIDED_RANK_TUBE_2026_09_20.md)
retains both neighboring terms and preserves value and rank-slope bounds
by simultaneous induction. Its rational-envelope checker proves the
correction inequalities for every rank using exact polynomial coefficients.
Both inequalities become identities on the repeated-root control, including
its zero limiting slope. Xi-specific two-sided envelopes and compatible
head and boundary estimates remain missing.

The [rank-tail theorem](../../research/RH_RANK_TAIL_BOOTSTRAP_2026_09_19.md)
proves that a positive head curvature and slope can pay for all subsequent
negative corrections when the neighboring correction factors remain positive.
`rank_tail_bootstrap.py` checks this sufficient scalar budget on finite Xi
heads. Its passing status is explicitly conditional; it does not certify
an unconditional infinite rank tail from a finite strip.

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/rank_tail_bootstrap.py --coefficients research/certified_xi/coefficients_120.json --output research/certified_xi/rank_tail_bootstrap.json
```

`compensated_rank_tail.py` retains the positive factorial baseline and the
shift factor m/(r+m). Its [conditional theorem](../../research/RH_COMPENSATED_RANK_TAIL_2026_09_19.md)
checks explicit prefix margins and bounds the remaining infinite loss
geometrically. The first passing heads for shifts 2..6 move to ranks
16,21,33,34,44; neighboring-factor and all-shift hypotheses remain open.

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/compensated_rank_tail.py --coefficients research/certified_xi/coefficients_120.json --output research/certified_xi/compensated_rank_tail.json
```

### Shift two at every rank

The [width obstruction](../../research/RH_RANK_TUBE_WIDTH_2026_09_20.md)
proves that the rectangular two-sided comparison forces linear width
growth if any central or neighboring interval has nonzero width. Consequently
its rational specialization can only pass with coinciding envelopes at
each interior triple. `rank_tube_width.py` checks this obstruction with
exact fractions, including distinct envelopes touching at the head.
This restricts the comparison method; it is not a Xi counterexample.
The note derives the joint spatial error difference that a replacement
estimate must control.

The [linearization control](../../research/RH_RANK_LINEARIZATION_2026_09_20.md)
then shows that correlation alone is insufficient. The exact repeated-root
array has a constant-in-shift error mode growing as `r(r+N)/(N+1)`.
Its full spatial spectrum is `n(n-1)`, `2<=n<=N`, with radial polynomial
growth of degree n. `rank_linearization.py` checks exact polynomial
identities; tests independently reproduce the modes by differentiating
Toeplitz determinants. This is sensitivity of a control family, not a
Xi-specific error bound or an all-rank finite-perturbation claim.

The [forced-mode budget](../../research/RH_RANK_GREEN_BUDGET_2026_09_20.md)
derives a Green formula and the exact signed moment that cancels each
growing mode. Under this balance and a potential-sized forcing bound,
the scalar response is uniformly bounded at every rank. The
`rank_green_budget.py` diagnostic implements the N=2 case with exact
rational prefixes and analytic infinite tails; a nonzero balance error
is classified as growing, regardless of its size. This checks a specified
control equation, not the missing Xi source or moment identities.

The [positive correction refinement](../../research/RH_SHIFT_TWO_CORRECTION_2026_09_20.md)
proves `C_r(2)>11/[100(r+2)^2]` for every rank. A common affine pole
model cancels under second differences, and geometric remainder decay
proves the tail from rank 90. Fresh coefficient intervals cover ranks
1..89. The rank slopes strictly increase to beta, with exact cumulative
sum `sum C_r(2)=beta-delta_1(2)` and explicit remaining-gain bounds.
This is a shift-two boundary result; the uniform interior budget remains open.

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/shift_two_correction.py --base research/certified_xi/pole_shift_two.json --coefficients research/certified_xi/coefficients_120.json --output research/certified_xi/shift_two_correction.json
```

The [exponential boundary refinement](../../research/RH_SHIFT_TWO_EXPONENTIAL_TUBE_2026_09_20.md)
also proves `delta_r(2)-delta_(r-1)(2)>0.06085` for every rank r>=1.
It gives compatible two-sided curvature and slope bounds for all r>=60,
using the same three-pole certificate. These supply the shift-two exterior
boundary for a possible comparison over m>=3. The higher-shift envelopes
and comparison inequalities remain unproved. A positive rational lower
envelope cannot fit the known exponential shift-two ratio decay.

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/shift_two_exponential_tube.py --base research/certified_xi/pole_shift_two.json --coefficients research/certified_xi/coefficients_120.json --output research/certified_xi/shift_two_exponential_tube.json
```

`pole_shift_two.py` certifies three real poles inside |z|=800 and bounds
residual determinants while preserving repeated-column cancellation. The
[written proof](../../research/RH_UNIFORM_SHIFT_TWO_2026_09_19.md) establishes
D_r(2)>0 and 0<t_r(2)<1 for every r>=1: the infinite tail starts at 45,
with a certified bridge over 1..44. This fixed-shift result does not depend
on the conditional rank-tail witnesses. It does not prove an all-shift
statement or RH, and is not Lean formalized.

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/pole_shift_two.py --coefficients research/certified_xi/coefficients_120.json --output research/certified_xi/pole_shift_two.json
```

### Shift three at every rank

The [five-pole proof](../../research/RH_UNIFORM_SHIFT_THREE_2026_09_23.md)
uses 201 certified Xi coefficient balls and five real reciprocal poles
inside `|z|=1150`. Its analytic tail proves `D_r(3)>0` and
`0<t_r(3)<1` from rank 82; dual determinant balls bridge ranks 1..81.
This is another fixed-shift result, not a uniform interior rank budget.
The [correction refinement](../../research/RH_SHIFT_THREE_CORRECTION_2026_09_23.md)
also proves `C_r(3)>1/[10(r+3)^2]` at every rank; its tail begins at
rank 137, with a finite bridge through rank 136.

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/coefficients.py --max-n 200 --bits 4096 --accuracy 128 --theta-max-n 8 --output research/certified_xi/coefficients_200.json
uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/pole_shift_three.py --coefficients research/certified_xi/coefficients_200.json --output research/certified_xi/pole_shift_three.json
uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/shift_three_correction.py --base research/certified_xi/pole_shift_three.json --coefficients research/certified_xi/coefficients_200.json --output research/certified_xi/shift_three_correction.json
```

### Obstruction to extrapolating fixed shifts

`fixed_shift_obstruction.py` verifies that multiplying the folded function
by `1+(z/3200)^122` preserves its first 122 coefficients, three certified
interior zeros, and both all-rank fixed-shift inequalities, while adding
an exact nonreal zero. The [proof](../../research/RH_FIXED_SHIFT_OBSTRUCTION_2026_09_19.md)
explains why this is a non-Xi counterexample to an inference, not an RH
counterexample. The full Xi theta/arithmetic identity is not preserved.

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/fixed_shift_obstruction.py --poles research/certified_xi/pole_shift_two.json --coefficients research/certified_xi/coefficients_120.json --output research/certified_xi/fixed_shift_obstruction.json
```
