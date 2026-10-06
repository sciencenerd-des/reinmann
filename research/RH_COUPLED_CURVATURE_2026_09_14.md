# Coupled derivative enclosure for theta curvature

The mean-value method certifies every real x in [1,2] with 512 cells and no
unresolved cells. The direct interval method exhausted 10,000 cells without
certifying the whole interval. This is a finite analytic-numerical result under
the existing FLINT/Arb and theta-tail trust boundary, not a Lean theorem or RH proof.

## Derivative and enclosure

Use the conventions of `RH_CONTINUOUS_THETA_2026_09_14.md`:
I(x) is the theta moment, K=log I, q=c I(x-1)I(x+1)/I(x)^2,
ell=log q, d=1-q and epsilon=(x+1)d. Write L=ell', M=ell'', N=ell'''.
The target numerator and its coupled derivative are

```
G  = q d M + q L^2 + d^2/(x+1)^2
G' = q d N + q L (3-2q) M + q L^3
     - 2 q d L/(x+1)^2 - 2 d^2/(x+1)^3.
```

Indeed q'=qL and d'=-qL. Differentiating the first term contributes
qL(1-2q)M+qdN; differentiating qL^2 contributes qL^3+2qLM.
Combining the M terms gives the displayed coefficient 3-2q.
An exact rational dual-number test independently applies the product rule to G.

The additional derivative requires

```
K''' = I'''/I - 3 I' I''/I^2 + 2 (I'/I)^3
(log c)''' = 2/x^3 + 16/(2x-1)^3 - 16/(2x+2)^3 - 16/(2x+1)^3
N = (log c)''' + K'''(x-1) + K'''(x+1) - 2 K'''(x).
```

For a cell [a,b], let m=(a+b)/2 and h=(b-a)/2. Certified midpoint quadrature
produces C containing G(m). Monotone moment boxes and interval arithmetic
produce D containing G'(x) throughout [a,b]. The mean-value theorem gives

```
G([a,b]) subset C + [-h sup|D|, h sup|D|].
```

The code also checks 0<q<1 and a strictly positive enclosure of (1-q)^2
throughout the cell, then encloses (log epsilon)''=-G/(1-q)^2.
A positive lower bound for G certifies strict log-concavity on the cell.
Budget exhaustion preserves unresolved cells and marks the cover incomplete.

The cancellation improvement occurs in C: the full expression is evaluated
at a single parameter before bounding its variation. D still uses separate
moment boxes and can overestimate substantially. This is a first-order
mean-value method, not a full multivariate Taylor model retaining every moment
correlation. On small cells, the contribution of width-dependent overestimation
in D is multiplied by h; simply raising arithmetic precision would not have
removed the old first-order interval dependency loss.

## Third logarithmic moment and tails

The shared APIs now accept max_order=3, retaining their previous default of 2.
The split integration and absolute tail formulas extend to
I'''(x)=integral u^(2x)(2 log u)^3 Phi(u) du.
On t<0 its finite split integral increases with x; on t>0 it also increases.
The fourth logarithmic power in the parameter derivative is nonnegative,
which proves these endpoint monotonicities directly.

For x in [a,b], A=2a+1 and the previous small-u kernel bound B, the new small-u
absolute remainder is

```
8 B exp(-A L) [L^3/A + 3 L^2/A^2 + 6 L/A^3 + 6/A^4].
```

This follows by integrating 8 B exp(-A v) v^3 over v>=L.
The omitted-series bound is the previous formula with (2 max(L,log U))^3.
The large-u bound uses p=2b+3 in the previous formula, since
|log u|^3<=u^3 for u>=U>=1. All required denominator signs remain checked.
These uniform integrable bounds also justify differentiation on compact
parameter intervals. J=12, L=64, U=4 and 256 working bits are unchanged.

## Reproducible comparison

| Method | Requested domain | Cells | Endpoint parameters | Result |
|---|---|---:|---:|---|
| Direct moment boxes | [1,2] | 10,000 | 30,001 | Incomplete; certified only [1,5345/4096] |
| Coupled derivative | [1,2] | 512 | 3,073 | Entire interval certified |
| Coupled derivative | [2,3] | 506 | 3,037 | Entire interval certified |

The new run took 72.49 seconds on this host. It uses 94.88% fewer cells than
the exhausted direct run and about 89.76% fewer endpoint parameters, while
covering a larger certified domain. An endpoint now includes four moments
instead of three, so endpoint counts are not identical work units. No precise
wall-time speedup is asserted from the historical baseline.

The historical direct artifact is preserved. Shared source files have since
changed to support the third moment; their current hashes therefore differ
from the historical artifact. New outputs record hashes of the coupled
implementation and all three local numerical dependencies.

## Replay and validation

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/coupled_cover.py --lo 1 --hi 2 --output research/certified_xi/coupled_cover_1_2.json
uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/coupled_cover.py --lo 2 --hi 3 --output research/certified_xi/coupled_cover_2_3.json
python experiments/certified_xi/verify_cover.py research/certified_xi/coupled_cover_1_2.json --output research/certified_xi/coupled_cover_1_2_summary.json
python experiments/certified_xi/verify_cover.py research/certified_xi/coupled_cover_2_3.json --output research/certified_xi/coupled_cover_2_3_summary.json
uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/certified_xi -v
```

Validated with 22 tests: the existing suites plus exact derivative algebra,
third-moment enclosures against unsplit integration, third-order tail decay,
cache order upgrades, a cell unresolved by the old method but certified by the
new one, interior point containment, complete small covers, exhausted budgets,
and rejected forged mean-value radii/enclosures. The standard-library verifier
checks rational partition adjacency, signs, the derivative-radius inequality,
and containment of the serialized midpoint-plus-radius witness. It does not
independently prove the quadrature or derivative bounds; those require replay
and the stated mathematical trust boundary. No Lean source changed in this pass.

## First complete discrete window

The [2,3] run completed in 69.80 seconds with 506 positive cells and no
unresolved cells. The exact shared endpoint 2 joins both covers into [1,3],
with 1,018 positive cells. `coupled_cover_1_3_summary.json` records both input
hashes, the checked union and an exact rational uniform margin kappa>0:

```
(log epsilon)''(x) <= -kappa  for all x in [1,3],
kappa approximately 0.000003036388079635799.
```

The approximation is for display; the summary retains the exact rational.
For f=log epsilon, the fundamental theorem of calculus gives

```
f(1)-2f(2)+f(3) = integral_1^3 (1-|x-2|) f''(x) dx <= -kappa.
```

The tent kernel has integral one. Thus
`epsilon(2)^2 >= exp(kappa) epsilon(1) epsilon(3) > epsilon(1) epsilon(3)`.
This provides a continuum-based derivation of the first discrete scaled-deficit
inequality, complementing the existing direct coefficient check. It is neither
a new all-shift theorem nor a claim of literature novelty.

To reproduce the combined margin after verifying the two covers, concatenate
their ordered cell arrays, check the partition on [1,3] with `summarize`, and
take `min(-Fraction(cell['log_epsilon_second']['hi']) for cell in cells)`.
Both input hashes and all four recorded numerical source hashes were checked.
`git diff --check` passed.

## Remaining mathematical work

An unbounded estimate still requires analytic control as x tends to infinity.
The derivative enclosure solves a computational dependency problem on compact
intervals; it does not supply that asymptotic theorem. A useful next analytic
target is a centered-cumulant bound for K''' and neighboring-shift differences,
with explicit remainders uniform beyond a finite threshold. Even an all-x
rank-two estimate would leave the higher-rank quantitative recurrence open.
