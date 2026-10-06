# Continuous theta-curvature laboratory

This continuation replaces integer-only evidence with rigorous logarithmic
moment enclosures at real shifts and a method for enclosing whole parameter
intervals. It retains the existing FLINT/Arb trust boundary: these are not
Lean certificates and do not establish an unbounded tail.

## Integrals and curvature

Let `I(x)=integral_0^infinity u^(2x) Phi(u) du`, x>=0, with the same theta
kernel and normalization as the certified-coefficient generator. We calculate
I and its first two derivatives by integrating

```
I^(k)(x) = integral_0^infinity u^(2x) (2 log u)^k Phi(u) du,
k=0,1,2.
```

The change of variables u=exp(t) gives the finite-integral integrand
`exp((2x+1)t) (2t)^k Phi(exp(t))`. It is entire as a function of t. This avoids
asking a numerical integrator to handle a logarithmic branch at u=0.
Differentiation under the integral is justified by the logarithmic-moment
bounds below, uniformly on compact parameter ranges in x>=0.

For `K=log I`, we use `K'=I'/I` and `K''=I''/I-(I'/I)^2`. For x>=1,

```
c(x) = (2x)(2x-1)/((2x+2)(2x+1))
q(x) = c(x) I(x-1) I(x+1)/I(x)^2
ell = log q,   epsilon=(x+1)(1-q)
G = q(1-q) ell'' + q (ell')^2 + (1-q)^2/(x+1)^2.
```

On any interval where 0<q<1,
`(log epsilon)'' = -G/(1-q)^2`. Strict positivity of a G enclosure therefore
certifies strict log-concavity throughout its parameter domain.

The rational derivatives of log c are evaluated explicitly:

```
(log c)' = 1/x + 2/(2x-1) - 2/(2x+2) - 2/(2x+1)
(log c)'' = -1/x^2 - 4/(2x-1)^2 + 4/(2x+2)^2 + 4/(2x+1)^2.
```

The remaining contributions are K derivatives at x-1,x,x+1. This method
differentiates the defining integrals, not finite differences of noisy data.

## Explicit absolute tail bounds

Use J=12 theta terms, t>=-L with L=64, and u<=U with U=4. The omitted regions
are u<exp(-L), j>J on the finite interval, and u>U. The quadrature ball already
includes its own integration error, following the [FLINT integration API](https://python-flint.readthedocs.io/en/latest/acb.html#flint.acb.integral).
The runtime is pinned to python-flint 0.8.0; the linked current documentation
may describe a newer version.

For a parameter interval `[a,b]`, a>=0, put h=exp(-L), A=2a+1 and

```
B = 4 pi^2 exp(9h/2-pi)/(1-16 exp(-3pi)).
```

For 0<=u<=h, `0<=Phi(u)<=B`. Hence the small-u absolute remainder is at most

```
B 2^k exp(-A L) sum_{j=0}^k [k!/(k-j)!] L^(k-j)/A^(j+1).
```

For the omitted theta series, let j0=J+1,
`qJ=16 exp(-pi(2j0+1)/2)`, and
`S=j0^4 exp(-pi j0^2/2)/(1-qJ)`. On `[h,U]`, use
`|log u|<=T=max(L,log U)` and `u^(2x)<=U^(2b)`. The series remainder is bounded by

```
4 pi^2 U^(2b+1) exp(9U/2-pi/2) S (2T)^k.
```

For the large-u tail, use `|log u|^k<=u^k` for u>=U>=1. Put
`p=2b+k`, `E=exp(2U)`, `qU=16 exp(-3pi E)` and `R=2pi E-9/2-p/U`.
The bound is

```
4 pi^2 2^k U^p exp(9U/2-pi E)/((1-qU) R).
```

All denominators must be certified positive. These are absolute bounds, also
valid when the first logarithmic moment is negative. The pointwise generator
records each tail separately and rejects an unmet accuracy target.

## From points to a continuum

`continuous_theta.py` certifies seven pointwise curvature signs at
`1,3/2,2,5/2,3,4,6`. All seven have G>0. For example, the log-curvature is
approximately -0.02177265 at x=1 and -0.00246981 at x=6. These points alone do
not establish an interval theorem.

`continuous_cover.py` supplies the interval argument. Split the finite t
integral at zero. The truncated Phi is nonnegative on the real integration
path. For each derivative order k:

- On t<0 the integral decreases with x when k is even and increases with x
  when k is odd.
- On t>0 it increases with x for all three derivative orders.

Endpoint quadratures therefore bound every intermediate real x. The code
combines the correct lower/upper endpoint bounds and adds uniform absolute
tails over the entire parameter cell. It then uses interval arithmetic for G.
No interpolation or assumed smoothness error is substituted for these bounds.

Unresolved cells are bisected within explicit depth and cell budgets. The
partition checker requires exact rational endpoint adjacency, with no gaps or
overlaps. A budget-exhausted cover is labeled incomplete; an unresolved cell
is never relabeled positive. A certified subdomain must be a complete union of
certified cells with its own explicit endpoints.

This direct enclosure is conservative: independent interval treatment loses
correlations among I,I',I'' and neighboring shifts. A future improvement is a
Taylor model with jointly bounded derivatives. More working bits alone cannot
remove uncertainty caused by the width of a parameter interval.

## Replay

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/continuous_theta.py --output research/certified_xi/continuous_theta.json
uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/continuous_cover.py --lo 1 --hi 2 --output research/certified_xi/continuous_cover_1_2.json
uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/certified_xi -v
```

Scope: a finite continuous region is useful calibration for the proposed theta
curvature estimate. Even a successful cover of [1,2] does not supply the full
interval [1,3] needed for the discrete log-concavity inequality centered at 2,
and does not prove any all-shift or all-rank statement.

## Completed cover and validation

The requested [1,2] cover exhausted its 10,000-cell budget. It contains 9,992
positive-G cells, zero negative-G cells and eight unresolved cells. Its overall
status is **incomplete_cover**.

The partition/sign verifier extracts one fully certified continuous subinterval:

```
[1, 5345/4096] = [1, 1.304931640625].
```

Throughout that subinterval, epsilon is positive and has strictly negative
log-curvature, under the stated numerical and analytic trust boundary. This
statement covers every real parameter in the interval, not just its endpoints.
It establishes neither the whole requested [1,2] domain nor an unbounded tail.
The unresolved cells are retained in the artifact.

Artifacts:

- `research/certified_xi/continuous_theta.json`: seven certified pointwise results
  with separate logarithmic-moment tail bounds.
- `research/certified_xi/continuous_cover_1_2.json`: complete partition of the
  requested domain, including unresolved cells and exact rational G bounds.
- `research/certified_xi/continuous_cover_summary.json`: checked subdomain summary
  tied to the cover by SHA-256.

Replay the consistency check with:

```sh
python3 experiments/certified_xi/verify_cover.py research/certified_xi/continuous_cover_1_2.json --output research/certified_xi/continuous_cover_summary.json
```

Validated with 18 certified-Xi tests, including integer-moment agreement with
the separate u-integral implementation, fractional-point enclosures, tail and
precision failure cases, a complete small cover, budget exhaustion, and
rejection of invalid partitions and false positive labels. Pointwise and cover
generation completed; their source hashes were verified. `git diff --check`
passed. This pass changes numerical tools and documentation, not Lean proofs.

The interval computation evaluated 30,001 endpoint parameters. Its cost shows
why merely enlarging the domain is a poor next experiment. A coupled Taylor
model or a mean-value bound for G using one further logarithmic moment should
preserve cancellations better. That improvement requires a rigorous third
moment tail and derivative propagation; it is not supplied by the current
pointwise precision or a fitted curve.

## Subsequent coupled improvement

The historical direct-cover result above is preserved. The next pass implemented
the coupled derivative method and certified [1,3]; see
[the coupled curvature report](RH_COUPLED_CURVATURE_2026_09_14.md) for the derivative
proof, subdivision comparison, artifacts and remaining unbounded gap.
