# A uniform effective quadratic saddle remainder

## What is established

`experiments/certified_xi/uniform_saddle.py` evaluates an explicit relative
error bound for the first-summand logarithmic moments J_k(x), k=0,1,2,
against a truncated quadratic model Q_k(x). Each output applies to **every
real x >= X**, not just a finite list. It covers the central approximation,
the amplitude defect, and both infinite spatial tails.

This is a uniform approximation theorem with computable constants. It does
not establish negative curvature: the certified approximation is too coarse
for the existing absolute-error propagation near a vanishing deficit. It
also supplies no interior all-rank budget. The previous shift-one boundary
certificate is unchanged.

## Model and notation

Use the phase p_x(t) and amplitude b(t) from the localized saddle note:

    p_x(t) = (2x+1)t + (9/2)exp(t) - pi exp(2 exp(t)),
    b(t) = 1 - 3/(2pi) exp(-2 exp(t)).

For x >= X >= 256 define

    u = W(2x/pi)/2, c = log(u), x = pi u exp(2u),
    A = -p_x''(c) = 2x(1+2u) - (9/2)u,
    lambda = p_x'(c)/sqrt(A) = (1+(9/2)u)/sqrt(A).

Let L >= 2 be a fixed standardized radius and t = c+s/sqrt(A). Define

    Q_k(x) = 4pi^2 exp(p_x(c))/sqrt(A)
             integral_{-L}^L exp(lambda*s-s^2/2)
                            [2(c+s/sqrt(A))]^k ds.

The amplitude in this initial model is 1; its difference from b is included
explicitly in the error. Q_k is not the pointwise midpoint model in the
previous note. Error bounds for one model must not be attached to another.

## Uniform derivative constants

Set u0 = W(2X/pi)/2 and define

    A0 = X(1+2u0), h0 = L/sqrt(A0), z0 = 1/(sqrt(A0) log(u0)),
    D0 = sqrt(2/pi) L exp(-u0) exp(h0),
    a0 = 11/(2 sqrt(2pi)) exp(-u0),
    C0 = 3 exp(3h0+D0) sqrt((2+1/u0)/pi) exp(-u0)
         + (9/4) exp(h0) X^(-3/2).

The implementation checks u0>1 and L z0<1, ensuring every central logarithmic
weight is positive. The following bounds hold uniformly for x>=X and |s|<=L:

    A >= x(1+2u) >= A0,
    0 < lambda <= a0,
    |p_x'''(c+s/sqrt(A))|/A^(3/2) <= C0.

Here are the details supporting the last bound. If v=exp(t), differentiation
at fixed x gives

    p_x'''(t) = (9/2)v - 2pi v exp(2v)(1+6v+4v^2).

Since u>=u0, |t-c|<=h0, and

    u |t-c| <= L exp(-u)/sqrt(2pi),
    2(v-u) <= sqrt(2/pi) L exp(-u0) exp(h0) = D0,

we have v<=u exp(h0) and exp(2v)<=exp(2u+D0). Moreover,

    1+6v+4v^2 <= (3/2) exp(2h0)(1+2u)^2.

Divide the two terms in the absolute third derivative by
[x(1+2u)]^(3/2). The exponential term is bounded using

    sqrt((1+2u)/x) = sqrt((2+1/u)/pi) exp(-u)
                  <= sqrt((2+1/u0)/pi) exp(-u0).

For the other term, u/(1+2u)^(3/2)<=1/2 gives the second term of C0.
Also, 1+(9/2)u <= (11/2)u for u>=1 proves the bound on lambda.
The lower bound on A follows because x(1+2u)>=(9/2)u for x>=256.
All replacements are one-sided inequalities on the full unbounded domain.

Taylor's theorem now gives

    |p_x(c+s/sqrt(A))-p_x(c)-lambda*s+s^2/2| <= C0 |s|^3/6.

Set R0=C0 L^3/6 and d0=L-a0-C0 L^2/2. The code requires d0>0.
Taylor's theorem applied to the first derivative gives inward standardized
slope magnitudes at both endpoints at least d0. Global phase concavity then
bounds the entire outer tails by the endpoint tangent lines.

## Full moment error

On the central interval the amplitude defect is at most

    B0 = 3/(2pi) exp(-2u0 exp(-h0)).

Thus the relative central-integral error is at most exp(R0)-1+B0.
This follows from |b exp(r)-1| <= exp(R0)-1+B0 for |r|<=R0 and
1-B0<=b<=1. Positivity of all central weights allows this pointwise bound
to be integrated relative to Q_k.

The integral defining Q_k, after removing its common scale and (2c)^k,
is at least

    H_k = 2 exp(-a0-1/2)(1-z0)^k,

by retaining only -1<=s<=1. At either tail endpoint the normalized phase is
at most a0 L-L^2/2+R0. With outward standardized distance v>=0,

    |t|/c <= 1+L z0+v z0.

Integrating the tangent exponential times this polynomial bounds the combined
absolute tails, relative to Q_k, by

    T_k = 2 exp(a0 L-L^2/2+R0)/H_k
          sum_{j=0}^k [k!/(k-j)!]
            (1+L z0)^(k-j) z0^j / d0^(j+1).

This includes the possibly negative left tail for k=1. Therefore

    |J_k(x)/Q_k(x)-1| <= sigma_k = exp(R0)-1+B0+T_k

for every x>=X and k=0,1,2, whenever the stated checks succeed. A bound above
1 remains a valid approximation bound but cannot establish positivity of J_k
from Q_k alone. The output deliberately makes no positivity or curvature claim.

## Evaluated constants and limitations

With L=8, upper bounds for all three moment orders, rounded upward, are:

| Uniform domain | Maximum relative error bound |
|---|---:|
| Every real x>=65536 | 31.574 |
| Every real x>=10^8 | 0.109119 |
| Every real x>=10^12 | 0.001281 |

Exact rational upper bounds and intermediate constants are saved in
`certified_xi/uniform_saddle.json`. These are evaluated analytic inequalities,
not an inference from sampled moment agreement.

There are three concrete obstructions to using this model unchanged:

1. The cubic phase estimate loses cancellation and decays too slowly for the
   existing curvature transfer. If all three zeroth-moment relative errors
   are bounded by sigma<1, that transfer uses a log-q error of at most
   -4 log(1-sigma). For a positive reference qhat, its upper endpoint is
   qhat/(1-sigma)^4. Keeping this endpoint below 1 requires
   sigma < 1-qhat^(1/4). This is a requirement of this particular error
   enclosure, not a necessary condition on correlated true moment errors.
2. Replacing b by 1 leaves an amplitude error that must be removed or expanded
   accurately before seeking a much sharper curvature estimate.
3. A fixed L leaves a positive tail-error floor as X tends to infinity.
   For unbounded curvature control, the window must grow with the parameter,
   or the Gaussian tails must be included in the model with sharper error
   treatment. Merely increasing X with L fixed cannot finish the proof.

The next useful improvement is a higher-order phase model with the amplitude
retained, combined with a growing-window analysis and coupled neighbor errors.
Arbitrary-order coefficient expansions exist in
[O'Sullivan, Theorem 1.4](https://arxiv.org/html/2007.13582v2), but their stated
asymptotic error terms are not substituted for the explicit continuous moment
bounds needed here.

## Validation and trust boundary

Replay:

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/uniform_saddle.py --output research/certified_xi/uniform_saddle.json
uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/certified_xi -p 'test_*.py'
```

Four new tests cover invalid domains and failed tangent decay, local derivative
checks against the global constants, independent integration against the
quadratic model, and precision restoration. The independent integration checks
use x=65536 and 10^6. A trial of the older localized quadrature at x=10^8 failed
its positive-moment/error check; no integral certificate at that point is claimed.
The analytic uniform constants require no such quadrature.

The proof above is mathematical prose with FLINT evaluation of constants;
it is not Lean formalized. Tests are regression checks of the implementation,
not the justification for the unbounded quantifier.

Validated with 45 certified-Xi tests passing, saved source hashes and all
reported error ceilings verified, and `git diff --check` passing. No Lean
source was changed in this continuation.
