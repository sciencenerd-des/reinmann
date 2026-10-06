# Higher-order saddle errors with a growing window

## Result and scope

The first-summand moment approximation now uses a degree-16 phase, retains
the exact amplitude, and has standardized radius L(x)=sqrt(32u), where
u=W(2x/pi)/2. Its explicit relative error bounds hold for **every real x>=X**.
Both the central error and the infinite-tail error tend to zero as the
threshold increases; the fixed-window error floor has been removed.

| Uniform domain | Relative error upper bound for all k=0,1,2, rounded up |
|---|---:|
| x>=10^6 | 8.215e-22 |
| x>=10^8 | 1.184e-34 |
| x>=10^12 | 1.374e-61 |

After including the omitted theta summands and model quadrature errors, the
true log-epsilon curvature is certified negative at x=100000001. At x=1000001,
the error enclosure contains zero and the outcome is recorded as unresolved.
Neither result establishes a uniform curvature sign. The uniform interior
rank budget remains open, and the earlier shift-one boundary result is unchanged.

Exact rational bounds, intermediate constants, input source hashes, and both
point outcomes are in `certified_xi/high_order_saddle.json`.  The file is
123 MB, above GitHub's file-size limit, so it is not tracked; regenerate it
with the replay command below.  SHA-256 of the run recorded here:
`94c052b4fc5512b5c5e9438665423688ad7ec0da7572aa59de25b099e85d222c`.

## Model definition

Retain the phase p_x(t), amplitude b(t), and center c=log(u) from the preceding
notes. Then x=pi u exp(2u), A=-p_x''(c)=2x(1+2u)-(9/2)u, and
lambda=p_x'(c)/sqrt(A)=(1+(9/2)u)/sqrt(A). For degree p define

    P_p(s) = sum_{j=1}^p p_x^(j)(c) s^j / (j! A^(j/2)),
    L = sqrt(K u),
    Q_k(x) = 4pi^2 exp(p_x(c))/sqrt(A)
             integral_{-L}^L exp(P_p(s)) b(c+s/sqrt(A))
                              [2(c+s/sqrt(A))]^k ds.

The implemented defaults are p=16 and K=32. These are three independently
specified moment models, not derivatives of Q_0 with respect to x. In
particular, differentiating the moving-window integral would introduce
boundary and model-dependence terms. The code does not make that substitution.

The phase coefficients use the exact Touchard polynomial identity, for j>=2:

    p_x^(j)(t) = (9/2) exp(t) - pi exp(2 exp(t)) T_j(2 exp(t)),
    T_j(z) = sum_{i=0}^j S(j,i) z^i,
    S(j+1,i) = i S(j,i) + S(j,i-1).

It follows by repeatedly applying z*d/dz to exp(z). The linear-in-t part of
p_x has vanished for j>=2. This integer recurrence is implemented directly;
no fitted coefficients or symbolic black-box approximation is used.

## Uniform bounds on the growing window

Let u0=W(2X/pi)/2, X>=65536, and put

    L0 = sqrt(K u0),
    h0 = L0/sqrt(X(1+2u0)),
    z0 = 1/[sqrt(X(1+2u0)) log(u0)],
    D0 = 2u0 h0 exp(h0).

The code checks u0>=3/2, L0>=2, and L0 z0<1. On the entire domain x>=X,
A>=x(1+2u), and the actual half-width L/sqrt(A) is bounded by

    h(u) = sqrt(K/pi) exp(-u)/sqrt(1+2u) <= h0.

Both h(u) and u h(u) decrease for u>=3/2. Thus, if |s|<=L and
v=exp(c+s/sqrt(A)), then v<=u exp(h0) and

    2(v-u) <= 2u h(u) exp(h0) <= D0.

All positive central logarithmic weights are bounded away from zero because
L/[sqrt(A)c] <= h0/log(u0) = L0 z0 < 1.

Let B_n=sum_i S(n,i) be the n-th Bell number. Positivity of the coefficients
and i<=n imply

    T_n(2v) <= exp(n h0) B_n (1+2u)^n.

Using A>=x(1+2u), the absolute n-th standardized derivative is at most

    B_n exp(n h0+D0) (2+1/u)^(n/2) pi^(1-n/2) exp(-(n-2)u)
      + (9/4) exp(h0) x^(-n/2),                 n>=3.

The first term follows by substituting x=pi u exp(2u); the second uses
u/(1+2u)^(n/2)<=1/2. Multiplying by L^n/n!, with n=p+1, bounds the Taylor
remainder throughout the window by R_n(u), where

    R_n(u) = B_n exp(n h0+D0) (2+1/u0)^(n/2) pi^(1-n/2)
              (K u)^(n/2) exp(-(n-2)u)/n!
             + (9/4) exp(h0) (K/pi)^(n/2) exp(-n u)/n!.

For n>=3 and u>=3/2, u^(n/2) exp(-(n-2)u) is nonincreasing: its logarithmic
derivative is n/(2u)-(n-2)<=0. Therefore R_n(u)<=R_n(u0)=R0, the constant
evaluated by the program. This gives a uniform central relative error
exp(R0)-1 because the amplitude is retained exactly and is positive.

## Infinite tails without a fixed-radius floor

Use the tighter third-derivative estimate from the quadratic note:

    C3(u) = 3 exp(3h0+D0) sqrt((2+1/u)/pi) exp(-u)
             + (9/4) exp(h0) x^(-3/2),
    a0 = 11 exp(-u0)/(2 sqrt(2pi)),
    B = C3(u0) L0, r = a0/L0,
    tau = 1/2-r-B/6, d = 1-r-B/2.

The code requires tau>0 and d>0. The product C3(u)L(u) decreases: its first
term is proportional to sqrt(2u+1) exp(-u), and its second to exp(-3u)/u.
Also lambda/L<=r. Taylor's theorem at the two window endpoints consequently
bounds the true normalized phase above by -tau L^2=-tau K u and the inward
standardized tangent-slope magnitudes below by d L.

Global phase concavity extends these endpoint tangents over both entire tails.
The same polynomial-tail integration as in the earlier note applies. Its
nonexponential factors are bounded using

    1/(sqrt(A)c) <= z0,
    L/(sqrt(A)c) <= L0 z0,
    1/(d L) <= 1/(d L0).

To lower-bound the model integral, retain only |s|<=1. The exact phase there
is at least -a0-1/2-C3(u0)/6; the Taylor model is at least this minus R0.
The amplitude is at least 1-b0, where

    b0 = 3/(2pi) exp(-2u0 exp(-h0)),
    H_k = 2 exp(-a0-1/2-C3(u0)/6-R0)(1-b0)(1-z0)^k.

After dividing out the common scale and (2c)^k, the model mass is at least H_k.
Both absolute tails relative to Q_k are bounded by

    T_k(u) = 2 exp(-tau K u)/H_k
              sum_{j=0}^k [k!/(k-j)!]
                (1+L0 z0)^(k-j) z0^j/(d L0)^(j+1).

In particular T_k(u)<=T_k(u0). The full uniform first-summand moment bound is

    |J_k/Q_k-1| <= exp(R0)-1+T_k(u0),       k=0,1,2.

The potentially negative k=1 left tail is bounded in absolute value; no
positivity of that tail is assumed. The denominator model moment is positive
by the checked central-domain conditions. Unlike the fixed-window calculation,
the pointwise envelope exp(R_n(u))-1+T_k(u) tends to zero with u.

## Error propagation and the unresolved sign

The finite model integral is computed in the s coordinate, directly from its
Taylor coefficients, avoiding subtraction of huge phase values inside the
integrator. If sigma is the analytic model error, eta the omitted-theta error,
and qerr the model quadrature error, the combined moment error relative to
the computed model midpoint is at most

    (1+sigma)(1+eta)(1+qerr)-1.

This bound is propagated through the existing three-neighbor log-moment and
curvature calculation. The numerical results, shown approximately, are:

| x | True curvature enclosure | Status |
|---|---|---|
| 1000001 | [-1.327e-13, 1.166e-13] | unresolved |
| 100000001 | [-4.227207e-19, -4.227156e-19] | certified negative at this point |

The second enclosure has propagated error below 2.498e-24. The unrounded
rational certificate is authoritative. These outcomes establish neither a
uniform sign for the model curvature nor a compact bridge to earlier intervals.
The distinction matters: a uniform approximation bound and one negative model
evaluation do not imply negativity at every unbounded parameter.

The next mathematical obligation is uniform sign control of the algebraic
curvature expression built from the three model-moment triples. One possible
route is a finite Gaussian-moment expansion with explicit remainders and
coupled neighboring-parameter differences. This remains to be carried out.
The all-rank interior recurrence budget remains a separate unproved obligation.

## Replay and validation

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/high_order_saddle.py --output research/certified_xi/high_order_saddle.json
uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/certified_xi -p 'test_*.py'
```

New tests cover exact Stirling/Bell coefficients and rejected domains,
decreasing central and tail bounds, an independent exact-phase integral
(using stable expm1 differences rather than the Taylor polynomial), and both
the negative and unresolved curvature outcomes. Regression tests do not prove
the uniform quantifier; the analytic inequalities above do that work.
The trust boundary is mathematical prose plus FLINT balls, not Lean formalization.

Validated with 49 certified-Xi tests passing, saved source hashes and all
reported numerical ceilings checked, both point classifications verified,
and `git diff --check` passing. No Lean source changed in this continuation.
