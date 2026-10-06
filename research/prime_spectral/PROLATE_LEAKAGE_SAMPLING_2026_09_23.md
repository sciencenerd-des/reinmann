# Sampling the prolate Fourier leakage outside the window

The [two-constraint audit](PROLATE_TWO_CONSTRAINT_DEFECT_2026_09_23.md)
left one analytic sampling term open. For the zero-integral prolate
combination `f=h_I`, extended by zero outside `[-lambda,lambda]`, put
`g=Ff` and `ell=1_(|y|>lambda)*g`. The concentration theorem makes
`||ell||_2` exponentially small, but `E(ell)(u)` samples infinitely
many values of `ell`; an `L2` bound alone cannot be substituted for
that sum. The special Fourier-transform structure of `ell` does give
a bound.

Throughout, `C=lambda^2` is an integer tending to infinity,
`u in [lambda^(-1),lambda]`, and `F` uses the unitary kernel
`exp(2*pi*i*x*y)`. The prolate modes are scaled as in
[Connes–Consani–Moscovici, Lemma 7.2](https://arxiv.org/html/2511.22755v1),
so they converge uniformly to the corresponding unit Hermite
functions with error `O(lambda^(-2))`. The explicit concentration
deficits from [Karnik–Romberg–Davenport, §3.2](https://arxiv.org/html/2006.00427)
are denoted `B_0,B_4` in the two-constraint audit.

## The finite-frequency part

The exact orthogonal leakage identity gives

```
||ell||_2^2 <= B_4+r^2*B_0
             =O(C^(7/2)*exp(-2*pi*C)),                 (1)
```

because the center ratio `r` stays bounded by the Hermite limit.
Also `||g'||_2=2*pi*||x f||_2<=2*pi*lambda*||f||_2=O(sqrt C)`.
For `y>=lambda`, the fundamental theorem of calculus and
Cauchy-Schwarz on `[y,infinity)` give

```
|g(y)|^2 <= 2*||ell||_2*||g'||_2,
sup_(y>=lambda)|g(y)|
    =O(C^(9/8)*exp(-pi*C/2)).                         (2)
```

Here `g(y)->0` at infinity because `f` is integrable and compactly
supported. For any splitting frequency `Y>=lambda`, there are at most
`Y/u` positive integers with `lambda<n*u<=Y`. Therefore

```
sqrt(u)*sum_(lambda<n*u<=Y)|g(n*u)|
    <= Y/sqrt(u)*sup_(y>=lambda)|g(y)|
    =O(Y*C^(11/8)*exp(-pi*C/2)),                     (3)
```

uniformly in the support window, since `u>=lambda^(-1)`.

## The infinite-frequency tail

For real even `f` that is `C^2` on the closed interval, two integrations
by parts in `g(y)=2*integral_0^lambda f(x)cos(2*pi*x*y)dx` give

```
g(y)= f(lambda)*sin(2*pi*lambda*y)/(pi*y)+R(y),
|R(y)| <= A/(2*pi^2*y^2),
A=|f'(lambda)|+integral_0^lambda |f''(x)|dx.      (4)
```

The boundary term at zero involving `f'(0)` vanishes by evenness.
The published uniform prolate-to-Hermite estimate and Gaussian decay
give the preliminary endpoint bound

```
|f(lambda)|=O(C^(-1)).                             (5)
```

The concentration estimate gives a stronger bound after the
polynomial sup estimate below.

We also need only a *polynomial* upper bound for `A`. In the scaled
variable `z=x/lambda`, each component `H` of `f(lambda*z)` solves
`-[(1-z^2)H']'+c^2*z^2*H=chi*H`, with `c=2*pi*C` and
`chi+c^2<=T=20+2*c^2`. Let `M=||H||_infinity`.
The regular endpoint condition gives, for `0<=z<1`,

```
H'(z)=Gbar(z)/(1+z),
Gbar(z)=(1-z)^(-1)*integral_z^1 (chi-c^2*s^2)*H(s)ds.
```

Hence `||H'||_infinity<=T*M`. If
`G(s)=(chi-c^2*s^2)*H(s)`, then
`Lip(G)<=(2*c^2+T^2)*M` and the derivative of its interval average
satisfies `|Gbar'(z)|<=Lip(G)/2`. The same argument at `-1` yields

```
||H''||_infinity
  <= (c^2+T^2/2+T)*M.                            (6)
```

The min-max and elementary sup bounds in the
[finite-Fourier diagonal](PROLATE_FOURIER_DIAGONAL_2026_09_23.md)
give `M=O(sqrt(T)*lambda^(-1/2))=O(C^(3/4))` for each normalized
low prolate mode. Applying (6) to both components of `f` gives
`||H''||_infinity=O(C^(19/4))`, where `19/4=4+3/4`.
Since `f''(x)=H''(x/lambda)/lambda^2`, integration over
`[0,lambda]` and the corresponding first-derivative bound yield

```
A=O(C^(17/4)).                                   (7)
```

In fact the endpoint value is exponentially small. Write
`d=P_lambda*g-f`. The compressed-Fourier eigenvalue equation and
`||psi_j||_infinity=O(C^(3/4))` give

```
|d(lambda)| <= (1-theta_4)*|psi_4(lambda)|
               +|r|*(1-theta_0)*|psi_0(lambda)|
             =O(C^(17/4)*exp(-2*pi*C)).
```

The estimate (2) holds at `y=lambda` by continuity of `g`, and
`g(lambda)=f(lambda)+d(lambda)` using the interior endpoint values
of `f` and `d`. Therefore

```
|f(lambda)|=O(C^(9/8)*exp(-pi*C/2)).              (7a)
```

An elementary Dirichlet-series estimate gives, for every real
`theta` and integer `M>=0`,

```
|sum_(n>M) sin(n*theta)/n| <= 10.                 (8)
```

For completeness, reduce `theta` modulo `2*pi`, using a sign change if
needed, to `[0,pi]`. At `theta=0` or `pi` the sum vanishes. Otherwise
put `m=floor(1/theta)`. The part through `m` is at most `m*theta<=1`
because `|sin(n*theta)|<=n*theta`. Every partial sum of the part from
`m+1` onward is bounded by `1/((m+1)*sin(theta/2))`: apply summation
by parts to the geometric-sum estimate
`|sum_(n=p)^q sin(n*theta)|<=1/sin(theta/2)`. Since
`m+1>1/theta` and `sin(theta/2)>=theta/pi`, this is below `pi`.
The same bound covers `m=0`. Thus every initial partial sum has
absolute value at most `1+pi`, and the difference of any two initial
partial sums has absolute value below `2*(1+pi)<10`. This also proves
convergence by the Dirichlet test.

Now choose `Y=exp(pi*C/4)`. For integer `C>=2`, one has `Y/u>=2`
throughout the support window. Let `M=floor(Y/u)`, so
`M>=Y/(2*u)`. The leading term of (4), summed over `n>M`, is at most
`10*|f(lambda)|/(pi*sqrt(u))` by (8); the remainder contributes at
most `A/(pi^2*Y*sqrt(u))`. Uniformly in the support window,

```
sqrt(u)*|sum_(n*u>Y) g(n*u)|
  <= 10*|f(lambda)|*sqrt(lambda)/pi
     + A*sqrt(lambda)/(pi^2*Y)
  = O(C^(11/8)*exp(-pi*C/2))
    +O(C^(9/2)*exp(-pi*C/4)).                        (9)
```

The sine series converges conditionally, while the remainder is
absolutely summable. At a sample with `n*u=lambda`, take half of the
limiting value of `ell` from above; use the same midpoint convention
for `f` and for the split `P_lambda*g+ell`. There is at most one such
positive integer, and its extra contribution is bounded by
`sqrt(lambda)*sup_(y>=lambda)|g(y)|/2`, which is absorbed in (3).
Thus `E(ell)(u)` is well defined by increasing integer cutoffs, and
(3) plus (9) prove

```
sup_(lambda^(-1)<=u<=lambda)|E(ell)(u)|
   = O(C^(9/2)*exp(-pi*C/4))                       (10)
```

with the ordinary midpoint convention at any jump location.

## Consequence for inversion and the remaining RH gate

Poisson summation for the compactly supported piecewise smooth input,
with the midpoint convention just stated, gives
for `integral f=0`

```
E(f)(u)-E(f)(u^(-1))
  =-E(P_lambda Ff-f)(u)-E(ell)(u)+f(0)/(2*sqrt(u)). (11)
```

The compressed term also has a pointwise bound:
`||d||_infinity=O(C^(17/4)*exp(-2*pi*C))` by the eigenvalue deficits
and the polynomial prolate sup estimate. At most `lambda/u` terms
occur in `E(d)(u)`, so `sup|E(d)|=O(C^5*exp(-2*pi*C))` on the
support window. The exact scalar defect gives
`sup|f(0)/(2*sqrt(u))|=O(C^(15/4)*exp(-2*pi*C))`.
Consequently (10)–(11) imply the uniform approximate inversion law

```
sup_(lambda^(-1)<=u<=lambda)
  |E(f)(u)-E(f)(u^(-1))|
    =O(C^(9/2)*exp(-pi*C/4)).                       (12)
```

On every fixed horizontal strip `|Im z|<=sigma`, the contribution of
this inversion defect to the centered Fourier profile is
`O(C^(9/2+sigma/2)*log(C)*exp(-pi*C/4))`, which tends to zero.

This is an **inversion/profile** estimate for the prolate candidate.
It is not an estimate of the prime-defined Weil quadratic form on
that candidate. No candidate Rayleigh-excess/gap ratio, separation
from the other near-radical modes, or all-support simple-even theorem
follows. Those remain the necessary inputs to the strip transfer and
to RH.
