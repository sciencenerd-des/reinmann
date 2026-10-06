# Closed Weil entries and a whole support-cell Taylor certificate

The [point derivative audit](SMOOTH_SUPPORT_DERIVATIVE_2026_10_05.md)
does not bound a ground-profile derivative throughout a support interval.
This step supplies a common analytic matrix expansion on the entire cell
`17<=C<=19`. It preserves the common support parameter through coefficient
arithmetic, so a later eigenpair residual can be formed before evaluating
the parameter interval. A validated eigenpair family is still needed.

## Exact closed entry formula

Let `L=log C`, `w_n=2*pi*n/L`, `a_k=2k+1/2`, and
`z_n=1/4-i*w_n/2`. Write a Weil entry as `W_mn=P_mn-H_mn-S_mn`,
where `S` is the explicit finite prime-power sum from the original
[integral implementation](../../experiments/prime_spectral/certified_weil.py).
The [closed implementation](../../experiments/prime_spectral/closed_weil.py)
uses

```
P_nn = 4/L * (cosh(L/2)-1) * (1/4-w_n^2)/(1/4+w_n^2)^2,

P_mn = 2*(cosh(L/2)-1)/(pi*(m-n))
       * [w_m/(1/4+w_m^2)-w_n/(1/4+w_n^2)],       m!=n,

H_nn = log pi - Re psi(z_n) - Re psi'(z_n)/(2L)
       + (2/L) sum_(k>=0) exp(-a_k L)
                       * (a_k^2-w_n^2)/(a_k^2+w_n^2)^2,

H_mn = [Im psi(z_m)-Im psi(z_n)]/[2*pi*(m-n)]
       + sum_(k>=0) exp(-a_k L)/(pi*(m-n))
                     * [w_m/(a_k^2+w_m^2)-w_n/(a_k^2+w_n^2)],  m!=n.
```

These follow from
`exp(z/2)/(2*sinh z)=sum_(k>=0)exp(-(2k+1/2)z)`, the endpoint identity
`exp(i*w_n*L)=1`, and the established digamma integral and trigamma
series. See [DLMF 5.9.16](https://dlmf.nist.gov/5.9.E16) and
[DLMF 5.15.1](https://dlmf.nist.gov/5.15.E1).
On the diagonal, the regularization constant is **log pi**. In detail,
the singular integral contributes `-log(2*epsilon)-gamma-Re psi(z_n)`;
the original analytic tail contributes `log(epsilon/2)`; and the
remaining constant is `log(4*pi)+gamma`. Their sum is
`log pi-Re psi(z_n)`. This checks the normalization against the original
archimedean formula rather than introducing a fitted constant.

The [17/8 comparison certificate](closed_weil_17_8.json) checks diagonal,
off-diagonal, opposite-index and neighboring-index cases against the
independent certified integrals. The tests also check cutoffs `2,13,19`.

## A remainder uniform in every Fourier index

Put `g_a(w)=w/(a^2+w^2)`. For real `w`,

```
|g_a'(w)| = |(a^2-w^2)/(a^2+w^2)^2| <= 1/a^2.
```

The mean-value theorem then gives

```
|[g_a(w_m)-g_a(w_n)]/[pi*(m-n)]| <= 2/(L*a^2).
```

Thus the off-diagonal divided difference retains the cancellation
between neighboring indices. Both its omitted exponential series and
the diagonal series have the same absolute tail bound after `K>=1`
terms:

```
tau(L,K) = 2*exp(-(2K+1/2)*L)
           / [L*(2K+1/2)^2*(1-exp(-2L))].
```

This bound holds for **all integer index pairs**, independently of
Fourier rank. A full matrix of dimension `d` therefore has operator
tail error at most `d*tau(L,K)`, by the symmetric row-sum bound.
The tests exercise indices `1000,999,-1000` with a short tail and
check enclosure of the refined formula; those checks support the
implementation, while the displayed argument proves the index-uniform
tail estimate.

An effective cumulative budget for this **evaluation remainder** follows.
For `L>=L0>0`, put `A=2/[L0*(1-exp(-2L0))]`. Since
`tau(L,K)<=A*exp(-2K*L0)`, dimensions `d_r` and a tolerance `epsilon>0`
can use

```
K_r = max(1, ceil([log(d_r*A/epsilon)+r*log 2]/(2L0))),  r>=1.
```

Then the sum of all matrix evaluation errors is at most `epsilon`.
This controls truncation of the archimedean evaluation series. It does
not control an eigenvector response or prove the rank budget required
for convergence to Xi.

## Holomorphic continuation and derivative remainders

Replace `Re psi(z_n)` by the symmetric expression
`[psi(1/4-i*pi*n/L)+psi(1/4+i*pi*n/L)]/2`; replace imaginary parts
by the corresponding antisymmetric expression divided by `2i`.
This gives a holomorphic fixed-prime branch on `Re L>0`. All possible
rational and polygamma poles occur on the imaginary `L` axis. The
finite prime sum is holomorphic there as well.

On `|L-c|<=R<c`, set `ell=c-R`, `M_L=c+R`. For real index parameter
`s` and `a>0`,

```
|1/(a +/- i*2*pi*s/L)| <= M_L/(a*ell).
```

Writing `g_a'` as half the sum of these two reciprocal squares
proves the complex version of the same divided-difference bound.
Consequently the omitted exponential series is bounded, uniformly
over all integer index pairs and the whole disk, by

```
B_K(c,R) = 2*M_L*exp(-(2K+1/2)*ell)
           / [ell^2*(2K+1/2)^2*(1-exp(-2ell))].
```

Cauchy's formula bounds its coefficient of `(L-c)^j` by `B_K/R^j`.
The [Taylor generator](../../experiments/prime_spectral/weil_support_taylor.py)
adds that error to every coefficient; it does not differentiate an
uncontrolled numerical tail. Polygamma values supply the coefficients
of the composed digamma functions. Circle arcs are covered by Arb
rectangles to enclose a Cauchy bound `M` for the complete entry.
Digamma on those rectangles is enclosed by its midpoint value and a
trigamma mean-value bound, avoiding wide-ball dependency loss.

For degree `D`, displacement `|h|<=delta<R`, and `q=delta/R`,

```
|W(c+h)-sum_(j=0)^D W_j*h^j| <= M*q^(D+1)/(1-q),

|W'(c+h)-sum_(j=1)^D j*W_j*h^(j-1)|
    <= (M/R)*q^D*[(D+1)-D*q]/(1-q)^2.
```

These are whole-cell analytic estimates, not interpolation errors
estimated from sampled points.

## Certified entire 17–19 cell and boundary control

The [full even-block certificate](weil_support_taylor_17_19_8.json)
contains all `9 x 9` coefficient matrices through degree `48`, at
`c=(log 17+log 19)/2`, with analytic radius `1/4` and `80` exponential
terms. The entire interval has half-width approximately `0.0556128`.
The outward operator remainder bounds are

```
matrix value:       < 1.355e-30,
matrix derivative:  < 1.201e-27.
```

The active prime branch includes `17` and excludes `19`. Its values
are continuous at both endpoints because the endpoint correlation
vanishes. Its derivatives are the right derivative at `17` and the
left derivative at `19`. The [boundary tests](../../experiments/prime_spectral/test_weil_support_taylor.py)
compare every even entry and derivative against independently computed
certified matrices at **both** boundaries. The existing rank-one jump
certificates provide the other one-sided derivatives.

The [subsequent even-eigenfamily certificate](WEIL_EVEN_EIGENFAMILY_CELL_2026_10_05.md)
validates polynomial candidates through a complete 32-subcell cover.
It also repairs coefficient precision loss in the installed series sine
and cosine operations using exact exponential identities. The global step
remains a bound on the ground-profile response
across every support cell and rank, plus identification of the limit
with Xi. These matrix Taylor bounds do not imply those conclusions,
uniform theta-curvature negativity, or RH.

Replay:

```sh
uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/prime_spectral -p test_closed_weil.py -v
uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/prime_spectral -p test_weil_support_taylor.py -v
```
