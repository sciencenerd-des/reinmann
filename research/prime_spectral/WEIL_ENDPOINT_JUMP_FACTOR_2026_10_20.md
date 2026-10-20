# Endpoint jump sources in the per-prime window comparison

The proposed per-prime comparison remains open. This round isolates an exact
rank-two jump factorization and tests its constant-vector tail on actual DH
coefficients **before** zeta. It certifies no new positive window and does not
supply the complete Schur energy needed by the certificate.

## Exact jump structure

Use additive window [0,L], L=log(C), and a_n=log(n). Let

    S v = sum_{n<C} w_n [1_{x>=a_n} v(x-a_n)
                         + 1_{x<=L-a_n} v(x+a_n)].

For zeta, w_n=Lambda(n)/sqrt(n); for the DH diagnostic, use its actual
logarithmic-derivative coefficients c_n/sqrt(n), including non-prime powers.
The gamma, conductor and pole pieces are not being modified or certified by
this shift-source experiment.

For a continuous v, the interior jump at a_n is w_n v(0), and that at L-a_n is
-w_n v(L). At coincident positions their amplitudes must be added before
squaring. Define G_0=sum w_n 1_{x>=a_n} and
G_L=sum w_n 1_{x<=L-a_n}. Then

    S v - v(0) G_0 - v(L) G_L

is continuous at every interior breakpoint. This is an exact identity about
jumps, for each continuous v; the leading jump map factors through its two
endpoint values. Subtracting endpoint jets similarly removes derivative
jumps. This is ordinary piecewise-smooth approximation theory, not a new
arithmetic positivity theorem.

## An exact coefficient formula and a fixed-window asymptotic

For v=1/sqrt(L), the degree-k normalized Legendre coefficient (k>=1) of S v is

    b_k = (1+(-1)^k) / (2 sqrt(2k+1))
          * sum_n w_n [P_{k-1}(t_n)-P_{k+1}(t_n)],
    t_n = 2 log(n)/L - 1.

It follows by integrating the Legendre derivative identity. For distinct
merged interior jumps j_r of the unnormalized function sqrt(L) S v at x_r,
classical [fixed-interior Legendre asymptotics](https://dlmf.nist.gov/18.15.iii)
and summation of oscillatory 1/k^2 terms give

    sum_{k>N} |b_k|^2 ~ K(C)/N,
    K(C) = (1/(2 pi)) sum_r |j_r|^2 sqrt(1-(2 x_r/L-1)^2).

For a fixed window with no coincident breakpoints this becomes

    K(C) = (1/pi) sum_{n<C} w_n^2 sqrt(1-t_n^2).

The result is for a fixed finite jump set. The constants in a remainder need
not be uniform as breakpoints approach one another or the endpoints.
At C=4 the n=2 source is constant, so its two coincident jumps cancel; a
formula that squares them separately is wrong. The probe includes that case.

## DH-first finite-band diagnostic

`weil_endpoint_jump_probe.py` evaluates the exact coefficient formula and
compares it with independent real-space quadrature at four low degrees.
It computes only finite dyadic bands N<k<=2N; it does not replace an unknown
infinite tail by its asymptotic. The ratio tested is
`2N sum_{N<k<=2N}|b_k|^2 / K(C)`, predicted to tend to 1.

| C | DH K(C) | zeta K(C) | ratio at N=32768, DH / zeta |
|---|---:|---:|---:|
| 4 | 0.00838203 | 0.10386541 | 0.999926 / 0.999926 |
| exp(2) | 0.29484504 | 0.42208272 | 0.999862 / 1.000156 |
| 9.5 | 0.40351136 | 0.52585151 | 0.999839 / 1.000045 |
| 19 | 0.83690198 | 0.90782663 | 0.999862 / 1.000854 |

These are floating diagnostics, not interval certificates. They validate the
normalization and expose the same algebraic leakage in DH. The lemma is a
shared prerequisite, not an RH separator.

Reproduction uses Python 3.12.11 with python-flint 0.8.0, NumPy 2.5.4,
SciPy 1.18.1 and mpmath 1.4.1; the exact environment and JSON output are retained
in `verification_2026_10_20_research_gates/`. One isolated invocation is:

```sh
uv run --no-project --python 3.12 --with python-flint==0.8.0 \
  --with numpy==2.5.4 --with scipy==1.18.1 --with mpmath==1.4.1 \
  python experiments/prime_spectral/weil_endpoint_jump_probe.py \
  --output /absolute/path/to/new-endpoint-jump-probe.json
```

## What this does and does not decide

For this source the leading coefficient is a sum of squared weights, rather
than the square of the comb norm. Thus jumps alone do not prove the proposed
kill criterion that every comparison must pay A_L. But their 1/N tail is still
far too large for the exponentially small positive margins if treated through
a crude coupling norm. Merely replacing A_L by K(C) in the existing symbol
comparison is invalid: these are different quantities and different bounds.

## Removing the two jump profiles: a second DH-first test

Take v(x)=sqrt(3/L)*(2x/L-1), and set R=S v-v(0)G_0-v(L)G_L.
With t=2x/L-1 and t_n=2log(n)/L-1, its exact piecewise-linear expression is

    sqrt(L) R = sqrt(3) sum_n w_n
        [(t-t_n) 1_(t>=t_n) + (t+t_n) 1_(t<=-t_n)].

For k>=2 let

    I_k(t) = [(P_(k-2)(t)-P_k(t))/(2k-1)
              -(P_k(t)-P_(k+2)(t))/(2k+3)]/(2k+1).

Integrating twice gives I_k(t)=integral_t^1 (u-t)P_k(u)du. Thus the corrected
normalized coefficient is exactly

    a_k = sqrt(3*(2k+1))/2 * (1-(-1)^k) sum_n w_n I_k(t_n).

For merged jumps d_r in the t-derivative of sqrt(L) R, the same fixed-interior
Legendre calculation gives the classical tail constant

    sum_(k>N) |a_k|^2 ~ K_3/N^3,
    K_3 = (1/(6*pi)) sum_r |d_r|^2 (1-t_r^2)^(3/2).

Before merging, d_r is sqrt(3)w_n at t_n and its negative at -t_n. Coincident
jumps again have to be combined. At C=4 the n=2 corrected source is globally
linear and contributes no coefficient for k>=2, as the formula predicts.

`weil_endpoint_jet_probe.py` checks the exact coefficients against independent
quadrature and computes finite dyadic bands, DH first. The last-band ratio
`8N^3 sum_(N<k<=2N)|a_k|^2/(7K_3)` at N=32768 is 0.999678 for DH at C=9.5
and 1.000239 for zeta. All eight fixed-window cases are recorded in
`endpoint_jet_probe.json`. This is numerical confirmation of normalization
and the expected change from 1/N to 1/N^3 after the jump subtraction; it is
not a certified infinite-tail remainder. The isolated environment is the same
as above, with the probe filename changed.

This test is a concrete smoothing result for the coupling source of one low
vector. It does not show that enlarging the trial space by G_0 and G_L has a
positive compressed block, or that its whole complement has a usable inverse.
Applying S to the new directions can generate further shifted breakpoints.
Consequently it is not a closed finite-dimensional invariant space or a
complete per-prime certificate strategy.

The endpoint-source decomposition suggests adding a finite number of explicit
jump directions, then estimating the smoother remainder with all arithmetic
weights retained. It does not solve the new directions' own couplings, their
archimedean singularities, or coercivity on the full complement. Boundary
traces are not bounded on the unrestricted logarithmic form domain, so a
uniform operator estimate cannot be inferred from this finite-vector identity.
The shifts by log(2) and log(3) still have no common finite invariant partition.

The next acceptance test is a bound on the **complete** operator Schur energy
for an enlarged finite space, including these directions and their new cross
terms, on the actual form domain. Until that bound is proved and tested on DH,
this remains finite-certificate engineering with an open bottleneck. No
frontier, polynomial-cost or all-window claim follows from this probe.
