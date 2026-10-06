# The two prolate constraints and the missing Weil estimate

The current finite candidate uses the `h_(0,lambda)` and
`h_(4,lambda)` combination with **zero integral**, as in
[Connes–Consani–Moscovici, §7](https://arxiv.org/html/2511.22755v1).
The earlier near-radical construction in
[Connes–Consani, §1 and §3](https://arxiv.org/html/2106.01715)
uses the space of even inputs satisfying **both** `h(0)=0` and
`integral h=0`. These conditions agree for a Fourier-invariant
function, but a compactly supported prolate function is only an
eigenfunction of the *compressed* Fourier transform. The difference
has an exact two-mode formula.

## Exact defect identity

Let `P_lambda` restrict to `[-lambda,lambda]`, let `F` be the unitary
additive Fourier transform with kernel `exp(2*pi*i*x*y)`, and let
`psi_0,psi_4` be real orthonormal even eigenfunctions of
`P_lambda F P_lambda` with positive eigenvalues `theta_0,theta_4`.
Write `a_j=psi_j(0)` and `I_j=integral_(-lambda)^lambda psi_j(x)dx`.
Evaluating the compressed Fourier eigenvalue equation at zero gives

```
I_j=theta_j*a_j.                                        (1)
```

Assume `a_0!=0`, so `I_0!=0`. The zero-integral and zero-at-origin
combinations, with the coefficient of `psi_4` fixed to one, are

```
h_I=psi_4-(theta_4*a_4/(theta_0*a_0))*psi_0,
h_Z=psi_4-(a_4/a_0)*psi_0.                             (2)
```

Direct substitution yields

```
h_I(0)=a_4*(1-theta_4/theta_0),
integral h_Z=a_4*(theta_4-theta_0),
h_I-h_Z=(a_4/a_0)*(1-theta_4/theta_0)*psi_0.          (3)
```

Thus the zero-integral condition used by the present candidate does
**not** imply exact vanishing at the origin. If `a_4!=0` and the two
compressed-Fourier eigenvalues differ, no nonzero vector in the span
of these two modes can satisfy both constraints. This is a finite
linear-algebra fact, not an RH assertion.

There is also an exact global Fourier-defect identity. With
`r=theta_4*a_4/(theta_0*a_0)`, extend `h_I` by zero outside the
interval. Orthogonality, unitarity of `F`, and the compressed
eigenvalue equations give

```
||F h_I-h_I||_2^2
    =2*((1-theta_4)+r^2*(1-theta_0)).                  (4)
```

Here the norm is on the whole real line. To verify (4), expand
`||Fh_I-h_I||_2^2=2||h_I||_2^2-2*Re< Fh_I,h_I >` and use
`<F psi_j,psi_k>=theta_j*delta_(j,k)`. The right side makes the
prolate concentration deficit explicit. Small deficits make `h_I`
approximately Fourier invariant in `L2`; they do not by themselves
bound its scale-invariant sum `E(h_I)` or its Weil-form residual.

For an even Schwartz function `f`, Poisson summation gives the exact
endpoint-corrected identity

```
E(f)(u)=E(F f)(u^(-1))
        +(u^(-1/2)*integral f-u^(1/2)*f(0))/2.          (5)
```

The familiar inversion identity follows only when **both** scalar
conditions vanish. A zero-extended prolate function with nonzero
endpoint values is not Schwartz, so it cannot be inserted directly
into the earlier exact-radical theorem. For that function, (5) needs
the usual symmetric or distributional interpretation at its jump
locations; equations (1)–(4) need no such qualification.

## An established effective concentration bound

The nonasymptotic PSWF estimate quoted in
[Karnik–Romberg–Davenport, §3.2](https://arxiv.org/html/2006.00427)
states that the time-frequency concentration eigenvalue of order `j`
obeys

```
1-tilde_lambda_j(c) <= B_j(c)
    := 7*c^(-1/2)*(2*c)^j*exp(-c)/j!,
    0<=j<2*c/2.7.                                        (6)
```

In our normalization the time interval and frequency band are both
`[-lambda,lambda]`, so `c=2*pi*lambda^2=2*pi*C` and
`tilde_lambda_j(c)=theta_j^2` for `j=0,4`. The latter equality follows
by squaring the compressed Fourier transform on the even subspace.
For integer `C>=2`, both indices satisfy the range condition, and

```
B_0(c)=7*c^(-1/2)*exp(-c),
B_4(c)=(14/3)*c^(7/2)*exp(-c).                      (7)
```

Both bounds are below one at `C=2` by Arb evaluation. Their
logarithmic derivatives with respect to `c` are `-1-1/(2c)` and
`-1+7/(2c)`, both negative for `c>=4*pi`; hence they stay below one
for every `C>=2`.
Since `theta_j>0`, equations (3)–(4) now give the explicit estimates

```
|h_I(0)|/|a_4|
   <= (B_0+B_4)/sqrt(1-B_0),
||Fh_I-h_I||_2^2
   <= 2*B_4 + 2*B_0/(1-B_0)*|a_4/a_0|^2.               (8)
```

The first bound is interpreted as `|h_I(0)|=0` when `a_4=0`.
At `C=13`, 256-bit Arb evaluation verifies `B_0<2.61e-36` and
`B_4<7.73e-29`; the exact rational enclosures are in
`prolate_concentration_13.json`. These are established bounds on the
**prolate** compression defect, not measurements of a Weil eigenvalue.
Replay from the repository root:

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/prolate_concentration_bound.py --cutoff 13 --output research/prime_spectral/prolate_concentration_13.json
```

## What the compression deficit does control

There is a direct `L2` bound for `E` **on the finite support window**.
For `f` supported in `[-lambda,lambda]`, set
`K_f(t)=E(f)(exp(t))` on `I=[-log(C)/2,log(C)/2]`. Minkowski's
inequality and `x=n*exp(t)` give

```
||K_f||_(L2(I))
  <= sum_(n=1)^C n^(-1/2)*||f||_(L2(0,lambda))
  <= (2*sqrt(C)-1)*||f||_(L2(-lambda,lambda)).       (9)
```

With `d=P_lambda F h_I-h_I`, the compressed eigenvalue equations show

```
||d||_2^2=(1-theta_4)^2+r^2*(1-theta_0)^2
          <= B_4^2+r^2*B_0^2.                         (10)
```

Thus the centered Fourier functional from the
[finite-Fourier diagonal](PROLATE_FOURIER_DIAGONAL_2026_09_23.md)
satisfies, throughout `|Im z|<=sigma`,

```
|F_z(K_d)| <= sqrt(log C)*H_sigma(log C)
              *(2*sqrt(C)-1)*sqrt(B_4^2+r^2*B_0^2). (11)
```

This is exponentially small up to the explicit factor `r` and the
strip weight. It handles the **in-window** part of the Fourier defect.
The prolate-to-Hermite estimate in
[Connes–Consani–Moscovici, Lemma 7.2](https://arxiv.org/html/2511.22755v1)
also supplies an asymptotic center ratio. The suitably normalized
`psi_0,psi_4` converge uniformly on their expanding support to the
unit Hermite functions, whose center values are `2^(1/4)` and
`sqrt(3)/(2*2^(1/4))`. Their `L2` normalizations tend to one, since
the uniform error is `O(lambda^(-2))` over an interval of length
`2*lambda` and the Hermite tails are Gaussian. Therefore

```
|a_4/a_0| -> sqrt(3/8),   |r|=O(1).                 (11a)
```

In particular, with `B_4=O(C^(7/2)*exp(-2*pi*C))` and
`H_sigma(log C)<=C^(sigma/2)`, equation (11) becomes

```
sup_(|Im z|<=sigma) |F_z(K_d)|
   =O(C^(4+sigma/2)*sqrt(log C)*exp(-2*pi*C))   (11b)
```

for each fixed `sigma>=0`. This rate concerns only the compressed
Fourier defect. The constant implicit in (11a) is not made effective
by the published `O(lambda^(-2))` statement.

Writing `Fh_I-h_I=d+ell`, with
`ell=(1-P_lambda)Fh_I`, gives the exact orthogonal leakage budget

```
||ell||_2^2=(1-theta_4^2)+r^2*(1-theta_0^2)
             <= B_4+r^2*B_0.                         (12)
```

Even this exponentially small `L2` norm alone does not bound the
Riemann sum `E(ell)`, which samples arbitrarily far outside the
interval. The [leakage sampling estimate](PROLATE_LEAKAGE_SAMPLING_2026_09_23.md)
uses the Fourier-transform structure, endpoint control, and
sine-series cancellation to prove the asymptotic bound
`sup_(lambda^-1<=u<=lambda)|E(ell)(u)|=O(C^(9/2)*exp(-pi*C/4))` with midpoint
values at jumps. This controls the candidate's inversion defect;
it does not bound its Weil-form residual. The scalar term in (5),
proportional to `h_I(0)`, is separately controlled by (8).

## What this changes in the RH route

The [finite-Fourier diagonal](PROLATE_FOURIER_DIAGONAL_2026_09_23.md)
controls projection of the candidate profile and preserves its Xi
limit. It does not turn the candidate into an exact member of the
two-constraint near-radical class. The effective concentration bound
above controls the two eigenvalue deficits without solving the prolate
ODE numerically. The published Hermite limit bounds the origin-value
ratio asymptotically, but an effective finite-cutoff constant is still
missing. The separate cutoff-13
[exact-prolate certificate](exact_prolate_gate_13_4.json) now encloses
finite candidate coefficients and their Weil Rayleigh excess at modes
4 and 8; these asymptotic bounds still do not control an all-support
Weil residual or gap.

A viable quantitative bridge would need, along a growing support and
mode path, all of the following:

1. Effective finite-cutoff bounds on `a_4/a_0` and the endpoint values
   of the **exact** prolate modes, to complement the asymptotic (11a).
2. A transfer from the now-controlled candidate inversion/profile
   defect to the Weil-form Rayleigh excess or residual of
   `P_N E(h_I)`. The leakage sampling estimate bounds the infinite
   sum by exploiting its special Fourier structure; the required
   Weil-form comparison does not follow from that bound.
3. Separation of this candidate from *every other* near-radical
   direction, including odd modes, at a rate strong enough for the
   strip residual theorem.

The finite Rayleigh certificates at cutoff 13 do not establish these
uniform estimates: even the exact prolate candidates lie above the second
even eigenvalue at modes 4 and 8. Neither the two-mode identities nor
the concentration asymptotics prove the all-support simple-even gate,
the prolate-to-Weil ground-state comparison, or RH.
