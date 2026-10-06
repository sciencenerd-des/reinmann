# Fixed-support Fourier Galerkin convergence and its boundary limit

The prime-defined finite Weil matrices are Galerkin restrictions of the
semilocal Weil form. [Connes–Consani–Moscovici, Proposition 3.4](https://arxiv.org/html/2511.22755v1)
already establishes that their Fourier spaces are a form core at each
**fixed** support cutoff. Below is a direct proof in the logarithmic
form norm, its qualitative Ritz-eigenpair consequence, and an explicit
reason that this convergence cannot by itself control the boundary
evaluation used in the quotient construction. None supplies a rate
uniform as the support grows.

## 1. The form norm and its Fourier core

Fix `lambda>1`, put `a=log(lambda)` and `I=(-a,a)`, and identify a test
function of `u` with its `t=log(u)` representative, extended by zero
outside `I`. Use the unitary Fourier transform on the real line. Define

```
q_log[f] = integral_R log(e+|xi|) |hat(f)(xi)|^2 dxi,
D_log  = {f in L2(I) : q_log[f]<infinity}.
```

Harmless Fourier-normalization constants are suppressed. The
archimedean symbol in [Connes–Consani–Moscovici, Theorem 3.6 and its
proof](https://arxiv.org/html/2511.22755v1) differs from a positive
multiple of `log(e+|xi|)` by a bounded function; for fixed `lambda`,
the prime and pole contributions are bounded operators. After adding
a sufficiently large multiple of the L2 norm, the closed Weil form
norm is therefore equivalent to `||f||_2^2+q_log[f]`. This bounded-form
decomposition is the external input used below; the core argument is
independent of its exact bounded coefficients.

Let `E_N` be the span, with zero extension, of

```
phi_n(t) = (2a)^(-1/2) exp(i*pi*n*t/a),  |n|<=N.
```

These are the finite matrix spaces in the paper and this repository.
Every `phi_n` lies in `D_log`: its whole-line Fourier transform is a
shifted sinc, whose squared tail is `O(|xi|^-2)`. More quantitatively,
for a constant depending only on `a`,

```
||phi_n||_2^2+q_log[phi_n] <= C_a(1+log(e+|n|)).       (1)
```

To prove density, first take `f in D_log`. Inward dilation
`f_r(t)=r^(-1/2)f(t/r)`, `r<1`, has support strictly inside `I`.
On the Fourier side its form norm is controlled by the same logarithmic
weight, since `log(e+|xi|/r) <= C log(e+|xi|)` for `r` near one.
Strong continuity of dilation in this weighted L2 space gives
`f_r -> f` in the form norm. Convolution of `f_r` with a sufficiently
narrow compactly supported smooth probability mollifier stays inside
`I` and also converges in form norm: its Fourier multiplier is bounded
by one and tends pointwise to one. Thus `C_c^infinity(I)` is a form core.

For `psi in C_c^infinity(I)`, its periodic extension is smooth. Its
Fourier coefficients `c_n` decay faster than every power. The triangle
inequality in the form Hilbert space and (1) give

```
||psi - sum_(|n|<=N) c_n phi_n||_form
    <= sum_(|n|>N) |c_n| C_a^(1/2)
                           (1+log(e+|n|))^(1/2) -> 0.   (2)
```

So `union_N E_N` is a form core. Reflection commutes with the Weil form;
symmetrizing every approximation gives the same conclusion for the
even cosine subspaces. This proves form-core density, not a uniform
bound on the constants `C_a` as `a` grows.

## 2. What the core proves about eigenpairs

The fixed-support Weil operator has discrete lower-bounded spectrum by
the cited Theorem 3.6. Write its ordered eigenvalues with multiplicity
as `lambda_0<=lambda_1<=...`, and the Ritz eigenvalues on `E_N` as
`lambda_k^(N)`. The min-max principle and the form core imply, for
each fixed `lambda` and `k`,

```
lambda_k^(N) decreases to lambda_k as N -> infinity.    (3)
```

Indeed `lambda_k^(N)>=lambda_k` and decreases with the nested spaces.
Approximate a basis of the first `k+1` eigenspaces in form norm using
(2); their span has dimension `k+1` for large `N`, and its maximal
Rayleigh quotient tends to `lambda_k`. Min-max gives the opposite
limsup inequality.

If the full lowest eigenvalue is simple with gap
`delta=lambda_1-lambda_0>0`, orient unit Ritz minimizers `v_N` toward
the unit eigenvector `v`. Spectral decomposition gives

```
||v_N-v||_2^2 <= 2 (lambda_0^(N)-lambda_0)/delta -> 0. (4)
```

There is also an exact quantitative target. For any `p in E_N` and
`e=v-p`, the eigenvector equation makes the cross terms cancel:

```
Rayleigh(p)-lambda_0
    = [QW_lambda[e]-lambda_0*||e||_2^2]/||p||_2^2. (5)
```

The numerator is nonnegative by the ground-state variational principle.
If `||e||_2<1`, then `||p||_2>=1-||e||_2`, so the right side bounds
`lambda_0^(N)-lambda_0` from above, and division by `delta` in (4)
gives an eigenvector-error bound. The core theorem guarantees that
some choices of `p` make this quantity tend to zero at fixed support;
it gives no effective estimate along `lambda -> infinity`. In
particular, ordinary L2 approximation of the prolate candidate is not
a substitute for this *form-error divided by gap* budget.

For `L=2a`, define the centered Fourier functional by
`F_z(f)=L^(-1/2) integral_I f(t) exp(-izt) dt`. Cauchy–Schwarz gives
`||F_z|| <= W(sigma,L)=sqrt(sinh(sigma*L)/(sigma*L))` on
`|Im z|<=sigma` (with `W(0,L)=1`). Combining (4) and (5), any chosen
`p in E_N` with `||v-p||_2<1` yields the explicit strip estimate

```
sup_(|Im z|<=sigma) |F_z(v_N)-F_z(v)|
  <= W(sigma,L) sqrt[2(QW_lambda[v-p]-lambda_0||v-p||_2^2)
                         /(delta ||p||_2^2)].        (5a)
```

This retains the entire form-error cancellation in its numerator. It
is conditional on an effective approximant to the *true* ground vector
and a gap; neither is presently uniform in support. Fourier-origin
normalization additionally needs a nonzero lower bound on `|F_0(v)|`,
as in the earlier strip transfer.

Consequently their *unnormalized* Fourier transforms converge locally
uniformly in the complex variable: on fixed `I`, each Fourier
functional has a bounded L2 norm uniformly on compact sets. If
`F_0(v)!=0`, their Fourier-origin-normalized transforms converge locally
uniformly as well. Simplicity, the positive gap, and `F_0(v)!=0` are
not proved here for every support. Equation (3) alone proves none of
them. Nor does fixed-support convergence supply the joint
`N,lambda -> infinity` rate needed to identify Xi.

## 3. Boundary evaluation is not controlled by this form norm

The quotient construction also uses the boundary value `f(a)`, whose
nonvanishing is certified at several finite configurations. It is not
a continuous functional on `D_log`. In fact its norm on the finite
spaces diverges quantitatively. For `N>=1`, take the unit boundary
Dirichlet kernel

```
d_N(t) = (L(2N+1))^(-1/2)
         sum_(|n|<=N) (-1)^n exp(2*pi*i*n*t/L),  L=2a.
```

It is real and even, `||d_N||_2=1`, and
`d_N(a)=sqrt((2N+1)/L)`. Put `omega_N=2*pi*N/L`. Its zero-extension
Fourier transform has, up to the harmless unitary constant, the form

```
hat(d_N)(xi) = 2 sin(xi*L/2)/sqrt(L(2N+1))
               * sum_(|n|<=N) 1/(xi-2*pi*n/L).       (6)
```

The apparent poles are removable. On `|xi|<=2*omega_N`, Parseval
bounds the log-weight integral by `log(e+2*omega_N)`. On
`|xi|>2*omega_N`, each denominator in (6) has magnitude at least
`|xi|/2`, so `|hat(d_N)(xi)|<=C_L*sqrt(N)/|xi|`. Integrating
`N*log(e+|xi|)/xi^2` from `2*omega_N` to infinity yields another
`O_a(log(e+N))`. Consequently

```
||d_N||_2^2+q_log[d_N] <= C_a log(e+N),
sup_(0!=f in E_N even) |f(a)|/||f||_form
    >= c_a sqrt(N/log(e+N)) -> infinity.          (7)
```

The form norm equivalence transfers this lower bound, with constants
depending on the fixed support, to the shifted Weil form norm. This
is a quantitative reason the finite boundary functional cannot be
controlled by form convergence alone.

The same split of the Fourier integral with `log(e+|xi|)^2` in place
of `log(e+|xi|)` shows that the compressed archimedean multiplier sends
`d_N` to a vector of L2 norm `O_a(log(e+N))`. The remaining prime and
pole operators are bounded at fixed support, so `d_N` belongs to the
Weil operator domain and

```
||d_N||_2+||A_lambda d_N||_2 <= C_a log(e+N),
|d_N(a)|/(||d_N||_2+||A_lambda d_N||_2)
    >= c_a sqrt(N)/log(e+N) -> infinity.          (7a)
```

For any fixed resolvent point `z`, setting
`h_N=(A_lambda-z)d_N` also rules out a bounded map
`h -> [(A_lambda-z)^(-1)h](a)` from L2 to boundary values. A useful
trace estimate therefore cannot be a generic graph-norm or L2
resolvent bound; it must exploit the ground-eigenfunction equation
more specifically or impose a stronger source norm.

This is also an interface distinction in the source paper. Its
[Lemma 5.5 and Corollary 5.6](https://arxiv.org/html/2511.22755v1)
pass the Dirichlet-kernel boundary evaluation to the limit for
functions in the domain of the **scaling derivative** with periodic
boundary conditions. Membership in the domain of the logarithmic-order
Weil operator does not imply that stronger derivative regularity.
For example, an even compactly supported function equal to
`|t|^(1/4)` near zero has Fourier decay `O(|xi|^(-5/4))` and therefore
finite log-squared Fourier energy; hence it
belongs to the Weil operator domain under the bounded-perturbation
decomposition, while its derivative is not in L2. Equation (7a) also
shows there is no continuous graph-norm embedding. Applying the
paper's boundary lemma to an infinite Weil ground eigenfunction
requires an additional regularity proof.

It also proves that the boundary-zero subspaces are form dense. Given
any even `psi in E_M`, for `N>=M` put

```
psi_N = psi - [psi(a)/d_N(a)] d_N  in E_N.
```

Then `psi_N(a)=0` and (7) gives
`||psi_N-psi||_form=O_(a,psi)(sqrt(log(e+N)/N)) -> 0`.
The even Fourier spaces are already a form core, so the union of their
boundary-zero subspaces is dense in the entire even form domain.

For a precise spectral consequence, let `m_N` be the minimum Rayleigh
quotient over nonzero even `f in E_N` with `f(a)=0`. Assuming the even
Weil operator has a discrete lower-bounded spectrum, min-max and the
density just proved give

```
m_N decreases to lambda_0,even,
m_N - lambda_0,even^(N) -> 0.                     (7b)
```

The second line follows because the unrestricted even Ritz minimum
also decreases to `lambda_0,even`. Hence a *fixed positive* separation
between the boundary-zero restriction and the even lowest Ritz value
cannot persist as `N -> infinity`. The finite boundary-kernel LDL
certificates establish nonzero boundary at their individual modes;
their margins cannot be promoted to a uniform all-mode margin by
form-core arguments. This does not imply that the actual continuous
ground state has zero boundary value: that value may lack a form trace
altogether, and the eigenfunction equation may supply extra regularity.

The stored cutoff-13 certificates give a finite illustration. The
following intervals enclose the absolute boundary value of a **unit**
even ground vector; for modes 12 and 16, the scale-invariant value was
recovered from the saved boundary-normalized half-vector `c` as
`(c_0^2+2*sum_(n>=1)c_n^2)^(-1/2)`. All source hashes were checked.

| Modes | Certified outward enclosure for `|v_N(a)|` |
|---:|---:|
| 4 | `(4.61528e-7, 4.61529e-7)` |
| 8 | `(4.50375e-11, 4.50376e-11)` |
| 12 | `(2.64881e-14, 2.64882e-14)` |
| 16 | `(5.61422e-17, 5.61423e-17)` |

These four shrinking values do **not** establish a limit or imply
that the continuous eigenfunction has zero boundary value. They do
show why an absolute trace error would need exceptional precision at
these finite modes.

The [boundary-susceptibility calculation](BOUNDARY_SUSCEPTIBILITY_2026_09_23.md)
separates this small unit boundary value from the collapsing
boundary-zero Ritz margin by an exact positive resolvent sum. It
certifies that relation at modes 4 and 8 but gives no uniform limit.

The same failure has a direct continuum-scale construction. Here is
an explicit boundary layer.

Choose a smooth function `phi` on `[0,infinity)` supported in `[0,1]`
which equals one near zero, and for `0<epsilon<a` set

```
f_epsilon(t) = phi((a-t)/epsilon),  a-epsilon<=t<=a,
               0,                       otherwise in I.
```

Its zero extension jumps at `a`, but it belongs to `D_log`: the Fourier
transform of the one-sided `phi` is `O(|xi|^-1)`, making its squared
log-weight integral finite. Scaling gives

```
||f_epsilon||_2^2 = O(epsilon),
q_log[f_epsilon] = O(epsilon log(1/epsilon)),
f_epsilon(a-) = 1.                                  (8)
```

For the second bound, substitute `eta=epsilon*xi` and use
`log(e+|eta|/epsilon) <= log(1/epsilon)+log(e+|eta|)` for
`epsilon<=1`. Thus `f_epsilon -> 0` in form norm while its boundary
value remains one. Adding the reflected bump proves the same fact in
the even subspace. In fact, the even sum
`g_epsilon(t)=f_epsilon(t)+f_epsilon(-t)` has a smooth periodic extension
because `phi` is constant near zero and flat at the end of its support.
Its finite Fourier partial sums converge both uniformly and in form
norm by (1) and rapid coefficient decay. If boundary evaluation were
bounded on the union of the finite Fourier spaces in the form norm,
passage to these partial sums would give
`1=|g_epsilon(a)| <= K ||g_epsilon||_form`, contradicting (8) as
`epsilon -> 0`. Boundary values can therefore not be passed through
(3) or (4) by form convergence alone, even within the finite Fourier
core.

The remaining boundary gate needs stronger regularity or a direct
ground-eigenfunction boundary identity. For example, a support-uniform
`H^s` bound with `s>1/2` would make point evaluation continuous, but
the logarithmic form norm itself supplies no such bound. Any useful
estimate must also survive increasing support and the very small
boundary values seen in the finite prime certificates.

The established core result and the min-max corollary settle qualitative
fixed-support Ritz convergence. They do not prove the simple-even
lowest state, boundary control, prolate-to-Weil approximation, joint
support-mode convergence, or RH.
