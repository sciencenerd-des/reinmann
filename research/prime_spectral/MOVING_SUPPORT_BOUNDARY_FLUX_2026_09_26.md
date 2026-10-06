# Boundary flux of a moving finite Fourier interval

The [physical cross-support bound](CROSS_SUPPORT_PHYSICAL_OVERLAP_2026_09_26.md)
compares ground Fourier functions after extending them by zero into
`L2(R)`. Its origin-matched distance cannot be controlled by simply
integrating an `L2` derivative in the support length: a moving interval
with nonzero boundary value has a square-root `L2` increment. The exact
first-order coefficient is the same boundary square that drives the
[prime-power Weil eigenvalue kink](COUPLED_SUPPORT_SCHUR_RECURRENCE_2026_09_26.md).
This is a structural identity and an obstruction to one proposed
budget, not a proof of RH.

## Rank-one derivative of the cross-basis Gram matrix

For the centered orthonormal even Fourier basis on `[-L/2,L/2]`, let
`G(a,b)` be the cross Gram matrix from the [previous note](CROSS_SUPPORT_PHYSICAL_OVERLAP_2026_09_26.md),
with the length-`a` modes as rows and the length-`b` modes as columns.
At fixed rank `N`, put

```
D = a * (right derivative in b) G(a,b) at b=a,
u = (1,sqrt(2),...,sqrt(2)).
```

Differentiating the exact sinc formulas gives

```
D_00 = -1/2,                 D_i0 = 0          (i>=1),
D_0j = -sqrt(2)              (j>=1),
D_ii = -1                   (i>=1),
D_ij = 2*j^2/(i^2-j^2)      (i,j>=1, i!=j).
```

The off-diagonal pair satisfies
`D_ij+D_ji=-2`; the central pair gives `-sqrt(2)`.
Consequently the **exact matrix identity** is

```
D + D^T = -u*u^T.                                  (1)
```

Its skew part is smooth dilation of the Fourier modes. Its symmetric
part is entirely the boundary flux. The vector `u` evaluates the
unscaled basis sum at either endpoint: for coefficient vector `w`,
`g_(a,w)(a/2)=u^T w/sqrt(a)`.

## The unavoidable square-root physical increment

Let `w(L)` be a differentiable one-sided path of unit coefficient
vectors and `g_L` its zero-extended unit Fourier function. Put
`q(a,b)=<g_a,g_b>`. At `b=a`, normalization gives
`w(a)^T w'(a)=0`, so (1) implies

```
(right derivative in b) q(a,b) at b=a
  = w(a)^T D w(a)/a
  = -(u^T w(a))^2/(2*a).                            (2)
```

This first derivative is independent of the interior coefficient
response. With `B=u^T w(a)` and `delta>0`, it follows that

```
||g_(a+delta)-g_a||_2^2
   = B^2*delta/a + o(delta).                         (3)
```

The same leading term survives matching Fourier origins. Write
`alpha_L=integral g_L=sqrt(L)*w_0(L)` and
`h_delta=g_(a+delta)-(alpha_(a+delta)/alpha_a)*g_a`. Since the
origin ratio equals `1+O(delta)`, direct differentiation of
`||h_delta||_2^2=1+s^2-2*s*q` gives

```
||h_delta||_2^2 = B^2*delta/a + o(delta).        (4)
```

If `B!=0`, these physical `L2` distances are proportional to
`sqrt(delta)`, so the zero-extended path has no finite `L2`
derivative. On any compact one-sided interval where `B` stays away
from zero and the coefficient path is smooth, partitions into `m`
equal pieces have total `L2` increment growing at least as `sqrt(m)`.
Thus a **continuous-support total-variation budget in physical `L2`**
cannot prove the desired profile convergence at such a finite rank.
The discrete support-step summability condition from the previous
note remains logically possible; a direct signed Fourier-profile
derivative is another route.

### A finite signed-profile derivative that avoids the `L2` cusp

Let `F_z(L)=integral_(I_L) g_L(t)*exp(i*z*t)dt`,
`alpha_L=F_0(L)`, and `P_L(z)=F_z(L)/alpha_L`. The even boundary value
is `beta_L=g_L(L/2)=g_L(-L/2)`. Differentiating the integral with its
moving endpoints, then differentiating the quotient, gives the exact
one-sided identity

```
dP_L(z)/dL = 1/alpha_L * {
  integral_(I_L) [partial_L g_L(t)]*[exp(i*z*t)-P_L(z)]dt
  + beta_L*[cos(z*L/2)-P_L(z)]
}.                                                     (4a)
```

Here `partial_L g_L` means the ordinary derivative **inside** the
current interval, including the coefficient response and dilation of
the cosine basis. The endpoint term is written explicitly; it is not
an `L2` derivative of the zero-extended function. At `z=0`, both
brackets vanish, as required by `P_L(0)=1`. For the constant Fourier
mode alone, (4a) reduces to
`d/dL sinc(zL/2)=[cos(zL/2)-sinc(zL/2)]/L`, checking its endpoint
normalization. The [coupled constrained-resolvent formula](COUPLED_SUPPORT_SCHUR_RECURRENCE_2026_09_26.md)
supplies the coefficient-response part of `partial_L g_L` between
prime-power thresholds. A uniform bound must keep that part, the
basis dilation, and the endpoint term **signed and together**;
equation (2) by itself controls none of their cumulative effect.

## Relation to the prime threshold and certified examples

At a prime-power threshold `C=p^k`, `a=log C`, the independent Weil
matrix calculation gives
`Delta dot(lambda_0)=-2*B^2/(k*sqrt(C))`. Equation (2) yields the
exact proportionality

```
Delta dot(lambda_0)
  = [4*log(C)/(k*sqrt(C))]
    * (right derivative in b) q(log C,b)|_(b=log C).   (5)
```

Both derivatives are negative whenever the finite ground state is
simple and its boundary evaluation is nonzero. Equation (5) does
**not** bound the ground Fourier-profile derivative: the constrained
inverse in the support-response identity can amplify the same
boundary forcing.

The [17/8](moving_boundary_17_8.json),
[17/16](moving_boundary_17_16.json), and
[19/16](moving_boundary_19_16.json) certificates replay the isolated
Weil ground vectors and prime-threshold jump certificates, then
verify (1)–(5) in Arb intervals:

| `C,N` | Unit boundary square `B^2` | Physical-overlap right slope | Prime eigenvalue derivative jump |
|---:|---:|---:|---:|
| `17,8` | `4.02273e-23` | `-7.09923e-24` | `-1.95131e-23` |
| `17,16` | `1.63285e-36` | `-2.88162e-37` | `-7.92049e-37` |
| `19,16` | `1.10801e-37` | `-1.88152e-38` | `-5.08388e-38` |

For ranks 16, directly interval-evaluating `w^T D w` loses its sign:
at `17,16` its enclosure extends to about `+-5.35e-21`, whereas
the exact rank-one identity encloses the true slope near
`-2.88e-37`. At `19,16` the direct enclosure extends to about
`+-3.57e-19` around a true slope near `-1.88e-38`. Evaluating the
boundary square as the reciprocal norm of the **boundary-normalized**
half-vector also avoids a second cancellation in `u^T w`.
These are concrete examples of why the algebraic coupling must precede
interval evaluation. The finite kink/profile susceptibility gap and
the all-rank Xi transfer remain open.

```sh
uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/prime_spectral -p test_moving_support_boundary.py -v
```
