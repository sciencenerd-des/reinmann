# Physical overlap across two finite prime supports

The [coupled support-step identity](COUPLED_SUPPORT_SCHUR_RECURRENCE_2026_09_26.md)
separates a change in Weil ground coefficients from a change in Fourier
interval length. A dot product of coefficient arrays omits the latter.
Here both unit ground Fourier functions are extended by zero into the
same `L2(R)` space. Their **physical** overlap supplies a direct, though
coarse, origin-normalized strip-profile bound. This remains a finite
comparison and does not prove convergence to Xi.

## Exact cross-basis Gram matrix

Let `a=log C < b=log D`, with even Fourier bases

```
e_(L,0)(t)=L^(-1/2),
e_(L,j)(t)=sqrt(2/L)*cos(2*pi*j*(t+L/2)/L), j>=1,
```

each supported on `[-L/2,L/2]`. Put `r=a/b` and
`sinc(x)=sin(x)/x`. Direct cosine integration over the smaller interval
gives `G_ij=<e_(a,i),e_(b,j)>`:

```
G_00 = sqrt(r),
G_i0 = 0                                      (i>=1),
G_0j = sqrt(2*r)*(-1)^j*sinc(pi*j*r)         (j>=1),
G_ij = sqrt(r)*(-1)^(i+j)*
       [sinc(pi*(i-j*r))+sinc(pi*(i+j*r))]   (i,j>=1).   (1)
```

Thus for unit coefficient vectors `u_C,u_D`, the coordinate overlap is
`u_C dot u_D`, whereas the physical overlap is `q=u_C^T G u_D`.
For positive oriented overlap, the physical distance is exactly
`d=sqrt(2*(1-q))`. Formula (1) becomes the identity Gram matrix at
equal lengths. The implementation checks it against independent
threshold-free Simpson integration, then evaluates it with outward
Arb balls using replayed certified Weil ground vectors.

## A common-space strip transfer

Let `g_C,g_D` be the zero-extended unit functions,
`alpha_E=integral g_E(t)dt>0`, and
`P_E(z)=integral g_E(t)exp(i*z*t)dt/alpha_E`. For
`|Im z|<=sigma`, define

```
M_sigma(L)=sqrt(sinh(sigma*L)/sigma),
M_0(L)=sqrt(L).
```

Since `||g_D-g_C||_2=d` and both functions are supported in the larger
interval, Cauchy–Schwarz and one denominator subtraction give

```
sup_(|Im z|<=sigma) |P_D(z)-P_C(z)|
 <= d/alpha_D * [M_sigma(b)
                 + M_sigma(a)*sqrt(b)/alpha_C].         (2)
```

The first term controls the Fourier-transform difference; the second
controls the changed origin integral. Unlike a coordinate-only bound,
(2) includes Fourier-basis and support-length drift automatically.

There is a sharper **cancellation-preserving** version. Put
`s=alpha_D/alpha_C` and `h=g_D-s*g_C`. Then `integral h=0` and

```
P_D(z)-P_C(z)=F_z(h)/alpha_D,
||h||_2^2=1+s^2-2*s*q,
sup_(|Im z|<=sigma)|P_D(z)-P_C(z)|
    <= M_sigma(b)*sqrt(1+s^2-2*s*q)/alpha_D.     (3)
```

This combines the origin change and physical overlap **before**
taking absolute values. For a support path `C_k` at fixed rank,
summability of the right side of (3), with a valid bound on each step,
would make the profiles locally uniformly Cauchy on every selected
closed substrip. It would still not identify their limit as Xi. The
same analytic inequality also applies when ranks change, provided
the physical unit functions and their origins are certified; this
implementation audits equal ranks only.

## Certified finite comparison

For the support step `17 -> 19`, the saved [rank-8](physical_overlap_17_19_8.json),
[rank-12](physical_overlap_17_19_12.json), and
[rank-16](physical_overlap_17_19_16.json) certificates give:

| Rank | Coefficient overlap | Physical overlap | Physical unit distance | Bound (2), `sigma=2/5` | Coupled bound (3) | Certified profile step at `z=4` |
|---:|---:|---:|---:|---:|---:|---:|
| 8 | `0.999963318` | `0.999815506` | `0.0192091` | `<0.101194` | `<0.045954` | `-0.0180228` |
| 12 | `0.999908047` | `0.999897403` | `0.0143246` | `<0.081460` | `<0.036037` | `-0.0125308` |
| 16 | `0.999871476` | `0.999928243` | `0.0119798` | `<0.070972` | `<0.030972` | `-0.0100622` |

The table rounds the rational interval certificates for readability.
The profile steps come from the independently replayed
[support-step certificates](support_schur_17_19_16.json). At these
three ranks, coordinate overlap decreases while physical overlap
increases. Both are high, yet neither alone certifies a small enough
all-support profile budget. The origin integrals in the new certificates
are near `0.91` to `0.99`. Origin matching improves the finite bounds by
more than a factor of two, but the remaining strip-functional growth
still requires an all-support estimate.

For large `b` with origins bounded below, the sufficient bound (3)
requires the weighted origin-matched norms
`||g_D-(alpha_D/alpha_C)g_C||*M_sigma(b)` to be summable along the
selected support path. This is
a **sufficient** rate demanded by this Cauchy–Schwarz proof, not a
necessary rate for actual profile convergence; signed Fourier
cancellation may yield a sharper route. No such summable estimate,
uniform rank control, or Xi identification is established here.
The [moving-boundary identity](MOVING_SUPPORT_BOUNDARY_FLUX_2026_09_26.md)
adds an important restriction: whenever a finite ground Fourier
function has nonzero endpoint value, its zero-extended physical `L2`
increment is proportional to the square root of a small support-length
change. Therefore this discrete-step sufficient condition cannot be
obtained by integrating an ordinary physical `L2` derivative over a
continuous support path.

```sh
uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/prime_spectral -p test_cross_support_physical_overlap.py -v
```
