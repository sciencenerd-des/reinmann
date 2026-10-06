# A coupled support-step identity for the prime Weil ground profile

The [nested-rank recurrence](COUPLED_RANK_SCHUR_RECURRENCE_2026_09_24.md)
holds at fixed support. Growing the prime support changes both the
Weil matrix and the length of the Fourier interval. A support-step
comparison must retain both effects. This note gives an exact finite
identity and certifies one support step; it does not supply an
infinite-support estimate or prove RH.

## Exact identity

Fix an even Fourier rank `N` and supports `C<D`. In the coefficient
basis, write their prime-defined even Weil matrices as

```
A_C = [[a_C, b_C*], [b_C, B_C]],
A_D = [[a_D, b_D*], [b_D, B_D]].
```

Suppose each has a simple lowest even eigenvalue `lambda_C`,
`lambda_D`, with nonzero zeroth eigenvector coordinate. Normalize the
ground vectors as `v_C=(1,h_C)` and `v_D=(1,h_D)`. The new
origin-constrained block `T_D=B_D-lambda_D I` is positive definite.
Subtract the two ground equations **before** inverting it:

```
r_(C,D) = (b_D-b_C) + (B_D-B_C)h_C
          + (lambda_C-lambda_D)h_C,
h_D-h_C = -T_D^-1 r_(C,D).                         (1)
```

The two terms in `r` are the matrix change and the eigenvalue shift.
There is no assumption that `lambda_C-lambda_D` has a fixed sign:
unlike a nested rank step, different support spaces are not nested
subspaces of one fixed Hilbert space.

Let `f_(C,z)` be the Fourier functional on the interval of length
`log C`, in these same coefficient coordinates, and put
`P_C(z)=f_(C,z)v_C`. Then

```
P_D(z)-P_C(z)
  = [f_(D,z)-f_(C,z)]v_C
    - f_(D,z)(0,T_D^-1 r_(C,D)).                    (2)
```

The first term is **basis-length drift**; the second is the coupled
ground-vector response. Omitting the first term would compare two
different Fourier transforms as if they used the same interval.
Equation (2) retains cancellation inside the source `r` and between
the two profile terms.

## A continuous support-flow version

Put `L=log C` and hold `N` fixed. Between successive prime-power
thresholds the finite matrix entries are differentiable in `L`:
the prime sum has a fixed finite index set, and the regularized
archimedean and pole integrals can be put on a fixed integration
interval by rescaling their variables. At a threshold `C=p^k`, the
new prime term has zero value because its correlation factor at
`log(p^k)=L` vanishes: the diagonal factor is `1-z/L=0`, and for
distinct integer Fourier indices the off-diagonal sinc factor is
`sinc(pi(m-n))=0`. Thus the matrix is continuous across each
threshold, although its derivative can have a one-sided jump.

Where the simple-even and nonzero-origin gates hold, differentiate
the ground equation. With a dot denoting `d/dL`, one obtains

```
dot(lambda) = v* dot(A) v / (v*v),
dot(h) = -T^-1 [dot(b)+dot(B)h-dot(lambda)h],
dot(P)(z) = dot(f_z)v
            - f_z(0,T^-1[dot(b)+dot(B)h-dot(lambda)h]).   (3)
```

This is the infinitesimal counterpart of (1)–(2). A proof of an
integrable bound on the **complete signed right side** of (3),
compatible with increasing rank, would give a cumulative support
profile budget. Neither the finite certificates nor the endpoint
vanishing of a single prime term supplies that bound.

### Exact rank-one kick at a prime power

The endpoint vanishing has a stronger derivative consequence. Let
`C=p^k`, `L_0=log C`, and `z=log(p^k)`. Set `x=z/L`. The prime
correlation in the full Fourier basis is

```
q_(m,m)(x)=2(1-x)cos(2*pi*m*x),
q_(m,n)(x)=-2*x*cos(pi*(m+n)*x)*sinc(pi*(m-n)*x), m!=n.
```

For all integer `m,n`, `q_(m,n)(1)=0` and
`d q_(m,n)/dx at x=1 = -2`. In the off-diagonal case this follows
from `d/dx sinc(pi*d*x) at x=1 = (-1)^d` for nonzero integer `d`,
and `(-1)^(m+n)*(-1)^(m-n)=1`. Because `dx/dL=-1/L_0`, the new
correlation has right derivative `2/L_0` in **every** full-matrix
entry. Its contribution to the Weil matrix carries coefficient
`-log(p)/sqrt(p^k)`. Therefore

```
dot(A_full)(L_0+) - dot(A_full)(L_0-)
  = -2/(k*sqrt(p^k)) * 1*1^T.
```

In the orthonormal even basis, `1` becomes
`u=(1,sqrt(2),...,sqrt(2))`, the boundary-evaluation vector. Thus

```
Delta dot(A_even) = -2/(k*sqrt(C)) * u*u^T,
Delta dot(lambda_0)
  = -2/(k*sqrt(C)) * (u^T v)^2/(v^T v) < 0        (3a)
```

whenever the lowest even eigenvalue is simple and its boundary
evaluation is nonzero. The second line is the Hellmann–Feynman
formula applied on each side of the threshold. In distributional
language, the **atomic** part of the second support derivative of
the least eigenvalue is negative at each such prime-power
threshold. This does not assert global concavity: the smooth
curvature between thresholds is uncontrolled.

The profile has a different, potentially amplified jump. Write
`u=(1,s)`, `v=(1,h)`, `B_0=u^T v`, `H=v^T v`, and
`gamma=2/(k*sqrt(C))`. Subtract the differentiated ground equations
on the two sides of the threshold. The terms involving the matrix
and eigenvalue jumps remain coupled:

```
Delta dot(h) = gamma*B_0*T^-1 [s-(B_0/H)h],
Delta dot(P)(z)
  = gamma*B_0*f_(L,z)(0,T^-1[s-(B_0/H)h]).     (3b)
```

The Fourier functional itself is smooth in `L` at the threshold, so
its own derivative has no jump. Equation (3b) is an exact finite
profile-susceptibility formula. The small boundary factor `B_0`
does **not** by itself make the profile jump small: `T^-1` can
amplify the boundary forcing. Controlling their signed product,
uniformly in rank and support on a strip, is a distinct missing
analytic estimate.

The [interval generator](../../experiments/prime_spectral/prime_threshold_jump.py)
replays the finite Weil eigenpair and certifies the right side of
(3a). Approximate values from the outward enclosures are:

| Prime threshold | Rank | Unit-vector boundary square | Least-eigenvalue derivative jump |
|---:|---:|---:|---:|
| 17 | 8 | `4.0227e-23` | `-1.9513e-23` |
| 17 | 12 | `2.9491e-30` | `-1.4305e-30` |
| 17 | 16 | `1.6329e-36` | `-7.9205e-37` |
| 19 | 8 | `1.6220e-23` | `-7.4423e-24` |
| 19 | 12 | `2.9760e-31` | `-1.3655e-31` |
| 19 | 16 | `1.1080e-37` | `-5.0839e-38` |

The same certificates evaluate (3b) by a certified signed
constrained-eigenmode sum:

| Prime threshold | Rank | Least-eigenvalue derivative jump | Ground-profile derivative jump at `z=4` |
|---:|---:|---:|---:|
| 17 | 8 | `-1.9513e-23` | `-0.039450513` |
| 17 | 12 | `-1.4305e-30` | `-0.029265817` |
| 17 | 16 | `-7.9205e-37` | `-0.019693155` |
| 19 | 8 | `-7.4423e-24` | `-0.034508280` |
| 19 | 12 | `-1.3655e-31` | `-0.026468688` |
| 19 | 16 | `-5.0839e-38` | `-0.020237167` |

All six profile intervals are strictly negative. Their magnitudes
exceed the corresponding eigenvalue-jump magnitudes by a certified
factor greater than `10^20` in these finite cases. At the imaginary
argument `z=i`, all six profile jumps are strictly **positive**.
Consequently the eigenvalue kink alone is not a usable profile
budget without a bound on the constrained susceptibility in (3b);
the profile's atomic support curvature has no common sign even at
these two arguments.

There is also an exact **positive-kernel counterexample** to deriving
the profile bound from the eigenvalue kink alone. Fix interval length
`L=2*pi` and even Fourier rank one. For `0<epsilon<1`, set

```
h=-(1-epsilon)/sqrt(2),
v=(1,h),  w=(-h,1),  H=v^T v,
A_epsilon=epsilon^2*I+(epsilon/H)*w*w^T,
u=(1,sqrt(2)).
```

The matrix is positive definite with simple lowest eigenvalue
`epsilon^2` and gap `epsilon`; `v` is its origin-normalized ground
vector and `u^T v=epsilon>0`. In the corresponding Fourier
normalization the spatial kernel is proportional to
`1+(1-epsilon)cos(t)`, whose minimum is `epsilon>0`. Thus matrix
positivity, a simple ground state, nonzero boundary evaluation, and
whole-support kernel positivity all hold.

Now perturb the matrix by `A_epsilon(t)=A_epsilon-t*u*u^T`, the same
rank-one direction as a prime threshold. Differentiating its simple
ground eigenpair at `t=0` gives

```
lambda_epsilon'(0)=-epsilon^2/H -> 0,
h_epsilon'(0)=(3-epsilon)/sqrt(2).
```

For the second identity, the one-dimensional constrained block is
`T=epsilon/H`, so (3b) reduces exactly to
`h'=epsilon*(H/epsilon)*(sqrt(2)-epsilon*h/H)`.

At real Fourier frequency `z=1`, the centered even Fourier
functional on this interval has coordinates `(0,-1/sqrt(2))`.
Consequently its origin-normalized ground profile satisfies

```
P_epsilon'(1;0)=-(3-epsilon)/2 -> -3/2.          (3c)
```

The ratio `|P_epsilon'(1;0)|/|lambda_epsilon'(0)|`
diverges like `epsilon^-2`. For each fixed `epsilon`, the finite
gates persist for a sufficiently small perturbation interval.
This model is **not** a prime Weil matrix; it proves that the
listed positivity, simplicity, and boundary gates together with a
small eigenvalue kink cannot logically imply a
uniform profile-kink bound. A new estimate must control the
boundary forcing together with the constrained inverse in (3b).
As an independent normalization check at cutoff 17, rank 8, the
test perturbs the **whole even matrix** by `-t*gamma*u*u^T` and
computes centered eigenpair secants. Their eigenvalue and `z=4`
profile slopes agree with the intervals from (3a)–(3b) to the
stated test tolerances. The secant is a numerical cross-check; the
rank-one endpoint calculation and differentiated eigenvector
equation provide the proof of the formulas.

The six `prime_threshold_jump_C_N.json` files, for example
[cutoff 19 at rank 16](prime_threshold_jump_19_16.json), record
rational intervals and provenance. Their rapid decrease with
rank is finite evidence only; no bound for all ranks or all prime
thresholds follows. The test checks the implemented correlation
formula by finite differences; the derivative identity above is the
exact algebraic proof.

## Certified cutoff 17 to 19 step

The [interval generator](../../experiments/prime_spectral/support_schur_recurrence.py)
replays both isolated Weil certificates, recomputes their matrices,
isolates `T_19` by positive inertia and Rump eigenpairs, and evaluates
`T_19^-1 r` as a **signed spectral sum**. It checks the resulting
coefficient change against independently isolated ground vectors.
It also checks (2) against the direct profile difference and against
the ground profiles recorded in the separate prolate-alignment
certificates.

At real frequency `z=4`, the outward rational enclosures in the saved
files have these approximate centers:

| Rank | Basis-length drift | Coupled ground response | Total support step | Certified total width |
|---:|---:|---:|---:|---:|
| 8 | `-0.025609251` | `+0.007586438` | `-0.018022813` | `<1e-6` |
| 12 | `-0.023536630` | `+0.011005800` | `-0.012530830` | `<1e-6` |
| 16 | `-0.022353731` | `+0.012291536` | `-0.010062195` | `<5.8e-8` |

Thus the ground-vector response offsets part, but not all, of the
Fourier basis drift in these three finite spaces. Direct interval
inversion of `T_19` at rank 16 gave a width above `10^4` for the
profile response because of interval dependency in a highly
conditioned solve. The certified signed eigenmode sum reduces that
width below `5.8e-8`. This is a conditioning repair, not an
asymptotic theorem.

The [rank-8](support_schur_17_19_8.json),
[rank-12](support_schur_17_19_12.json), and
[rank-16](support_schur_17_19_16.json) files contain the full
enclosures, coupled source, coefficient change, and input/source
hashes.

## What a two-axis limit would require

For a path `(C_k,N_k)` with both coordinates increasing, insert an
intermediate state `(C_k,N_(k+1))`. Every profile increment is the
sum of a **rank step at fixed `C_k`**, governed by the nested-rank
identity, and a **support step at fixed `N_(k+1)`**, governed by (2).
To prove that the ground profiles converge locally uniformly, their
combined tail must tend to zero uniformly on every compact subset
of `|Im z|<1/2`. Bounds on the two absolute terms in (2) may be too
costly; the signed sum is the natural target.

If `Q_(C,N)` is the exact projected prolate profile, the more direct
transfer target is the **difference of support responses**

```
[P_D(z)-P_C(z)] - [Q_D(z)-Q_C(z)].                (4)
```

Controlling (4) cumulatively on a rank/support diagonal could
preserve cancellation between the prime ground profile and the
prolate candidate. The [cross-support alignment](CROSS_SUPPORT_PROLATE_RANK_SCALING_2026_09_26.md)
shows that their discrepancy grows at each tested fixed rank, so a
fixed-rank estimate is insufficient. No bound on (3) along a growing
rank path, no uniform simple-even gate, and no RH proof is obtained.

Subtracting the **certified** ground-minus-exact-prolate profile
intervals at supports 19 and 17 gives the following displays of (4)
at `z=4`: rank 8, `-0.016600781`; rank 12, `-0.011109389`; rank 16,
`-0.008640755`. The intervals are strictly negative and disjoint in
that order. Thus the finite support defect is still nonzero at rank
16, although its magnitude decreases over these three ranks. The
[replay test](../../experiments/prime_spectral/test_support_schur_recurrence.py)
checks the signed interval ordering directly from both prolate
alignment certificates.

Replay the rank-16 certificate and its independent test with:

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/support_schur_recurrence.py --first research/prime_spectral/isolated_kernel_17_16.json --second research/prime_spectral/isolated_kernel_19_16.json --output research/prime_spectral/support_schur_17_19_16.json
uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/prime_spectral -p test_support_schur_recurrence.py -v
uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/prime_spectral -p test_prime_threshold_jump.py -v
```
