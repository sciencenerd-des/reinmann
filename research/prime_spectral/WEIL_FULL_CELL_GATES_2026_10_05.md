# Full Weil ground and spatial gates on the 17–19 support cell

The degree-64 certificates now prove positivity of the full Weil form, a
simple even full ground state, a nonzero spatial boundary, and a positive
spatial kernel throughout `17<=C<=19`, with Fourier cutoff `N=8` (full
matrix dimension 17). The normalized entire Fourier ground profiles have
only real zeros by the existing exact displacement/quotient theorem.
These are finite support and finite dimension conclusions. Convergence to
Xi, the theta curvature theorem, and RH remain unproved.

Subsequent work: the [coupled density budget](WEIL_STRIP_CELL_BUDGET_2026_10_05.md)
now controls exact ground-profile increments throughout this cell. Its
determinant identity also proves that the boundary and Fourier origin
have the same sign whenever the full ground is simple, even, and has a
nonzero origin. Infinite-path summability remains open.

This closes the odd-parity and spatial gates left open by the
[degree-48 even eigenfamily certificate](WEIL_EVEN_EIGENFAMILY_CELL_2026_10_05.md).
The local candidates are validated polynomial eigenpair predictors. They
are not the canonical prolate candidates, which still fail the previously
recorded residual-and-gap clearance test.

## Exact boundary rigidity at arbitrary Fourier rank

The following proof applies at every positive support length and every
finite Fourier cutoff where the defining Weil displacement identity holds.
It does not require a Taylor approximation, sampled roots, or a numerical
boundary evaluation.

Index the real symmetric Weil matrix `A` by `-N,...,N`, and set

```
J=diag(-N,...,N),  e=(1,...,1)^T,
b_i=i*A_(i,0),  b_-i=-b_i,
[A,J]=e b^T-b e^T.
```

The last identity follows from the exact off-diagonal correlation formula
`A_ij=(b_i-b_j)/(i-j)` and linearity of all the pole, archimedean and prime
contributions. It holds on each active prime branch, including its endpoint
values. The derivation is in the
[quotient theorem](QUOTIENT_OPERATOR_2026_09_19.md).

**Boundary rigidity theorem.** Let `c` be a nonzero even eigenvector of `A`
at eigenvalue `lambda`. If `lambda` is absent from the odd spectrum, then
`S=e^T c` is nonzero.

**Proof.** Put `G=A-lambda I`. Evenness gives `b^T c=0`, so

```
G Jc=[A,J]c=-b S.
```

If `S=0`, then `Jc` is an odd eigenvector at `lambda`, unless `Jc=0`.
But `Jc=0` leaves only the central coordinate of `c`; then `S=c_0=0`
would imply `c=0`. Thus `Jc` is nonzero and contradicts absence of
`lambda` from the odd spectrum. QED.

In particular, a strict odd/even ground separation already supplies the
nonzero boundary normalization needed by the quotient theorem. This removes
a separate boundary hypothesis from the conditional spectral program; it
does not prove the odd/even separation at unbounded support or rank.

There is also a quantitative estimate. Suppose `c` has norm one and
`g=lambda_(odd,min)-lambda>0`. The odd restriction of `G` is at least
`g I`, hence

```
g ||Jc|| <= ||G Jc|| = ||b|| |S|.
```

A bound that never divides by `||b||` follows directly from
`||b||<=N||A||`, since `b=J A e_0`:

```
|S| >= g ||Jc||/(N||A||)
     >= g sqrt(1-c_0^2)/(N||A||),
```

when `N>=1` and `||A||>0`. The inequality is valid also when `b=0`;
then the numerator is zero. In orthonormal even coordinates
`v=(v_0,...,v_N)`, `c_0=v_0` and `||Jc||^2=sum_(j>=1) j^2 v_j^2`.
The generator uses an outward upper bound on `v_0<1` and on `||A||`,
and an outward positive lower bound on `g`, to produce a strictly positive
bound in this cell.

The nonzero theorem controls absolute boundary size; it does not choose
the sign of `S`. Spatial Bernstein positivity below fixes the sign in the
positive Fourier-origin orientation.

### Exact odd-resolvent reconstruction

The same identity yields a second, arbitrary-finite-rank consequence that
preserves the boundary cancellation algebraically. Let `E` and `O` be the
orthonormal even and odd blocks, `lambda` the even eigenvalue, and suppose
`O-lambda I` is invertible. Set

```
K=diag(1,...,N),  a=K E_(1:N,0),
h=(O-lambda I)^(-1) a.
```

In these coordinates `Jc` has odd coordinates `K v_(1:N)` and `b` has
odd coordinates `a`. Therefore

```
(O-lambda I) K v_(1:N)=-S a,
v_j/S=-h_j/j,                       j=1,...,N,
v_0/S=1+sqrt(2) sum_(j=1)^N h_j/j.   (boundary normalization)
```

The last equation follows from `S=v_0+sqrt(2) sum v_j`, rather than a
second spectral assumption. Thus the entire boundary-normalized even
eigenvector is reconstructed from the odd resolvent at its even
eigenvalue. For a unit vector one has the exact identity

```
1/S^2 = [1+sqrt(2) sum_j h_j/j]^2 + sum_j (h_j/j)^2.
```

This is a written algebraic identity, not an additional numeric
certificate. Its proof is the displacement equation and unit
normalization just given. It recasts the tiny boundary as a reciprocal
norm, and makes the common odd resolvent an explicit target for a
coupled support/rank estimate. It does not bound that resolvent along an
infinite path. In particular the finite lower boundary bound below is
not a uniform-in-rank trace estimate and does not repair the trace
obstruction in the [fixed-support form-core audit](FIXED_SUPPORT_FORM_CORE_2026_09_23.md).

## Certified whole-cell odd spectrum and full ground separation

The [odd generator](../../experiments/prime_spectral/weil_odd_cell.py)
constructs the odd Taylor block

```
A_odd,ij=A_(i,j)-A_(i,-j),  i,j=1,...,8.
```

It encloses both scalar Taylor series first and adds their analytic
remainder bounds. Exact dyadic midpoint coefficients give a common matrix
polynomial over the full cell. The coefficient rounding error is added
to the truncation error. The same 32 adjacent closed subcells used by the
even certificate cover the entire cell, including both prime boundaries.
Incomplete or altered covers are rejected.

On each subcell the certified center eigenbasis, polynomial predictors,
complete residual polynomial through degree 128, Neumann inverse bound,
and disjoint Gershgorin disks isolate every odd eigenvalue. No convergence
assumption about the eigenpair predictor recurrence is used. Odd and even
uniform eigenvalue bands are then compared, including both residual disk
radii. Every odd eigenvalue lies above the positive lowest even eigenvalue.
The next full eigenvalue is the smaller of the first odd and second even
bands. Thus the full matrix is positive and its full ground is simple and
even at every parameter.

The [degree-64 even artifact](weil_eigenfamily_17_19_8_degree64.json),
[odd/parity artifact](weil_odd_cell_17_19_8_degree64.json), and
[spatial artifact](weil_spatial_cell_17_19_8_degree64.json)
give these bounds, rounded outward:

| Quantity, uniform over the full cell | Bound |
|---|---:|
| Even matrix approximation operator error | `<4.870e-41` |
| Odd analytic value operator remainder | `<4.694e-41` |
| Even eigenvalue disk radius | `<4.456e-40` |
| Odd eigenvalue disk radius | `<3.812e-40` |
| Full lowest eigenvalue | `>2.259e-26` |
| Full ground spectral gap | `>4.043e-23` |
| Exact-to-candidate unit even ground distance | `<8.687e-21` |
| Origin-normalized candidate profile error, `abs(Im z)<=2/5` | `<4.618e-20` |
| Unit spatial boundary, positive-origin orientation | `>1.189e-12` |
| Absolute unit spatial boundary from displacement estimate alone | `>1.458e-24` |

The degree-48 vector error, below `2.416e-10`, was much larger than the
spatial boundary. Raising the degree to 64 retains the same 32-subcell
cover and resolves the cancellation in the small boundary sum.

## Spatial positivity with coupled Bernstein functionals

For the unit even eigenvector in orthonormal even coordinates, its raw
spatial kernel on `|t|<=L/2` is

```
r(t)=v_0+sqrt(2) sum_(j=1)^N v_j cos(2pi*j*(t+L/2)/L).
```

Writing `u=(1+cos(2pi*t/L))/2` gives the exact degree-N polynomial

```
r(u)=v_0+sqrt(2) sum_(j=1)^N v_j T_j(1-2u).
```

At the spatial endpoints `u=0`, and `r(0)=S=v_0+sqrt(2) sum v_j`.
If `T_j(1-2u)=sum_r a_jr u^r`, its degree-N Bernstein coefficient is

```
beta_k=v_0+sqrt(2) sum_j v_j sum_(r<=min(j,k))
        a_jr * binom(k,r)/binom(N,r).
```

All `a_jr` and binomial ratios are calculated exactly as rationals. Let
`ell_k` denote this linear functional and let `q(L)` be the polynomial
candidate in the exact orthogonal center eigenbasis `Q`. For each k the
complete temporal polynomial `ell_k Qq(L)` is formed before interval
range evaluation, preserving cancellation between Fourier components.
The normalized candidate coefficients are divided by a certified norm
interval with lower endpoint one. The exact unit ground coefficient then
lies within an additional `||ell_k||_2*d`, where `d` is its certified unit
vector distance from the candidate.

Every exact unit Bernstein coefficient is above `1.189e-12` throughout
every subcell. The Bernstein basis functions are nonnegative on `[0,1]`
and sum to one, proving `r(t)>0` everywhere including the spatial
endpoints. Since `v_0>0` and `integral r=L v_0`,

```
r(t)/(L v_0)
```

is an even probability density and its characteristic function is the
origin-normalized ground Fourier profile.

## Entire real-zero profiles and the remaining convergence problem

Full ground simplicity makes `G=A-lambda I` positive on its quotient by
the ground vector. Boundary rigidity permits `e^T c=1`; the protected
Fourier origin permits profile normalization. The exact displacement
identity makes `T=omega J-omega Jc e^T` self-adjoint for the induced
positive quotient metric. Its quotient characteristic polynomial has
only real zeros. The sinc/determinant identity in the existing quotient
proof then establishes that the entire ground Fourier profile has no
nonreal zeros, at every support in this cell. Kernel positivity is an
additional conclusion; real-zero control uses the quotient argument.

This is a written algebraic/analytic proof with certified finite
hypotheses, not a Lean formalization. The source has neither checked roots
nor used Xi coefficients as inputs. These profiles are not identified
with Xi. Boundary rigidity alone gives no uniform parity theorem,
no infinite-rank kernel positivity, and no cumulative support/rank
convergence bound. The necessary `N/L^2 -> infinity` scaling for a Xi
limit remains only a necessary condition. The unbounded theta curvature
and interior all-rank budget are still open.

## Replay and independent checks

The [tests](../../experiments/prime_spectral/test_weil_full_cell.py) replay
the degree-64 even and odd certificates and spatial proof over the full
cover. Original integral matrices independently check every odd entry
at the cell center and boundaries, every odd entry derivative at both
one-sided prime boundaries, and all odd spectral bands there. Original
even eigenvectors independently check every spatial Bernstein interval at
both endpoints. Exact rational examples check the displacement identity
and the odd partner when a boundary-zero even eigenvector exists.
Synthetic crossings, an odd mode below the even ground, incomplete
covers, and unprotected origins fail the relevant gates.
The exact odd-resolvent reconstruction is independently checked against
the original even eigenvectors at both prime endpoints, with unit-vector
comparison error below `1e-40`.

Validation: the full 131-test prime-spectral regression suite passed in
212.257 seconds before adding the additional reconstruction test; that
test then passed independently in 2.195 seconds. All four new certificate
source hashes match, Python compilation passed, and `git diff --check`
passed. The certificates retain their input hashes and finite/open scope.

```sh
uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/prime_spectral -p test_weil_full_cell.py -v
```
