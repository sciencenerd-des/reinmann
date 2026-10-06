# Uniform even eigenfamily on the full 17–19 support cell

Update: the [degree-64 full-cell audit](WEIL_FULL_CELL_GATES_2026_10_05.md)
subsequently closes the odd-parity, nonzero spatial-boundary and positive
kernel gates on this same cell. This note records the original degree-48
even certificate and its scope.

The [matrix Taylor certificate](CLOSED_WEIL_TAYLOR_CELL_2026_10_05.md)
now yields a validated **even** eigenfamily over the entire support cell
`17<=C<=19`, at Fourier rank `8`. The [generator](../../experiments/prime_spectral/weil_eigenfamily.py)
checks 32 adjacent subcells using a common certified matrix polynomial,
coupled polynomial residuals, and a uniform spectral separation test.
This identifies the lowest eigenvalue of the even block. The odd block
has not been enclosed over this cell, so identification with the least
eigenvalue of the full Weil matrix remains a separate gate.

## Precision repair before validation

The previous coefficient enclosures were valid but too wide for this task.
In `python-flint==0.8.0`, direct calls to `acb_series.sin()` and `.cos()`
were observed to give constant-coefficient radii around `1e-16` at requested
1024-bit precision. For example, the sine series at constant coefficient
`1` had radius approximately `1.127e-16`. Series exponentials retained
the requested precision. The Taylor generator now uses the exact identities

```
sin z = [exp(i z)-exp(-i z)]/(2i),
cos z = [exp(i z)+exp(-i z)]/2.
```

Its regenerated constant matrix coefficients have maximum width below
`1.626e-188`. Regression tests check scalar sine/cosine values, first
derivatives, and more than 480 bits of coefficient accuracy at a requested
512 bits. They also bound every saved coefficient radius below `1e-140`.
The analytic Taylor truncation bounds alone would not have removed the
earlier coefficient uncertainty.

## Coupled polynomial candidate construction

Let `A(L)` be the real symmetric even block and `P(L)` the polynomial
obtained by choosing exact dyadic midpoints of its certified coefficients.
The coefficient radii and the analytic tail are both included in an
outward operator bound `||A(L)-P(L)||<=epsilon` over the full cell.

On each subcell, translate this same polynomial to its local center.
FLINT's certified Rump algorithm isolates all center eigenvalues and
eigenvectors; the [official routine documentation](https://github.com/flintlib/flint/blob/main/doc/source/acb_mat.rst)
states the isolation and eigenvector enclosure guarantees on success.
The real normalized center eigenvectors define an exact
orthogonal matrix `Q`; their interval enclosures are retained. Write
`B(L)=Q^T P(L)Q`. Its constant coefficient is exactly
`diag(lambda_0,...,lambda_8)`, by symmetric spectral theory. This identity
is used before interval arithmetic on the higher coefficients.

For branch `i`, construct a polynomial vector `q_i` with anchor coordinate
`(q_i)_i=1` and a polynomial eigenvalue `ell_i`. The coefficient recurrence
proposes candidates in the diagonal center basis. Its calculated
coefficients are rounded to exact dyadic numbers. No convergence theorem
for this recurrence is assumed: the complete candidate is validated by
its residual against `B`.

One predictor centered on the entire cell failed validation: its higher
coefficients grew too fast at the full half-width. Translating the matrix
polynomial onto 32 subcells controls the validated residual. The
subdivision count is part of the certificate, not a sampled sign test.

## Uniform residual and eigenvalue isolation theorem

For any parameter in a subcell, put the candidate vectors into columns
of `U`, put their candidate eigenvalues into `Lambda=diag(ell_i)`, and
form the polynomial residual

```
E_poly = B U - U Lambda.
```

Products and differences are performed coefficient by coefficient before
enclosing the support displacement. Bounds on the full polynomial
residual, including its coefficients above candidate degree 48, are then
combined with `epsilon*||q_i||_2` for the true matrix remainder. This
gives an outward bound on the true residual `E`.

If `beta>=||U-I||_infinity` and `beta<1`, the Neumann series gives
`||U^(-1)||_infinity<=1/(1-beta)`. Consequently

```
U^(-1) Q^T A Q U = Lambda + U^(-1) E,
eta = ||E||_infinity/(1-beta).
```

Gershgorin's theorem puts the eigenvalues in disks of radius `eta`
around `ell_i`. If every adjacent candidate range is separated by more
than `2*eta`, the disks are pairwise disjoint, each contains exactly one
eigenvalue, and the branches retain their order throughout the subcell.
The true eigenvalues are real because `A` is symmetric. This proves
uniform isolation, rather than inferring it from isolation at the centers.

All 32 subcells pass. The [saved certificate](weil_eigenfamily_17_19_8.json)
has the following outward consequences across the complete cell:

| Quantity | Certified bound, rounded outward |
|---|---:|
| `||U-I||_infinity` | `< 0.01633` |
| Eigenvalue disk radius | `< 1.240e-29` |
| Lowest even eigenvalue | `> 2.258e-26` |
| Gap from lowest to second even eigenvalue | `> 2.378e-20` |
| Exact-to-candidate unit even ground-vector distance | `< 2.416e-10` |
| Exact unit even ground-vector zeroth Fourier coordinate | `> 0.5753099` |

## Uniform origin-normalized profile transfer

Let `v_hat=Q q_0`. Its norm is at least one because its center-basis
anchor coordinate is identically one. Let `rho` bound
`||A v_hat-ell_0 v_hat||_2`, and let `D` be the uniform clearance
between the second exact eigenvalue and `ell_0`. Projecting the residual
onto the non-ground spectral subspace gives

```
distance(unit(v_hat), unit(v_ground)) <= sqrt(2)*rho/D = d,
```

after choosing the ground orientation toward the candidate. The verified
origin bound protects a unique positive-origin orientation everywhere.
If the unit candidate origin is at least `c>d`, the exact unit ground
origin is at least `c-d`. The established Fourier-functional norm on
`|Im z|<=sigma` is `W=sqrt(sinh(sigma*L)/(sigma*L))`, so

```
sup_(|Im z|<=sigma) |P_ground(L,z)-P_candidate(L,z)|
    <= W*d/(c-d)*(1+1/c).
```

Using `sigma=2/5` and `L<=log 19`, every subcell passes the protected-origin
gate. The uniform bound across the whole cell, for **all real parts** of
`z`, is

```
|P_even_ground(L,z)-P_candidate(L,z)| < 1.285e-9,
17<=C<=19,  |Im z|<=2/5.
```

This is comparison with the validated piecewise polynomial candidate,
not with the canonical prolate candidate or Xi. The exact even ground
family is continuous throughout the cell and analytic in its interior;
the local polynomial candidates need not agree exactly at subdivisions.

Analyticity also follows directly from the analytic implicit-function
theorem. In origin coordinates, a kernel vector of the eigenpair Jacobian
satisfies `(A-lambda I)dv=dlambda*v` and `dv_0=0`. Multiplication by
`v^T` gives `dlambda=0`; simplicity then gives `dv=a*v`, and the nonzero
origin forces `a=0`. The Jacobian is invertible. The protected origin fixes
the same orientation on overlaps, so these local analytic branches patch
to the exact even ground family.

## Boundary checks and remaining proof obligations

The closed prime branch includes `17` and excludes `19`. Matrix values
are continuous at both endpoints. It uses the right branch at `17` and
the left branch at `19`; the existing prime-threshold certificates supply
the derivative jumps to the neighboring branches.

The [tests](../../experiments/prime_spectral/test_weil_eigenfamily.py)
replay every subcell and compare ground eigenvalues, eigenvectors and
origin-normalized profiles with independently evaluated original integral
matrices at both prime boundaries and the whole-cell center. A synthetic
spectral crossing is rejected by the uniform separation gate. The
original matrix-Taylor boundary derivative checks remain in place.

The remaining finite work includes the odd-parity comparison, a uniform
nonzero spatial boundary evaluation and kernel positivity gate, derivative
propagation to the exact ground profile, and an effective integrated
profile budget. The protected Fourier origin proved here is distinct
from the spatial boundary evaluation used by the quotient construction.
The all-support/all-rank estimates and identification of
the spectral limit with Xi remain open. This finite eigenfamily does not
prove the uniform theta-curvature claim or RH.

Replay:

```sh
uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/prime_spectral -p test_weil_eigenfamily.py -v
```
