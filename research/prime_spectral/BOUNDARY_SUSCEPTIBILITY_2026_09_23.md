# Boundary susceptibility of the finite Weil ground state

The [fixed-support form-core audit](FIXED_SUPPORT_FORM_CORE_2026_09_23.md)
shows that the boundary-zero Ritz margin tends to zero as Fourier modes
grow. That fact alone says nothing about the ground eigenvector's
boundary value. An exact secular identity separates the two quantities
through a positive susceptibility. This note certifies the identity's
finite inputs at cutoff 13; it does not establish a uniform asymptotic.

## 1. Exact finite identity

Let `A` be a real symmetric even-mode matrix with simple lowest
eigenvalue `lambda_0<lambda_1`. Let `e_j` be an orthonormal eigenbasis,
`A e_j=lambda_j e_j`, and let `ell` be a nonzero real boundary
functional. Write `b_j=ell(e_j)`. Define

```
m = min_{0!=x in ker ell} <Ax,x>/||x||^2.
```

If `b_0!=0` and `lambda_0<m<lambda_1`, then the minimizing vector
satisfies `(A-mI)x=t*ell` for some nonzero multiplier `t`. Expanding
in the eigenbasis and imposing `ell(x)=0` gives

```
sum_j b_j^2/(lambda_j-m) = 0,
b_0^2/(m-lambda_0)
    = sum_(j>=1) b_j^2/(lambda_j-m) =: chi(m)>0.   (1)
```

Thus `b_0^2=(m-lambda_0)*chi(m)`. In complex coordinates replace
`b_j^2` by `|b_j|^2`. The right side is a positive higher-mode
resolvent quadratic form; no zeta zeros enter it. The identity is
undefined at an eigenvalue collision, so the computation below first
certifies the strict bracket `lambda_0<m<lambda_1`.

The boundary-zero margin may shrink while the ground boundary remains
nonzero, because `chi(m)` may grow. Conversely, an independently proved
lower bound on the product `(m-lambda_0)*chi(m)` would prove a boundary
lower bound. The form-core result supplies neither factor at the
precision needed along an unbounded support-and-mode family.

## 2. Certified cutoff-13 diagnostic

In the orthonormal even Fourier basis, `ell=(1,sqrt(2),...,sqrt(2))`.
The columns `e_j-sqrt(2)e_0`, `j=1,...,N`, span its kernel. The
implementation builds the restricted quadratic matrix `H=B^T A B`
and Gram matrix `G=B^T B`, then bisects the smallest generalized
eigenvalue by interval LDL inertia of `H-tG`. It checks the initial
bracket and fails if a pivot sign is unresolved. The unit ground
boundary is enclosed independently from the certified eigenvector;
exact rational endpoint arithmetic forms `chi=b_0^2/(m-lambda_0)`.

| Modes | Certified `m-lambda_0` | Certified `chi(m)` |
|---:|---:|---:|
| 4 | `(2.88677e-15, 2.88678e-15)` | `(73.7876, 73.7877)` |
| 8 | `(1.33255e-23, 1.33256e-23)` | `(152.2176, 152.2180)` |

The displayed decimal intervals are outward rounded from the saved
rational certificates. The ground boundary magnitudes are separately
certified near `4.61528e-7` and `4.50375e-11`. The spectral identity
then interprets the susceptibility intervals as the positive sums in
(1), without certifying every individual higher eigenpair. These two
finite configurations cannot establish monotonicity, a growth law, or
nonvanishing at an infinite limit.

Replay from the repository root:

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/boundary_susceptibility.py --certificate research/prime_spectral/certified_weil_13_4.json --output research/prime_spectral/boundary_susceptibility_13_4.json
uv run --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/boundary_susceptibility.py --certificate research/prime_spectral/certified_weil_13_8.json --output research/prime_spectral/boundary_susceptibility_13_8.json
uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/prime_spectral -p 'test_*.py' -q
```

## 3. What remains analytically necessary

One needs an eigenfunction-specific estimate of the boundary product,
or a way to avoid boundary normalization while retaining the finite
real-zero quotient and a nonzero Xi limit. Bounds on `m-lambda_0`
alone are insufficient: the previous form-core theorem proves that
this margin vanishes at fixed support. Bounds on `chi` alone are also
insufficient without the matching rate. Neither the small finite
boundary coordinates nor the profile comparisons prove that the
continuous ground state has a boundary trace.

[Suzuki's 2026 Theorem 1.4](https://arxiv.org/html/2606.09096v2)
establishes a simple even lowest Weil eigenfunction for sufficiently
small support. It does not supply the large-support theorem or the
prolate-to-Weil approximation required for RH. Those gates remain open.
