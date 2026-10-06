# Certifying the exact prolate modes from a finite Jacobi section

The [finite exclusion radii](PROLATE_CANDIDATE_GATE_2026_09_23.md)
apply to the exact prolate projection once that projection has an
interval enclosure. The prolate differential operator admits a
simple tail certificate in the orthonormal even Legendre basis. This
note proves the spectral part; the separate analytic-projection and
error-transfer certificates complete the cutoff-13 finite check.

Fix `C=lambda^2`, put `c=2*pi*C`, and let `J` be the Jacobi matrix of
`-d/dz[(1-z^2)d/dz]+c^2*z^2` on even functions of `[-1,1]`.
Index the normalized Legendre functions by `k>=0`, meaning degree
`2k`. With `a_0=0` and
`a_l=l/sqrt((2l-1)*(2l+1))` for `l>=1`, its entries are

```
J_(k,k) = (2k)*(2k+1)+c^2*(a_(2k)^2+a_(2k+1)^2),
J_(k,k+1) = c^2*a_(2k+1)*a_(2k+2).              (1)
```

Let `A_M` be the leading `M`-by-`M` block and `D_M` the tail.
Because multiplication by `z^2` is positive and the Legendre
differential part is diagonal,

```
D_M >= d_M*I,   d_M=(2M)*(2M+1).               (2)
```

The only coupling between the two blocks is
`beta_M=c^2*a_(2M-1)*a_(2M)`, from the last retained coordinate
to the first tail coordinate. For any `b<d_M`, set

```
tau_M(b)=beta_M^2/(d_M-b).                      (3)
```

Write the eigenvalues of `A_M` as `alpha_0<=alpha_1<=...` and the
discrete eigenvalues of the full even operator as
`lambda_0<=lambda_1<=...`. For every `j` with `alpha_j<b`,

```
alpha_j-tau_M(b) <= lambda_j <= alpha_j.       (4)
```

The upper bound is min-max on the first `M` coordinates. For the
lower bound, at any `s<=b` the tail block `D_M-s` is positive and
the negative inertia of `J-s` equals that of its Schur complement

```
A_M-s-B*(D_M-s)^(-1)*B^*.
```

The correction lies between zero and `tau_M(b)*I`. Thus no `j`th
eigenvalue can lie below `alpha_j-tau_M(b)`. This argument uses the
infinite tail as an operator inequality; a tiny last Legendre
coefficient alone would not establish (4).

There is also a direct eigenfunction-error gate. Embed a normalized
finite trial vector `v` in the infinite coefficient space, choose
any trial eigenvalue `mu`, and calculate

```
rho^2=||(A_M-mu)v||_2^2+beta_M^2*|v_(M-1)|^2. (5)
```

Suppose interval bounds from (4) isolate a simple `lambda_j` and
place every other eigenvalue at distance at least `Delta>0` from
`mu`. Spectral decomposition then gives, after orienting its unit
eigenvector `psi_j` toward `v`,

```
||v-psi_j||_2 <= sqrt(2)*rho/Delta.            (6)
```

Equations (1)–(6) are suitable for Arb evaluation: interval
eigenvalue brackets for `A_M`, a high-precision rational trial
vector, and a rational/ball residual in (5) suffice. Once both
`psi_0` and `psi_4` are enclosed in `L2`, the bounded finite-window
map `E` and exact cosine-projection integral formula can transfer
those errors to the candidate coefficient vector. The target is the
strict unit-vector radius in `robust_prolate_gate_13_4.json` or
`robust_prolate_gate_13_8.json`.

At `C=13`, `M=80`, the [256-bit Arb certificate](prolate_jacobi_13_80.json)
uses 96 exact-dyadic Sturm bisections per finite eigenvalue and an
outward-rounded Schur shift. Its readable approximations are

```
d_M=25760, beta_M approximately 1667.98,
alpha_0,...,alpha_3 approximately
  80.9291, 404.6216, 724.2176, 1039.6346.
```

With `b=1500`, the certified upper bound in (3) is approximately
`114.681`. The exact rational interval endpoints in the JSON imply
that the first four full-even eigenvalue intervals are disjoint, with
consecutive gaps greater than `209.0`, `204.9`, and `200.7`.
In particular, the first and third even prolate eigenvalues are
simple and isolated at this cutoff. The [trial-vector certificate](prolate_vectors_13_80.json)
then replays the Jacobi isolation and evaluates (5) with Arb on
saved 75-digit decimal vectors. Its approximate outward bounds are:

| Even prolate index | Residual norm upper | Distance to other eigenvalues lower | Oriented unit-vector error upper |
|---:|---:|---:|---:|
| 0 | `1.240e-53` | `209.0` | `8.388e-56` |
| 2 (Hermite label 4) | `1.453e-49` | `200.7` | `1.024e-51` |

These are enclosures of the **exact infinite-dimensional prolate
eigenfunctions in the Legendre `L2` basis**. They are far smaller than
the finite Weil exclusion radii. The
[closed-form Arb projection](prolate_projection_trial_13_4.json) and
[error transfer](exact_prolate_gate_13_4.json) now place the exact
candidate inside the mode-4 exclusion radius; corresponding
[mode-8 projection](prolate_projection_trial_13_8.json) and
[transfer](exact_prolate_gate_13_8.json) do the same. This certifies
failure of the Rayleigh-below-second-even test only for those finite
spaces, without an increasing-support conclusion.

Replay from the repository root:

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/certified_prolate_jacobi.py --cutoff 13 --terms 80 --tail-cut 1500 --output research/prime_spectral/prolate_jacobi_13_80.json
uv run --with python-flint==0.8.0 --with mpmath --python 3.12 python experiments/prime_spectral/certified_prolate_vectors.py --jacobi research/prime_spectral/prolate_jacobi_13_80.json --output research/prime_spectral/prolate_vectors_13_80.json
uv run --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/exact_prolate_finite_gate.py --certificate research/prime_spectral/certified_weil_13_4.json --candidate research/prime_spectral/prolate_candidate_13_4.json --jacobi research/prime_spectral/prolate_jacobi_13_80.json --vectors research/prime_spectral/prolate_vectors_13_80.json --output research/prime_spectral/exact_prolate_gate_13_4.json
```
