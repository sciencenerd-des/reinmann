# Exact finite prolate-to-ground alignment and the strip-rate target

The [low-cluster certificate](PROLATE_LOW_CLUSTER_2026_09_24.md)
places the exact projected prolate candidate mostly in the bottom
four-dimensional even Weil eigenspace at cutoff 13. It does not say
how the candidate is oriented **within** that cluster. This note
measures its overlap with the uniquely selected finite ground
eigenvector and transfers the resulting coefficient difference to
the critical strip.

For each saved Fourier rank, the [interval generator](../../experiments/prime_spectral/prolate_ground_alignment.py)
replays the exact prolate and Weil certificates, isolates the simple
ground eigenvector by Rump's method, and orients both unit vectors
with positive zeroth Fourier coordinate. The certified prolate
eigenfunction-to-trial error is then added to the interval vector
comparison. This is a direct finite comparison; it does not infer
ground alignment from the failed Rayleigh-below-second gate.

| Cutoff 13 modes | Unit prolate-to-ground distance upper | Squared non-ground mass upper | Coupled profile bound on `|Im z|<=2/5` |
|---:|---:|---:|---:|
| 4 | `0.257607` | `0.065261` | `0.581306` |
| 8 | `0.123204` | `0.015122` | `0.292510` |
| 12 | `0.068783` | `0.004726` | `0.166917` |
| 16 | `0.041816` | `0.001748` | `0.102617` |

The squared mass is `1-|<v,w>|^2`, bounded using the oriented
overlap of the exact unit prolate vector `w` with the finite unit
ground vector `v`. The original generic unit-distance strip bound
is larger (respectively `2.832`, `0.918`, `0.454`, `0.261`). To keep
the cancellation from origin normalization, the tighter bound
computes the coefficient vector

```
d = v/v_0 - w/w_0,
sup_(|Im z|<=sigma)|P_v(z)-P_w(z)|
    <= sqrt(sinh(sigma*L)/(sigma*L))*||d||_2,          (1)
```

and transfers the tiny certified trial-to-exact prolate error
separately. The zeroth coordinate of `d` is **exactly zero**.
This is why the coupled bounds are much smaller than applying
triangle inequalities to the two unit vectors and denominators.

At selected arguments, the certificates also enclose the signed
ground-minus-exact-prolate profile difference:

| Modes | At `z=4`, approx. | At `z=8`, approx. | At `z=i`, approx. |
|---:|---:|---:|---:|
| 4 | `-0.228309` | `-0.191924` | `+0.024015` |
| 8 | `-0.100597` | `-0.108206` | `+0.009768` |
| 12 | `-0.054401` | `-0.064032` | `+0.005111` |
| 16 | `-0.032557` | `-0.039973` | `+0.003013` |

These are certified finite intervals, not just the earlier floating
distance trend. The [rank-4](prolate_ground_alignment_13_4.json),
[rank-8](prolate_ground_alignment_13_8.json),
[rank-12](prolate_ground_alignment_13_12.json), and
[rank-16](prolate_ground_alignment_13_16.json) files contain the
outward rational endpoints, hashes, and strip bounds. The rank-4
and rank-8 ground profiles agree with the independent origin-Schur
certificates; rank 12 agrees with the independent least-eigenvalue
response certificate.

## What an all-support result would need

Let `C` grow, `L=log C`, and choose a rank path `N(C)` on which the
prolate candidate profile tends to `Xi(z)/Xi(0)` as established for
the candidate by the [finite-Fourier diagonal](PROLATE_FOURIER_DIAGONAL_2026_09_23.md).
For ground and prolate unit vectors on that path, put

```
D_C=||v_(C,N)/v_(C,N)[0]-w_(C,N)/w_(C,N)[0]||_2.
```

For every fixed `sigma<1/2`, (1) would transfer that limit to the
ground profiles if

```
D_C*sqrt(sinh(sigma*log C)/(sigma*log C)) -> 0.    (2)
```

For example, the **sufficient** support-uniform estimate
`D_C=O(C^-1/4)` makes (2) hold on every closed substrip of
`|Im z|<1/2`. The finite data here are all at `C=13` and provide
no such estimate. The later [cross-support comparison](CROSS_SUPPORT_PROLATE_RANK_SCALING_2026_09_26.md)
tests cutoffs 17 and 19 at ranks 8, 12, and 16, still without a
support-uniform estimate. Even if (2) were proved, the finite real-zero and
simple-even gates would still need to hold along the same path.
The [full Weil semigroup sign obstruction](SEMIGROUP_SIGN_OBSTRUCTION_2026_09_23.md)
also prevents a direct large-support Perron-Frobenius shortcut for
selecting the ground direction within the cluster. RH remains open.

Replay with:

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/prolate_ground_alignment.py --exact-gate research/prime_spectral/exact_prolate_gate_13_16.json --spectrum research/prime_spectral/isolated_kernel_13_16.json --cluster research/prime_spectral/prolate_cluster_13_16.json --jacobi research/prime_spectral/prolate_jacobi_13_80.json --vectors research/prime_spectral/prolate_vectors_13_80.json --output research/prime_spectral/prolate_ground_alignment_13_16.json
uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/prime_spectral -p test_prolate_ground_alignment.py -v
```
