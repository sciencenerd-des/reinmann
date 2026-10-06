# A gap-free eigenvalue-response bridge for prime spectral profiles

The [strip residual theorem](STRIP_RESIDUAL_TRANSFER_2026_09_23.md)
compares a candidate with the finite Weil ground vector using the
second eigenvalue gap. The [coupled rank recurrence](COUPLED_RANK_SCHUR_RECURRENCE_2026_09_24.md)
instead estimates ground profiles directly. There is a third exact
description: each origin-normalized ground profile is a **ratio of
directional derivatives of the least eigenvalue**. This removes the
gap from the *finite identity*, though a uniform limit of the
responses remains open.

Let `A_N` be a real symmetric even Weil matrix with a simple lowest
eigenvalue and unit real ground vector `v_N`, oriented with
`v_N[0]>0`. Let `e=e_0`, and let `f_{N,z}` be the centered Fourier
functional in the same orthonormal basis, so
`P_N(z)=f_{N,z}^T v_N/v_N[0]`. For a real vector `q`, define

```
H_q=e q^T+q e^T,
Lambda_N(q;t,s)=lambda_min(A_N+t H_q+s e e^T).
```

The simple-eigenvalue perturbation formula gives

```
partial_t Lambda_N(q;0,0)=2 v_N[0] q^T v_N,
partial_s Lambda_N(q;0,0)=v_N[0]^2>0.                 (1)
```

Consequently, for real `z`, or for the real and imaginary parts of a
complex Fourier functional separately,

```
P_N(z)=partial_t Lambda_N(f_{N,z};0,0)
       /(2 partial_s Lambda_N(f_{N,z};0,0)).         (2)
```

The denominator response is independent of `z`. It equals
`1/||v_N/v_N[0]||^2`. The [Parseval obstruction](ORIGIN_NORM_TIGHTNESS_OBSTRUCTION_2026_09_24.md)
shows why this response may shrink with increasing support. A
limit theorem must control the **ratio**, or rescale both responses
by the same factor; convergence of their unscaled difference to
zero would be uninformative.

## Certified secants without eigenvectors

For any real symmetric perturbation `H`, the function
`g(t)=lambda_min(A_N+tH)` is concave as an infimum of affine
Rayleigh quotients. Thus, for every rational `h>0`,

```
[g(h)-g(0)]/h <= g'(0) <= [g(0)-g(-h)]/h.         (3)
```

Apply (3) with `H_q` and with `H_(e/2)=e e^T`; if the lower origin
secant is positive, divide the resulting outward derivative
intervals to enclose (2). This certificate needs no eigenvector
interval, gap estimate, or inverse of `A_N-lambda_N I`. Its
independent inputs are three certified least-eigenvalue intervals
per perturbation, obtained by interval LDL inertia.

The [mode-4](eigenvalue_response_13_4.json),
[mode-8](eigenvalue_response_13_8.json), and
[mode-12](eigenvalue_response_13_12.json) certificates at support
13 use rational steps `10^-17`, `10^-25`, and `10^-30`. Their profile
intervals overlap the independently certified origin-Schur profiles
at ranks 4 and 8. At rank 12 they overlap the rank-8 profile plus
the independently isolated [signed spectral increment](spectral_alignment_13_8_12.json).

| Modes | `P_N(4)` certified interval, approximately | Interval width upper |
|---:|---:|---:|
| 4 | `[0.4773937697, 0.4773937728]` | `3.1e-9` |
| 8 | `[0.6043375904, 0.6043375928]` | `2.3e-9` |
| 12 | `[0.6505327798, 0.6505328270]` | `4.8e-8` |

These finite profiles are still changing substantially with rank.
The mode-12 secant calculation is useful as an interval method:
the direct Schur inverse on that matrix has a width above `6900`
for the rank-8-to-12 real-frequency-4 change, whereas the response
ratio remains sharp.

## A precise infinite-dimensional target

For a sequence of finite matrices, choose any positive scalars
`a_j`. Set

```
G_(j,q)(t,s)=a_j*(Lambda_j(q;t,s)-Lambda_j(q;0,0)).
```

Suppose, for each Fourier functional under consideration, these
concave functions converge pointwise in a fixed neighborhood of
`(0,0)` to functions differentiable at the origin, and the common
origin-response limit has strictly positive `s` derivative. Then
the finite derivatives in (1) converge, and their ratios converge
to the ratio of limiting derivatives. The proof needs no uniform
finite spectral gap: for each coordinate direction, the two secants
in (3) sandwich the derivative; take the `j` limit at fixed `h`
and then let `h` decrease to zero.

For RH one would additionally have to identify those limiting
ratios with `Xi(z)/Xi(0)` throughout the critical strip and prove
local uniform convergence of the analytic profiles, for example
through a local normal-family bound. Neither the response-surface
limit nor its Xi identification is known here. The finite
certificates do not supply either condition. Equation (2) is a
gap-free **reformulation of the missing comparison**, not a proof
that it holds.
The [coupled rank-response determinant](COUPLED_RESPONSE_DETERMINANT_2026_09_24.md)
identifies the scalar cross-derivative that must be summable across
ranks, and documents how the shrinking finite gaps force smaller
secant steps in the current experiments.

Replay with:

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/eigenvalue_response.py --certificate research/prime_spectral/certified_weil_13_12.json --step 1e-30 --output research/prime_spectral/eigenvalue_response_13_12.json
uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/prime_spectral -p test_eigenvalue_response.py -v
```
