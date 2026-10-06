# Signed spectral deflation of a coupled rank response

The [generator](../../experiments/prime_spectral/deflated_rank_response.py)
extracts certified low-mode responses before bounding the remaining positive
energy. This removes most of the amplification in the finite experiments.
It does not prove a cumulative all-rank profile budget or RH.

## Exact coupled source and energy

Fix a support and write the even rank-M Weil matrix as
`A_M=[[a,b^T],[b,C_M]]`, with origin-normalized lowest eigenvector
`v_M=(1,h_M)` and eigenvalue `lambda_M`. Assume the ground is simple and
its origin coordinate is nonzero. Then `T_M=C_M-lambda_M I` is positive
definite: equality in the lowest Rayleigh inequality would force an
origin-zero vector to be a multiple of the ground.

For a nested rank N<M, extend `v_N` by zero and put

```
delta=lambda_N-lambda_M,
r=(delta*h_N, d+E^T*h_N),
dH=(h_N,0)-h_M=T_M^-1 r.
```

Here `(d,E^T)` is the new-rows/old-columns block of `A_M`.
The old-coordinate eigenvalue shift and new-mode forcing belong to one
source. They are combined before any absolute-value bound.
The independent exact energy identity is

```
E=r^T T_M^-1 r=delta*||v_N||^2.
```

Indeed `dH` has zero origin coordinate, the full ground annihilates
`A_M-lambda_M I`, and the Rayleigh energy of the extended `v_N` is
`delta*||v_N||^2`. The profile change is `-f_z(dH)`.

## Deflate only the dangerous inverse directions

Let `q_k` be an orthonormal eigenbasis of `T_M`, with
`0<mu_0<...<mu_(M-1)` and `alpha_k=<q_k,r>`. Choose `0<=m<M` and form

```
u_low=sum_(k<m) q_k*alpha_k/mu_k,
E_perp=E-sum_(k<m) alpha_k^2/mu_k
      =sum_(k>=m) alpha_k^2/mu_k >=0.
```

For every complex Fourier functional, Cauchy–Schwarz in the positive
inverse quadratic form gives

```
|f_z(T_M^-1 r)-f_z(u_low)|
 <= sqrt[E_perp * sum_(k>=m) |f_z(q_k)|^2/mu_k].       (1)
```

The signed low-mode sum is evaluated before its magnitude. Opposing low
responses can cancel. The complementary energy is enclosed both by its
modal sum and by the independent energy difference; the smaller valid
upper bound is used. Only the complement is transferred by Cauchy–Schwarz.

Orthogonality also gives the uniform vector estimate

```
||T_M^-1 r||^2
 <= sum_(k<m) alpha_k^2/mu_k^2 + E_perp/mu_m.          (2)
```

Combining (2) with the established Fourier-functional norm bound
`W_sigma(L)=sqrt[sinh(sigma L)/(sigma L)]` bounds the profile increment
for **every real part** on the entire closed strip `|Im z|<=sigma`.
The two squared vector contributions are added before taking a square root.

## Certified finite outcomes

Both experiments use cutoff 13, two deflated constrained modes, 1024-bit
Arb arithmetic, the original interval Weil matrix, and certified Rump
eigenpair isolation. Neither computes a model replacement for that matrix.

| Rank transition | Fourier point | Whole-energy upper, approximate | Deflated absolute upper | Complement radius upper, approximate |
|---|---|---:|---:|---:|
| 4→8 | 4 | 25.6695 | <0.127438 | 0.001041946 |
| 4→8 | 8 | 21.2300 | <0.083024 | 0.000827491 |
| 4→8 | i | 2.71185 | <0.014757 | 0.000429928 |
| 8→12 | 4 | 3.23569 | <0.046222 | 0.000060768 |
| 8→12 | 8 | 3.34863 | <0.044270 | 0.000061515 |
| 8→12 | i | 0.317437 | <0.004665 | 0.000018416 |

The whole-strip height-1 bounds are `<0.428404` for 4→8 and `<0.183786`
for 8→12. These are finite rank-increment bounds at one support.
The [4→8](deflated_rank_response_13_4_8.json) and
[8→12](deflated_rank_response_13_8_12.json) certificates save signed
projections, full constrained spectra, independent energy enclosures,
and complementary dual energies. Tests compare the resulting intervals
with separately solved origin-normalized ground-profile differences.
An exact diagonal example checks cancellation of two nonzero low-mode
terms while complementary source energy remains positive.

## An all-rank bound on the number of dangerous modes

There is a useful rank-uniform consequence of the
[infinite-tail/coercivity estimate](WEIL_INFINITE_RANK_TAIL_2026_10_06.md),
even though it does not give an all-rank budget.
Throughout the **different support cell** `17<=C<=19`, the even compression
onto indices `j>=n*=18,612,929` exceeds the identity. The complete rank-8
eigenfamily enclosure gives

```
lambda_8(C) < 1.380e-24.
```

For every finite M>=8, nested Rayleigh minimization implies
`lambda_M(C)<=lambda_8(C)`, without requiring full-matrix positivity.
Consequently the corresponding high-index compression of
`T_M=C_M-lambda_M I` has lower bound

```
kappa=1-1.380e-24 >0.
```

Its codimension in the origin-constrained space is
`d=n*-1=18,612,928` whenever M>d. For any real symmetric T with a
codimension-d subspace on which its Rayleigh quotient is at least kappa,
the (d+1)-st ordered eigenvalue is at least kappa. To see this, intersect
that subspace with the span of the first d+1 eigenvectors. The intersection
is nonzero by dimension counting. Its Rayleigh quotient is simultaneously
at least kappa and at most the (d+1)-st eigenvalue.

Thus at most d constrained modes lie below kappa, **independently of M**,
uniformly over this closed support cell. Both prime-power endpoints are
included by the input matrix and eigenfamily certificates. For M<=d the
count bound is vacuous. This does not assert positive low eigenvalues:
positivity and invertibility of T still require the ground hypotheses.
No matrix of size n* was constructed. No infinite ground-state convergence
is used in this finite-dimensional theorem.

This gives an effective, conservative finite-dimensional reduction of the
dangerous inverse spectrum on a fixed support cell. It does not bound the
signed source projections onto that low spectral space, protect the
origin for all ranks, or control increasing supports. The threshold from
17–19 is not applied to the cutoff-13 examples.

## Remaining cumulative estimate

For rank steps indexed by j, a sufficient budget would be

```
sum_j W_sigma(L_j)
       *sqrt[sum_low alpha_(j,k)^2/mu_(j,k)^2
             +E_(j,perp)/mu_(j,m)] < infinity,
```

together with the support increments, prime-threshold boundary control,
and ground/origin hypotheses along the path. Low inverse projections,
not merely the count of low eigenvalues, must be controlled. The exact
telescoping eigenvalue-energy identity does not imply this square-root
sum converges. No finite table supplies that missing estimate.

The theta reference-curvature theorem, interior all-rank budget,
prime-profile identification with Xi, and RH remain open. These spectral
lemmas and certificates are not Lean-formalized.

Verification on 2026-10-06: all 154 prime-spectral unit tests passed in
227.066 seconds. New certificate input/source hashes, Python compilation,
note links, and whitespace checks passed. The test run is finite
verification; the arbitrary-rank spectral-count statement uses the written
dimension-counting argument above.
