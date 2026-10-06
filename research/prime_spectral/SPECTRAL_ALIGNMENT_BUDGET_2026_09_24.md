# Spectral alignment in one coupled rank increment

The [coupled Schur recurrence](COUPLED_RANK_SCHUR_RECURRENCE_2026_09_24.md)
expresses a nested-rank profile change as `-f_z^* T^{-1}r`, where `T` is
the positive origin-constrained block and `r` contains both the old
eigenvalue shift and the new-mode forcing. A single Cauchy-Schwarz
estimate mixes the Fourier energy in one eigendirection with the
residual energy in another. That accounts for its large overestimate
in the cutoff-13, rank-4-to-8 example.

For any partition of the spectrum of `T` into orthogonal projections
`E_B`, spectral calculus and Cauchy-Schwarz **within each band** give

```
|f_z^* T^-1 r|
  <= sum_B sqrt((f_z^* T^-1 E_B f_z) (r^* T^-1 E_B r)).      (1)
```

For simple eigenpairs `(tau_j,u_j)`, the singleton-band bound is

```
|f_z^* T^-1 r|
  <= sum_j |<f_z,u_j><r,u_j>|/tau_j.                         (2)
```

Both inequalities are exact finite-dimensional statements. The
triangle inequality in (2) still loses cancellation **between**
eigenmodes, but preserves the alignment of the two factors within
each eigenmode. The global Cauchy bound instead multiplies two sums
before checking their alignment.

The [512-bit interval calculation](spectral_alignment_13_4_8.json)
isolates all eight positive simple eigenvalues of the rank-8
constrained block using Rump eigenpairs. It bounds the individual
terms in (2), checks their signed sum against the direct Schur solve,
and replays the same centered Fourier functional as the rank
recurrence. Its outward bounds are:

| Argument | Actual change, approximately | Singleton absolute sum upper | Bound/actual upper | Global Cauchy upper |
|---|---:|---:|---:|---:|
| `z=4` | `0.1269438203` | `0.1269438295` | `1.000000072` | `25.66949` |
| `z=8` | `0.0817765839` | `0.1077941966` | `1.318155` | `21.23005` |
| `z=i` | `0.0145581139` | `0.0145587697` | `1.000046` | `2.711853` |

The same generator now replays [rank 8 to 12 at support 13](spectral_alignment_13_8_12.json)
and [rank 4 to 8 at support 17](spectral_alignment_17_4_8.json)
and [19](spectral_alignment_19_4_8.json). The ratios of singleton bound
to certified signed change at real frequency 4 are respectively
`1.00000057`, `1.00000011`, and `1.00005945`; at real frequency 8
they are `1.074402`, `1.496382`, and `1.571667`. Thus alignment
remains useful in these finite cases, but its quality at frequency 8
does **not** improve monotonically with the support cutoff.

At support 13, rank 8 to 12, a direct interval inversion encloses the
real-frequency-4 change with width greater than `6900`, reflecting
extreme conditioning. The spectral signed sum encloses the same change
with width below `2.2e-8`. The script therefore computes the global
Cauchy comparison from positive spectral energies and uses the signed
spectral enclosure for its ratio. It retains the direct inverse as an
overlap check; this is a numerical-stability improvement, not a new
mathematical assumption.

These are bounds for **four finite pairs at three supports**. In
particular, the good alignment at these three arguments says nothing
about all ranks and supports, or an entire compact subset of the
critical strip. The next missing estimate is a support-uniform
summable bound on the band pairings in (1), or directly on their
signed sum, along an increasing rank/support path. The exact
rank-energy identity alone cannot provide it: it controls only the
residual factor, while the Fourier dual factor can grow sharply in
soft eigendirections. No all-rank profile budget or RH proof follows.

Replay with:

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/spectral_alignment.py --first research/prime_spectral/certified_weil_13_4.json --second research/prime_spectral/certified_weil_13_8.json --output research/prime_spectral/spectral_alignment_13_4_8.json
uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/prime_spectral -p test_spectral_alignment.py -v
```
