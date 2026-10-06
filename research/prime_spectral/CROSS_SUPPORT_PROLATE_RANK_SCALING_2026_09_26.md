# Cross-support prolate-to-Weil ground comparison

The exact zero-integral prolate candidate and the prime-defined even Weil
ground vector can be compared in the **same** finite Fourier space. The
[ground-alignment generator](../../experiments/prime_spectral/prolate_ground_alignment.py)
uses a certified Jacobi eigenfunction error, exact Fourier projection,
Rump-isolated Weil eigenvectors, and interval arithmetic. Both unit vectors
are oriented by a positive zeroth Fourier coordinate. The cluster Rayleigh
gate is optional because a direct vector comparison does not require it.

For the exact projected prolate unit vector `w` and Weil ground unit vector
`v`, the generator now encloses both `||v-w||_2` and
`||v/v_0-w/w_0||_2`. Its trial-to-exact error is included in **both**
directions. The latter norm controls the origin-normalized Fourier profiles
on a strip by the Fourier evaluation norm
`sqrt(sinh(sigma log C)/(sigma log C))`.

The two-sided transfer is elementary and preserves the cancellation at
the zeroth mode. If `t` is the certified trial unit vector,
`||w-t||_2<=epsilon`, and `a<=t_0` with `a>epsilon`, then

```
| ||v-w||_2 - ||v-t||_2 | <= epsilon,
||w/w_0 - t/t_0||_2 <= epsilon/(a-epsilon)*(1+1/a).
```

Applying the reverse triangle inequality to the second line encloses
`D_(C,N)` from below as well as above. This is stronger than inferring
ground alignment from a Rayleigh quotient or taking separate bounds on
two origin-normalized profiles.

The following are decimal displays of certified rational endpoints; the
linked JSON files contain the full outward enclosures and provenance.

| Cutoff `C` | Rank `N` | `||v-w||_2` (rounded) | `D_(C,N)` (rounded) | Coupled strip upper | Four-mode cluster gate |
|---:|---:|---:|---:|---:|---|
| 13 | 8 | `0.123203796` | `0.268718737` | `0.292509643` | passes |
| 13 | 12 | `0.068782428` | `0.153340806` | `0.166916773` | passes |
| 13 | 16 | `0.041815177` | `0.094270498` | `0.102616700` | passes |
| 17 | 8 | `0.160532864` | `0.361609614` | `0.400755779` | passes |
| 17 | 12 | `0.097616998` | `0.225303227` | `0.249693501` | passes |
| 17 | 16 | `0.064213507` | `0.150196122` | `0.166455652` | passes |
| 19 | 8 | `0.177496277` | `0.404629526` | `0.451985397` | passes |
| 19 | 12 | `0.109990430` | `0.257253886` | `0.287361629` | fails |
| 19 | 16 | `0.074308095` | `0.176257045` | `0.196885311` | fails |

The strip height in this table is `2/5`.

At fixed rank 8, 12, or 16, the **lower** distance endpoint at each
larger cutoff exceeds the **upper** endpoint at the preceding cutoff.
The actual finite coefficient distance therefore increases from cutoff
13 to 17 to 19 in each of those ranks. The same disjoint ordering holds
for the origin-normalized distance `D_(C,N)`. At fixed cutoff, both
distances decrease strictly as rank increases from 8 to 12 to 16.
The sample path `(13,8), (17,12), (19,16)` decreases, but its three
points say nothing about the needed infinite diagonal.

The cutoff-19 cluster failure is a limitation of that sufficient
Rayleigh test, not a failure of direct alignment. At ranks 12 and 16
the trial Rayleigh values are about `3.60e-13` and `8.96e-18`, while
the fifth even eigenvalue lower bounds are only `4.55e-14` and
`1.05e-19`. Thus `mu < lambda_4` cannot be certified and is in fact
false at the displayed scales. The direct certified ground distances
still fall from rank 12 to 16. The exact-prolate Rayleigh-below-second
gate also fails in every tested space.

The cutoff-19 Jacobi certificate uses 100 modes with tail cut 1600.
At 80 modes, the Schur tail correction widened past the fourth-mode
separation; increasing the finite Jacobi section restored certified
isolation. This changes the certification resolution, not the prolate
or Weil definitions.

The [finite-Fourier diagonal](PROLATE_FOURIER_DIAGONAL_2026_09_23.md)
provides a sufficient candidate-projection path `N(C)=ceil(C^9)`.
To transfer its Xi limit to these Weil ground profiles on each closed
substrip `|Im z|<=sigma<1/2`, an all-support theorem would need

```
D_(C,N(C)) * sqrt(sinh(sigma log C)/(sigma log C)) -> 0,
D_(C,N)=||v_(C,N)/v_(C,N)[0]-w_(C,N)/w_(C,N)[0]||_2,
```

along with the finite simple-even and real-zero gates on the same
diagonal. The tested ranks are vastly smaller than `C^9`; neither
fixed-rank worsening nor finite rank improvement decides this limit.
No support-uniform ground-alignment or all-rank argument has been
proved, so RH remains open.
The later [coupled support-step identity](COUPLED_SUPPORT_SCHUR_RECURRENCE_2026_09_26.md)
separates the Fourier basis drift from the prime-defined ground-vector
response and identifies the rank-one derivative kick at each prime
power threshold.

Replay the cutoff-19 rank-16 direct certificate without a cluster file:

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/prolate_ground_alignment.py --exact-gate research/prime_spectral/exact_prolate_gate_19_16.json --spectrum research/prime_spectral/isolated_kernel_19_16.json --jacobi research/prime_spectral/prolate_jacobi_19_100.json --vectors research/prime_spectral/prolate_vectors_19_100.json --output research/prime_spectral/prolate_ground_alignment_19_16.json
uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/prime_spectral -p test_prolate_ground_alignment.py -v
```

All nine certificates are
[`prolate_ground_alignment_C_N.json`](prolate_ground_alignment_19_16.json)
with the corresponding cutoff and rank in the filename.
