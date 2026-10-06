# The exact prolate candidate is a low-cluster vector, not a certified ground vector

The [finite prolate replay](PROLATE_CANDIDATE_REPLAY_2026_09_24.md)
shows that the exact zero-integral prolate candidate fails the
Rayleigh-below-second gate at cutoff 13 for Fourier ranks 4, 8,
12, and 16. That gate identifies a **single** ground eigenvector.
The earlier [Connes–Consani construction](https://arxiv.org/html/2106.01715)
also treats several prolate vectors as an approximate low-energy
family. We therefore checked whether the same exact candidate is
nevertheless concentrated in a small bottom eigenspace of the
prime-defined Weil matrix.

Let `A` be a positive finite even Weil matrix with ordered
eigenvalues `0<lambda_0<...<lambda_N`, and let `w` be the unit
exact projected prolate candidate. If `mu=<Aw,w><lambda_k` and
`Q_>=k` is the spectral projection onto eigenvectors numbered
`k,...,N`, then spectral decomposition gives

```
mu >= lambda_0*(1-||Q_>=k w||^2)
      +lambda_k*||Q_>=k w||^2,
||Q_>=k w||^2 <= (mu-lambda_0)/(lambda_k-lambda_0)
                  <= mu/lambda_k.                         (1)
```

The second inequality uses `0<lambda_0<mu<lambda_k`. Formula (1)
is a rigorous **subspace** distance bound that requires no estimate
of the tiny gap between the first two eigenvalues.

The [certified generator](../../experiments/prime_spectral/prolate_cluster_gate.py)
replays each saved exact-prolate transfer and Weil spectrum. At ranks
4 and 8 it isolates the full even spectrum from the stored interval
Weil matrix; at ranks 12 and 16 it replays the existing Rump-isolated
spectrum. It propagates the exact prolate eigenfunction/projection
error into an upper Rayleigh bound before using (1) with `k=4`.

| Cutoff 13 modes | Exact prolate Rayleigh upper, approx. | Fifth even eigenvalue lower, approx. | Squared mass outside first four, certified upper |
|---:|---:|---:|---:|
| 4 | `4.33263e-5` | `0.4825088` | `<8.980e-5` |
| 8 | `8.19961e-10` | `3.04730e-6` | `<2.691e-4` |
| 12 | `3.55211e-15` | `2.04261e-11` | `<1.740e-4` |
| 16 | `2.44796e-20` | `1.01482e-15` | `<2.413e-5` |

Thus **more than 99.97% of the exact candidate's squared coefficient
norm lies in the first four even Weil modes** in every tested finite
space. The precise rational bounds and input/source hashes are in
[mode 4](prolate_cluster_13_4.json),
[mode 8](prolate_cluster_13_8.json),
[mode 12](prolate_cluster_13_12.json), and
[mode 16](prolate_cluster_13_16.json).

This reconciles two finite observations: the prolate candidate can be
an excellent **low-cluster** vector while remaining far above the
second eigenvalue, because several Weil eigenvalues are extremely
small. It does not identify which vector in that cluster should have
the real-zero quotient property. An arbitrary cluster projection
does not inherit the certified ground-vector real-zero theorem.
To obtain RH by this route one would need an increasing-support
cluster estimate, a canonical real-zero-preserving choice in the
cluster, and a locally uniform Xi limit for that choice. None is
proved by (1) or by these four finite certificates.
The [direct ground-alignment certificates](PROLATE_GROUND_ALIGNMENT_2026_09_24.md)
measure the remaining orientation within the cluster at the same
finite support, without using the failed Rayleigh-below-second gate.

Replay with:

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/prolate_cluster_gate.py --exact-gate research/prime_spectral/exact_prolate_gate_13_16.json --spectrum research/prime_spectral/isolated_kernel_13_16.json --jacobi research/prime_spectral/prolate_jacobi_13_80.json --vectors research/prime_spectral/prolate_vectors_13_80.json --output research/prime_spectral/prolate_cluster_13_16.json
uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/prime_spectral -p test_prolate_cluster_gate.py -v
```
