# Two Fourier samples obstruct finite Rayleigh repair

The [exact prolate gate](PROLATE_CANDIDATE_GATE_2026_09_23.md) shows that
the unfiltered prolate candidate misses the necessary finite Weil
Rayleigh-below-second-even test at cutoff `C=13`. An inverse spectral
filter lowers its Rayleigh quotient but changes its Fourier profile.
Here is a stronger finite statement: **any** even vector that preserves
the exact projected prolate profile sufficiently closely at two real
frequencies still misses that gate.

Fix the orthonormal even Fourier basis with `d=N+1` coordinates and
`L=log C`. Write `sinc(t)=sin(t)/t` and define the real Fourier row

```
q_0(x)=sinc(x*L/2),
q_j(x)=(-1)^j/sqrt(2)*[
    sinc(pi*j-x*L/2)+sinc(pi*j+x*L/2)],  1<=j<=N.
```

For a vector `v` with `v_0!=0`, its origin-normalized profile is
`P_v(x)=q(x)·v/v_0`. Let `p_4,p_8` be the two values of the **exact**
normalized prolate projection at `x=4,8`. The
[analytic projection](prolate_projection_trial_13_4.json) encloses the
decimal-trial coefficients; the [exact eigenfunction transfer](exact_prolate_gate_13_4.json)
bounds the distance between that trial unit vector and the exact one.
If the distance is `e`, the trial central coordinate is at least `a>e`,
and `Q_x=||q(x)||_2`, the denominator identity gives

```
|P_exact(x)-P_trial(x)|
  <= Q_x*e/(a-e)*(1+1/a).                         (1)
```

This produces interval enclosures for both `p_4` and `p_8`, with
widths below `6e-49` before the profile-tolerance enlargement. The
Fourier row was independently checked against the existing finite
quotient-profile implementation.

For any target values `p_4,p_8`, set the two constraint rows
`r_x=q(x)-p_x*e_0`. A vector with those profile values satisfies
`r_4·v=r_8·v=0`. The minor of their columns `0,3` is enclosed away
from zero, so solving these two coordinates gives a basis matrix `B`
for the common nullspace. Let `A_even` be the certified Weil matrix
and let `beta` be the certified **upper** endpoint of its second even
eigenvalue. For a positive rational `gamma`, the 1024-bit Arb check
certifies every LDL pivot of

```
B^T * (A_even-(beta+gamma)*I) * B                 (2)
```

strictly positive, even when each target `p_x` ranges over its full
exact-prolate enclosure enlarged by the tolerance below. Thus every
nonzero `v` within that tolerance at **both** frequencies obeys
`Rayleigh_A(v)>beta+gamma`, and cannot satisfy the necessary
`Rayleigh_A(v)<lambda_1` gate.

| `C,N` | Allowed error at each profile sample | Certified Rayleigh excess `gamma` over second-even upper bound | Certificate |
|---:|---:|---:|---|
| `13,4` | `1e-9` | `4e-8` | [JSON](profile_constraint_13_4.json) |
| `13,8` | `1e-22` | `3e-17` | [JSON](profile_constraint_13_8.json) |

Two samples are essential to this particular obstruction. A single
homogeneous profile constraint has codimension one and must intersect
the span of the first two even Weil eigenvectors; its minimum Rayleigh
quotient cannot exceed the second eigenvalue by min-max. The second
constraint removes that automatic escape. The certified tolerances
are conservative interval-LDL bounds, not claimed optimal.

This result rules out a **profile-preserving finite repair** at the two
tested Fourier dimensions. It does not rule out a repair whose
distortion tends to zero along a different growing-support path, nor
does it prove an all-support gap, convergence to Xi, or RH.

Replay from the repository root:

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/profile_constraint_gate.py --certificate research/prime_spectral/certified_weil_13_4.json --candidate research/prime_spectral/prolate_candidate_13_4.json --jacobi research/prime_spectral/prolate_jacobi_13_80.json --vectors research/prime_spectral/prolate_vectors_13_80.json --excess 4e-8 --profile-tolerance 1e-9 --output research/prime_spectral/profile_constraint_13_4.json
uv run --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/profile_constraint_gate.py --certificate research/prime_spectral/certified_weil_13_8.json --candidate research/prime_spectral/prolate_candidate_13_8.json --jacobi research/prime_spectral/prolate_jacobi_13_80.json --vectors research/prime_spectral/prolate_vectors_13_80.json --excess 3e-17 --profile-tolerance 1e-22 --output research/prime_spectral/profile_constraint_13_8.json
```
