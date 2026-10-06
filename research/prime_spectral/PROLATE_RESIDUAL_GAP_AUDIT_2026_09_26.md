# Exact prolate candidate: finite residual and gap audit

The [conditional strip transfer](STRIP_RESIDUAL_TRANSFER_2026_09_23.md)
requires a unit candidate in the **same** even Fourier space as the certified
Weil matrix, with Rayleigh value below its second even eigenvalue. We checked
that requirement for the zero-integral prolate candidate from
[Connes–Consani–Moscovici, §7](https://arxiv.org/html/2511.22755v1).
The paper proves convergence of this candidate's Fourier transform on closed
substrips, but explicitly leaves the candidate-to-Weil-ground comparison open.

## Normalization and projection

Set `C=lambda^2`, `L=log C`, and `t=log u` on
`[-L/2,L/2]`. The prolate operator on `z=x/lambda` is
`-d/dz((1-z^2)d/dz)+(2*pi*C)^2*z^2`. For its normalized first and third
even modes `H_0,H_4`, the combination
`H=H_4-[H_4]_0/[H_0]_0 H_0` has zero integral; `[H]_0` is the coefficient
of the constant normalized Legendre polynomial. The candidate is
`K_C(t)=sqrt(exp(t))*sum_(n>=1) H(n*exp(t)/lambda)`, with `H` extended by
zero outside `[-1,1]`.

For `j>=0`, the certified Weil even basis is
`e_0(t)=L^-1/2` and
`e_j(t)=sqrt(2/L) cos(2*pi*j*(t+L/2)/L)` for `j>=1`.
Changing variables `z=n*exp(t)/lambda` gives the exact projection

```
w_j = b_j * sum_(n=1)^C n^(-1/2)
      * integral_(n/lambda)^lambda x^(-1/2) h_lambda(x)
          cos((2*pi*j/L)*log(lambda*x/n)) dx,
```

where `b_0=L^-1/2` and `b_j=sqrt(2/L)`. The `n=C` term is empty.
The implementation expands each Legendre polynomial exactly and integrates
each monomial by its closed antiderivative. The phase in the scaled
variable is `log(C*z/n)`; this agrees with the centered cosine basis.
The independent threshold-split quadrature tests cover both `C=2` and
multiple active summands at `C=13`. Arb balls enclose the decimal trial's
projected coefficients. An infinite-Jacobi residual certificate then
bounds the distance between that trial and the **exact** prolate
eigenfunctions, and the projection map bound transfers it to a unit
Fourier-vector error `eta`.

## Residual transfer and finite result

For a real symmetric finite even matrix `A`, let `w` be the certified unit
trial projection, `v` the exact unit prolate projection, and
`||v-w||<=eta`. If `M>=||A||`, then

```
|<Av,v>-<Aw,w>| <= 2*M*eta,
| ||(A-<Av,v>)v|| - ||(A-<Aw,w>)w|| | <= 4*M*eta.
```

The second line follows by subtracting the two residual vectors and using
`|<Av,v>|<=M`. We use an outward interval row-sum bound for `M`, the
certified infinite-Jacobi/projection error for `eta`, the interval Weil
matrix for the trial residual, and the isolated even spectrum for the gap.
The stored exact-prolate gate is replayed from its source inputs before any
result is accepted. A positive `lambda_1-mu` is the necessary gate for the
strip transfer; when its **upper** endpoint is negative, the candidate is
certifiably above the second even eigenvalue.

| `C,N` | Exact Rayleigh `mu`, approximate | Exact residual norm, approximate | Even gap `lambda_1-lambda_0`, approximate | `lambda_1-mu`, approximate | Gate |
|---:|---:|---:|---:|---:|---|
| `17,8` | `8.98638e-9` | `7.37157e-5` | `1.51841e-19` | `-8.98638e-9` | above second |
| `17,16` | `9.48430e-20` | `1.64563e-10` | `2.82677e-32` | `-9.48430e-20` | above second |
| `19,16` | `8.96063e-18` | `2.69680e-9` | `1.70727e-33` | `-8.96063e-18` | above second |

The table rounds for readability; the [17/8](prolate_residual_gap_17_8.json),
[17/16](prolate_residual_gap_17_16.json), and
[19/16](prolate_residual_gap_19_16.json) JSON files contain rational
outward endpoints and input/source hashes. The previously saved exact
Rayleigh certificates also exclude the canonical candidate at `C=13`
for ranks `4,8,12,16`, and at `C=17,19` for ranks `8,12,16`.
No finite instance here clears the residual-and-gap gate. These calculations
do not exclude another candidate or a growing cutoff/rank path.

Replay the new certificates and tests from the repository root:

```sh
uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/prime_spectral -p test_prolate_residual_gap_audit.py -v
```

The missing input to the strip theorem remains an all-support
candidate-to-Weil-ground estimate with **positive** clearance and an
origin-normalized Fourier-profile error tending to zero on closed
critical substrips. Finite residuals, however accurately enclosed, do not
provide that estimate or a proof of RH.
