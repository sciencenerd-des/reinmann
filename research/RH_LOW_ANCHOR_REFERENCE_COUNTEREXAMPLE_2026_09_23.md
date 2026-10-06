# The frozen degree-16 reference changes curvature sign at low anchors

The [uniform shifted-Gaussian theorem](RH_SHIFTED_GAUSSIAN_CURVATURE_2026_09_20.md)
proves negative reference and true-theta log-deficit curvature for every
anchor `a >= 10^6`. Its hypothesis is substantive: the same frozen
degree-16 reference, extended by its defining finite integral to `a=1`,
has **positive** log-deficit curvature. Consequently an assertion of
negative curvature for this unchanged reference at *every* anchor is false.
The true theta integral has negative curvature at `a=1`; the sign failure
belongs to the low-anchor approximation, not to Xi.

## Exact quantity checked

At fixed anchor `a`, use the original `u`, `A`, `L`, degree-16 polynomial
`P_a` and amplitude `b` from the common-remainder construction. Its reference is

```
Q_a(y) = [4 pi^2 exp(p_a(log u))/sqrt(A)]
         * integral_(-L)^L exp(P_a(s)) b(log u+s/sqrt(A))
                             exp(2(y-a)(log u+s/sqrt(A))) ds.
```

Define `q_a(y)` and `F_a(y)` exactly as in the uniform theorem:

```
q_a(y) = y(2y-1)/[(y+1)(2y+1)]
         * Q_a(y-1) Q_a(y+1) / Q_a(y)^2,
F_a(y) = log[(y+1)(1-q_a(y))].
```

The prefactor in `Q_a` and the affine tilt `exp(2(y-a)log u)` cancel in
the ratio and its centered derivatives. The new evaluator integrates the
remaining finite expression and its first two tilt derivatives at offsets
`-1,0,+1` with Arb balls. Writing `ell=log q`, it evaluates the exact identity

```
F_a''(a) = -1/(a+1)^2 - q ell''/(1-q) - q (ell')^2/(1-q)^2.
```

The output stores exact rational lower and upper endpoints, rather than the
rounded values below:

| Anchor | `q_a(a)` | Certified sign of `F_a''(a)` | Approximate curvature |
|---:|---:|---|---:|
| 1 | 0.4119977799 | positive | 0.88353050395877 |
| 6 | 0.8245085214 | positive | 0.000943664287324 |
| 8 | 0.8599963113 | negative | -0.000369923802217 |

Each row has `0<q<1`, so the real logarithm is defined there. In contrast,
the independent direct theta-moment routine certifies
`(log epsilon_true)''(1) < -0.0217726504067`. Thus replacing the true
low-anchor integral by this saddle reference reverses the sign at `a=1`.

This is a point counterexample to an **all-anchor extension of the reference
claim**, not a negative statement about the existing tail theorem. A proof
of true-theta curvature below `10^6` needs a separate compact-domain
certificate or a different low-anchor reference. Even a complete
true-theta curvature theorem would be rank two only: the interior cumulative
budget is an independent higher-rank obligation.

## Replay and validation boundary

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/reference_low_anchor.py --output research/certified_xi/reference_low_anchor.json
uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/certified_xi -p test_reference_low_anchor.py -v
```

The regression test independently compares the new finite-integral formula
with the existing high-anchor `anchored_moments` evaluator at `a=10^6`.
It also checks that the true theta curvature and frozen-reference curvature
have opposite certified signs at `a=1`. The argument relies on the written
identities and Arb quadrature, and is not Lean formalized.
