# A coupled response determinant for nested Weil ranks

The [eigenvalue-response identity](EIGENVALUE_RESPONSE_BRIDGE_2026_09_24.md)
writes each finite ground Fourier profile as a ratio of two
least-eigenvalue derivatives. Subtracting the two ratios **after**
bounding their derivatives separately can obscure cancellation,
especially at imaginary frequencies. The determinant below retains
that cancellation and states a scalar all-rank target.

Fix one support cutoff and nested even Fourier ranks `N<M`. For each
rank let `Lambda_R(q;t,s)` and its derivatives be as in the response
bridge. Since the Fourier functional at rank `N` is the restriction
of the rank-`M` functional, the perturbed rank-`N` matrix is the
leading block of the perturbed rank-`M` matrix. The min-max principle
therefore gives

```
Delta_(N,M)(q;t,s)
  := Lambda_N(q;t,s)-Lambda_M(q;t,s) >= 0              (1)
```

for every real `t,s`. Write `d_(R,q)=partial_t Lambda_R(q;0,0)`
and `d_(R,e)=partial_s Lambda_R(q;0,0)>0`. The origin response does
not depend on `q`. The exact profile increment is

```
P_M(z)-P_N(z)
 = [d_(M,z)*d_(N,e)-d_(N,z)*d_(M,e)]
   /[2*d_(M,e)*d_(N,e)]
 = [d_(N,z)*partial_s Delta_(N,M)
    -d_(N,e)*partial_t Delta_(N,M)]
   /[2*d_(M,e)*d_(N,e)].                              (2)
```

For complex `z`, apply the identity to the real and imaginary parts
of its Fourier functional. This is an algebraic consequence of the
simple-eigenvalue perturbation formula. The second form in (2)
shows that the relevant rank defect is a **coupled derivative**:
its Fourier change must be compared with its origin change at the
same rank. Bounds on either derivative alone can be much too large.

The [finite response-determinant certificates](rank_response_13_4_8.json)
and [rank 8 to 12 certificate](rank_response_13_8_12.json) use exact
rational arithmetic on the independently certified secant intervals.
They overlap the separately certified signed Schur-spectral rank
increments. The ratio below is a certified lower bound on the sum of
the absolute values of the two numerator products divided by the
absolute value of their coupled difference:

| Support 13 rank step | `z=4` | `z=8` | `z=i` |
|---|---:|---:|---:|
| 4 to 8 | `>8.52` | `>1.97` | `>142.71` |
| 8 to 12 | `>27.16` | `>6.49` | `>442.04` |

Thus the determinant coupling is material, not merely aesthetic.
For example, the certified `z=i` profile increment at rank 8 to 12
is about `-0.00465643`, while the two products whose difference
produces it are over 442 times larger in total.

## A gap-free finite-difference bound, and its real bottleneck

For one real perturbation direction `q`, write
`g_R(t)=Lambda_R(q;t,0)` and
`Delta(t)=g_N(t)-g_M(t)>=0`. Define the nonnegative symmetric
secant curvature

```
omega_M(h)=[2*g_M(0)-g_M(h)-g_M(-h)]/h, h>0.
```

Concavity brackets each derivative by its positive and negative
secants. Subtracting these brackets and using `g_N=g_M+Delta`
gives the exact inequality

```
[Delta(h)-Delta(0)]/h - omega_M(h)
  <= d_(N,q)-d_(M,q)
  <= [Delta(0)-Delta(-h)]/h + omega_M(h).            (3)
```

The same formula holds for the origin direction `q=e/2`.
Consequently a uniform rank budget from (2) would require control
of the **response of the rank defect** at both directions and of
their coupled determinant, plus a curvature modulus small enough
at the chosen perturbation scale. Positivity `Delta>=0` alone does
not bound its derivative: a narrow nonnegative feature can have a large
slope.

This is where the missing spectral control reappears. At support
13 the certified second-even gaps at ranks 4, 8, and 12 are
approximately `8.65e-10`, `9.62e-18`, and `4.68e-24`. For the
origin perturbation, a fixed secant step `h=10^-17` gives derivative
bracket widths approximately `2.1e-9`, `0.123`, and `0.614` at those
three ranks. Shrinking the step to `10^-25` at rank 8 and `10^-30`
at rank 12 makes the finite brackets sharp, but does not produce a
rank-independent differentiability modulus. This is why the
gap-free identity by itself does not solve the all-rank problem.

For a rank path `N_0<N_1<...`, an actual all-rank profile theorem
would follow if, on every compact `K` in `|Im z|<1/2`, the sum of
the absolute coupled terms in (2) from rank `N_a` onward tends to
zero uniformly in `z in K`, with positive origin responses along
the path. One would still need the independent increasing-support
identification with `Xi(z)/Xi(0)` and the finite real-zero gates.
The current certificates check two finite increments only. They do
not prove such a cumulative estimate, support uniformity, or RH.

Replay with:

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/rank_response_determinant.py --first-response research/prime_spectral/eigenvalue_response_13_8.json --second-response research/prime_spectral/eigenvalue_response_13_12.json --first-weil research/prime_spectral/certified_weil_13_8.json --second-weil research/prime_spectral/certified_weil_13_12.json --output research/prime_spectral/rank_response_13_8_12.json
uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/prime_spectral -p test_rank_response_determinant.py -v
```
