# Coupled infinite Fourier tails and uniform high-mode coercivity

The [new generator](../../experiments/prime_spectral/weil_rank_tail_cell.py)
proves a bound on the **entire infinite forcing tail**, uniform over
`17<=C<=19`, for the exact retained-rank `K=8` unit Weil ground vector.
It combines the previously certified support eigenfamily and spatial
boundary with signed moment expansions. No upper limit on the omitted
Fourier indices is sampled or assumed.

The [certificate](weil_rank_tail_cell_17_19_8_degree64.json) gives

```
||(A u)_even,j>64||_l2 < 9.491e-12,
```

at every support in the cell. The separate displacement bound is below
`2.906086`. The reduction exceeds `3e11` in these upper bounds. The
order-8 geometric expansion remainder alone is below `1.219e-22`.
This is forcing of the **retained-rank** ground by the infinite operator;
it is not an enclosure of the infinite operator's ground eigenvector.

The same written proof supplies rank-independent off-diagonal operator
bounds and explicit high-mode coercivity. Throughout this support cell,
the even compression to Fourier indices `j>=18,612,929` is strictly
larger than the identity. The full compression to `|j|>=60,879,750`
is strictly larger than the identity. These conservative thresholds
come from analytic inequalities. No matrices of those sizes were built.
They control only the high-mode blocks, not the full spectrum or a
uniform all-rank profile budget. RH remains unproved.

## 1. Use the displacement identity before summing absolute values

The full matrix has indices in the integers and exact off-diagonal form

```
A_ij=(b_i-b_j)/(i-j),   b_i=i*A_(i,0),
b_0=0, b_-i=-b_i.
```

This follows by linearity from the
[established Weil correlation formulas](https://arxiv.org/html/2511.22755v1#S2.SS2)
and the [closed-entry derivation](CLOSED_WEIL_TAYLOR_CELL_2026_10_05.md).
Let `u=(u0,...,uK)` be any real even vector in the orthonormal even
basis. Its full coefficients are `c0=u0`, `c_(+/-i)=u_i/sqrt(2)`.
For an omitted positive index `n>K`, the even component of `A u` is
`sqrt(2)*(A c)_n`. Pairing `i` with `-i` gives exactly

```
R_n = sqrt(2)*b_n*S/n
      + (2*b_n/n)*sum_(i=1)^K u_i*i^2/(n^2-i^2)
      - 2*sum_(i=1)^K i*b_i*u_i/(n^2-i^2),
S=u0+sqrt(2)*sum_(i=1)^K u_i.
```

The boundary sum is formed before taking absolute values. Thus the
leading `1/n` coefficient contains the actual tiny boundary, rather
than the sum of the absolute coefficients. The remaining numerators
have common denominators and signed moments. This formula is valid
for any finitely supported even vector; being a ground vector is used
only to certify the moments in the present experiment.

## 2. Exact moment expansion with effective infinite remainder

For order `R>=0` define

```
m_r=sum_(i=1)^K u_i*i^(2r),           r>=1,
nu_r=sum_(i=1)^K u_i*b_i*i^(2r+1),   r>=0.
```

The finite geometric-series identity gives

```
R_n = sqrt(2)*b_n*S/n
      + 2*b_n*sum_(r=1)^R m_r/n^(2r+1)
      - 2*sum_(r=0)^(R-1) nu_r/n^(2r+2)
      + E_n.
```

Choose an integer tail cutoff `J>K` and a bound `|b_n|<=B_J` for all
`n>J`. Put

```
M=sum_(i=1)^K |u_i|*i^(2R+2),
V=sum_(i=1)^K |u_i*b_i|*i^(2R+1),
gamma_J=1/[1-(K/J)^2].
```

For all `n>J` the exact remainder satisfies

```
|E_n| <= 2*gamma_J * [B_J*M/n^(2R+3)+V/n^(2R+2)].
```

For clarity, its unbounded-index proof uses the exact remainders

```
i^2/(n^2-i^2)
 = sum_(r=1)^R i^(2r)/n^(2r)
   + i^(2R+2)/[n^(2R)*(n^2-i^2)],

1/(n^2-i^2)
 = sum_(r=0)^(R-1) i^(2r)/n^(2r+2)
   + i^(2R)/[n^(2R)*(n^2-i^2)].
```

Since `i<=K<J<n`, replacing `1/[1-(i/n)^2]` by `gamma_J` is valid
uniformly over the infinite tail.
For each integer `p>=1`, the integral test gives

```
H_p(J)=[sum_(n>J) n^(-2p)]^(1/2)
       <= J^(1/2-p)/sqrt(2p-1).
```

Minkowski's inequality then proves the effective all-index bound

```
||R_n>J||_l2
 <= sqrt(2)*B_J*|S|*H_1(J)
    + 2*B_J*sum_(r=1)^R |m_r|*H_(2r+1)(J)
    + 2*sum_(r=0)^(R-1) |nu_r|*H_(2r+2)(J)
    + 2*gamma_J*[B_J*M*H_(2R+3)(J)+V*H_(2R+2)(J)].
```

This theorem has arbitrary finite retained rank, arbitrary `J>K`, and
arbitrary finite expansion order. The constants and moments need to be
bounded on any desired family; the theorem does not assume an infinite
rank cutoff or suppress a remainder.

## 3. Bound the displacement sequence independently of Fourier rank

Set `L=log C`, `w_n=2pi*n/L`, `d_k=2k+1/2`, and `D=cosh(L/2)-1`.
The closed formula for `n*A_(n,0)`, for `n>=1`, is

```
b_n = 2D/pi * w_n/(1/4+w_n^2)
      + Im psi(1/4+i*pi*n/L)/(2pi)
      - sum_(k>=0) exp(-d_k L)*w_n/(d_k^2+w_n^2)/pi
      + sum_(p^a active) (log p)/sqrt(p^a)*sin(w_n*log(p^a))/pi.
```

The established [digamma series](https://dlmf.nist.gov/5.7.E6) gives,
for `x>0,y>0`,

```
Im psi(x+iy)=sum_(k>=0) y/[(k+x)^2+y^2].
```

Its summand decreases in `k`; its sum is at most its first term plus
its integral. At `x=1/4` this yields

```
0<Im psi(1/4+iy)<=pi/2+min(2,1/y).
```

Use `|w/(d^2+w^2)|<=1/(2d)` and also `<=1/|w|`. Let

```
Lmin=log17, Lmax=log19,
E=exp(-Lmin/2)/(1-exp(-2Lmin)),
P=sum_(p^a<=17) (log p)/sqrt(p^a),
Dmax=cosh(Lmax/2)-1.
```

The active branch includes 17 and excludes 19; its value agrees with
the physical form at both endpoints. Uniform bounds are

```
|b_n|<=B,
B=2Dmax/pi + [pi/2+min(2,Lmax/pi)]/(2pi)+E/pi+P/pi,

|b_n|<=B0+B1/n,
B0=1/4+P/pi,
B1=Lmax*[Dmax+(1+E)/2]/pi^2.
```

Oddness gives the same bound for negative indices. The certificate
has `B<3.157010`, and for `n>64` uses `B_64<2.115418`.
These estimates hold uniformly at every omitted Fourier index. Tests
at large indices are implementation checks, not the proof of uniformity.

## 4. A discrete Hilbert commutator controls the full off-diagonal matrix

On `l2(Z)`, let `H_ij=1/(i-j)` for `i!=j`, with zero diagonal.
The Fourier-series multiplier of this discrete Hilbert operator is
`-i*(pi-theta)` for `0<theta<2pi`; hence `||H||=pi` by Plancherel.
This can be established by the sine series of the sawtooth function,
first in L2 and then as the bounded multiplier operator.
Writing `D_b=diag(b_i)`, the exact identity is

```
A_off=D_b H-H D_b,
||A_off||<=2*pi*sup_i |b_i|.
```

It holds for all finite compressions with the same bound, independently
of dimension, and defines a bounded operator on the full Fourier
space. The certificate gives `||A_off||<19.836078` on the full cell.
The same argument applies separately to the archimedean contribution,
whose displacement sequence has bound

```
B_arch=[pi/2+min(2,Lmax/pi)]/(2pi)+E/pi.
```

This decomposition supplies an effective rank-independent bounded
perturbation, rather than summing an off-diagonal row absolutely.
Individual absolute rows have divergent harmonic tails; the Hilbert
operator estimate preserves their signed structure.

## 5. Effective logarithmic high-mode coercivity

The same digamma series implies

```
Re psi(1/4+iy)>=log y-1/y,     y>0.
```

A direct proof writes its real part as
`lim_M [log M-sum_(k=0)^(M-1) f(k)]`, with
`f(t)=(t+1/4)/[(t+1/4)^2+y^2]`. The difference between the sum and
integral has absolute value at most `integral |f'|<=1/y`.
The integral comparison limit is `log sqrt((1/4)^2+y^2)>=log y`.
The [trigamma series](https://dlmf.nist.gov/5.15.E1) also gives
`|psi'(1/4+iy)|<=1/y^2+pi/(2y)` by the same first-term-plus-integral
comparison. Combining these with the diagonal closed formula yields

```
(-Arch)_nn >= log(n/Lmax)-Lmax/(pi*n)-1/(4n)
             -Lmax*(1+E)/(2*pi^2*n^2),      |n|>=1.
```

The off-diagonal archimedean norm is at most `2pi B_arch` by Section 4.
The prime contribution is a finite sum of truncated translations and
their adjoints; its negative norm is at most `2P`.
The pole kernel on the centered physical interval is

```
2*cosh((s-t)/2)
 =2*cosh(s/2)*cosh(t/2)-2*sinh(s/2)*sinh(t/2).
```

Its negative eigenvalue is `L-2sinh(L/2)`. On the even subspace the
sinh term vanishes, so the pole contribution is nonnegative.
Therefore the high-mode even compression, to `|n|>=n0`, has lower bound

```
beta_even(n0)
 = log(n0/Lmax)-Lmax/(pi*n0)-1/(4n0)
   -Lmax*(1+E)/(2*pi^2*n0^2)-2pi*B_arch-2P.
```

For the full compression subtract
`2sinh(Lmax/2)-Lmax` additionally. Both lower bounds increase with
`n0` and tend to infinity. Outward interval arithmetic verifies

```
beta_even(18,612,929)>1,
beta_full(60,879,750)>1.
```

Thus these inequalities hold for every larger finite tail compression;
by closure they also hold for the corresponding infinite tail form.
They do not assert that the full Weil operator is positive. The
intermediate and low modes are excluded from these compressions.

## 6. Enclose the shared moments over the whole support cell

The degree-64 matrix and ground candidates are used only as enclosures;
no asymptotic eigenpair recurrence is assumed. In each of the 32
support subcells, write the physical candidate coefficients as `p_i(x)`.
Its norm is enclosed in an interval `[1,norm_upper]`, and its normalized
unit distance from the exact rank-8 ground is at most `d`.

For `m_r`, form the complete polynomial `sum i^(2r) p_i(x)` before
support-parameter evaluation, divide by the positive norm interval,
and add `d*sqrt(sum i^(4r))`.
For `nu_r`, multiply the physical candidate by the **common matrix
Taylor polynomial** for `b_i(L)=i*A_even,i0/sqrt(2)`, then form the
whole moment polynomial before parameter evaluation. Both the
coefficient radii and the analytic matrix remainder are retained.
The final moment error includes `d` times the weighted `b_i` norm and
the matrix remainder paired with the candidate. Thus cancellation
between neighboring Fourier components and their shared support
parameter occurs before outward bounds.

The already certified unit spatial boundary interval supplies `S`.
Absolute remainder moments use separate absolute bounds only after
the finite signed expansion has been removed. The geometric
remainder is not discarded even when small.

For example the independently evaluated original unit ground at `C=17`
has the readable values

| Moment | Approximate value |
|---|---:|
| `S` | `6.3425e-12` |
| `m_1` | `-6.2547e-8` |
| `nu_0` | `-5.3873e-10` |
| `m_2` | `1.1860e-4` |
| `nu_1` | `1.7116e-6` |

These point values illustrate the cancellation. The proof of the
infinite-tail bound uses the complete saved intervals over all 32
subcells, not these values.

## 7. The remaining inverse-response gate

There is an immediate, limited inverse-energy consequence. Let `Q`
project to the even modes `j>=18,612,929`, let `lambda_8` denote the
lowest even eigenvalue at retained rank eight, and put
`T_Q=Q A Q-lambda_8 I`. The saved even family bounds
`lambda_8<1.380e-24`, while `Q A Q>I`. Thus `T_Q>1-1.380e-24` and

```
< QAu, T_Q^(-1) QAu >
 <= ||QAu||^2/(1-lambda_8) <9.007e-23.
```

This follows conservatively from the `j>64` forcing bound; using the
power-law factors at the larger cutoff can sharpen it. The inequality
holds for this direct high-tail response of the retained-rank vector.
It is not the profile response after eliminating the intermediate
modes `9,...,18,612,928`. Those modes can amplify the forcing through
a near-singular constrained inverse. The existing
[rank-energy/dual-resolvent audit](COUPLED_RANK_SCHUR_RECURRENCE_2026_09_24.md)
already proves that tiny energy alone need not imply a tiny profile
increment.

An all-rank argument now has two explicit ingredients: a moment-controlled
infinite forcing tail, and a uniform coercive outer block. It still
needs a controlled elimination of the intermediate block and a coupled
Fourier-profile inverse bound, with support-dependent origin normalization
included. None of those missing estimates follows from the present
certificate. Uniformity for growing support, a summable combined
support/rank path, and arithmetic identification with Xi also remain
open. The unbounded theta-reference sign and interior all-rank theta
budget are unchanged by this independent prime-defined program.

## Replay and verification scope

The [tests](../../experiments/prime_spectral/test_weil_rank_tail_cell.py)
replay the entire support-cell certificate, independently enclose its
signed moments with original integral eigenvectors at both prime
endpoints, and compare the omitted-mode formula with a new original
integral mode. Exact rational tests check the finite geometric
expansion including its remainder for arbitrary even vectors and odd
displacement sequences. Digamma/trigamma bounds, integral-test bounds,
coercivity monotonicity and closed entries at large Fourier indices
are checked independently. Invalid tail parameters fail closed.
The written proof, not the large-index samples, establishes the infinite
index range. These new arguments are not Lean formalized.

Validation: all 147 prime-spectral tests passed in 221.646 seconds.
Certificate source and input hashes match the current files; Python
compilation, new-file whitespace checks and `git diff --check` passed.

```sh
uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/prime_spectral -p test_weil_rank_tail_cell.py -v
```
