# Positive correction and cumulative gain at shift three

Using the [five-pole shift-three certificate](RH_UNIFORM_SHIFT_THREE_2026_09_23.md),
the actual Xi normalized rank correction satisfies

```
C_r(3)=delta_(r+1)(3)-2delta_r(3)+delta_(r-1)(3)
      > 1/[10(r+3)^2] > 0,
delta_r(3)=-log t_r(3), delta_0(3)=0,
```

for every integer `r>=1`. For every `r>=137`, the sharper bounds hold:

```
1/[2(r+3)^2] < C_r(3) < 3/[2(r+3)^2].
```

The rank slopes therefore increase strictly to a positive limit
`beta≈0.391901067229202`, and the exact infinite identity is
`sum_(r>=1) C_r(3)=beta-delta_1(3)≈0.339020868063442`.
These are analytic-numerical all-rank statements at **one fixed shift**;
they do not bound Xi corrections uniformly over all interior shifts.
In particular the certified negative `C_r(4)` values remain an obstacle.

## Uniform tail proof

Let `W_m`, `lambda_m` and `E_m(r)` for `m=2,3,4` be the certified
positive leading weights, rates and decreasing geometric error sums from
the five-pole proof. Since

```
t_r(3)=(r+3)/3 * D_r(2)D_r(4)/D_r(3)^2,
```

the leading model is `A(r+3)q^r`, where

```
A=W_2 W_4/(3 W_3^2)>0,
q=lambda_2 lambda_4/lambda_3^2=x_4/x_3 in (0,1),
beta=-log q.
```

For every `r>=82`, positivity and the determinant error estimates give

```
delta_r(3)=beta*r-log(r+3)-log A+epsilon_r,
|epsilon_r|<=K(r)
          =-log(1-E_2(r))-2log(1-E_3(r))-log(1-E_4(r)).
```

Every summand defining each `E_m` has positive coefficient and geometric
base below one. If `sigma` is their largest certified base, then for
all `j>=0`, `E_m(r+j)<=sigma^j E_m(r)`. The nonnegative power series of
`-log(1-x)` gives `K(r+j)<=sigma^j K(r)`. This preserves the common affine
model before bounding the second difference.

The affine terms cancel exactly and the explicit model second difference is

```
s_r=log[(r+3)^2/((r+2)(r+4))]
   =-log[1-1/(r+3)^2].
```

Thus `|C_r(3)-s_r|<=K(r-1)+2K(r)+K(r+1)` for `r>=83`.
At head `R=137`, the certified quantities satisfy

```
kappa=(R+3)^2*[K(R-1)+2K(R)+K(R+1)] < 0.443869,
sigma*((R+4)/(R+3))^2 < 0.865612 < 1.
```

The scaled error at each later rank decreases, so
`|C_r-s_r|<=kappa/(r+3)^2` for every `r>=R`.
The elementary bounds `x<=-log(1-x)<=x/(1-x)` for `0<x<1` imply
the stated tail interval. Its upper weighted bound is below `1.443920`.

## Finite bridge and sum

Certified dual determinants from the 201 Xi coefficient balls provide
`t_r(3)` through rank 137. Direct interval logarithms give
`(r+3)^2 C_r(3)>1/10` for every `r=1,...,136`.
The minimum lower enclosure is above `0.117966482003052` at rank one.
The tail lower constant exceeds `1/2`, so the two ranges meet with no gap.

The bound `K(r)->0` in the model shows that the slope
`delta_r(3)-delta_(r-1)(3)` tends to `beta`. Since `C_r` is the
difference of successive slopes, the finite telescope followed by this
limit proves the infinite-sum identity. The saved certificate also
encloses the first slope, limiting slope and their difference.

The proof uses the exact pole and determinant identities, geometric
series, interval arithmetic, and finite certified coefficients. It is
not Lean formalized. It supplies a second positive-correction boundary
column, while a simultaneous rank-and-shift budget remains open.

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/shift_three_correction.py --base research/certified_xi/pole_shift_three.json --coefficients research/certified_xi/coefficients_200.json --output research/certified_xi/shift_three_correction.json
uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/certified_xi -p test_shift_three_correction.py -v
```
