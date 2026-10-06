# Shift three at every rank from five certified reciprocal poles

## Result and scope

With the same Xi coefficient normalization and analytic-numerical trust
boundary as the [shift-two proof](RH_UNIFORM_SHIFT_TWO_2026_09_19.md),
the five-pole certificate proves for every integer `r>=1`:

```
D_r(3)>0,
0<t_r(3)=(r+3)/3 * D_r(2)D_r(4)/D_r(3)^2 <1.
```

The contour-and-determinant tail starts at rank 82; certified coefficients
cover ranks 1..81, including the two neighboring determinants in the ratio.
This establishes one more fixed interior shift, **not** a simultaneous
all-shift or all-rank budget. It is not a proof of RH. The analytic argument
below is written analysis with FLINT/Arb certificates, not Lean formalized.

## 1. Five poles in a bounded disk

Let `E(z)=sum (mu_n/mu_0) z^n`, `F(z)=E(-z)`, and `H=1/F=sum h_n z^n`.
The new coefficient certificate encloses `mu_0,...,mu_200` using the
special-function series and independently checks the theta integral at
indices 0..8. For its degree-200 polynomial `P`, use `R=1150`, `S=2300`.
Since the coefficients of `E` are positive,

```
|F-P| <= tau=E(S)*2^(-201),
|F'-P'| <= 201*tau/R                  on |z|<=R.
```

For the derivative, `n 2^(-n)` decreases for `n>=201`. The upper
bound on `tau` is below `3.458e-47`. A 512-arc translated-Taylor contour
certificate bounds `|P|` below by `4.330e-9` on the circle and gives
winding number five. Rouché transfers the zero count to `F`.

Five disjoint real sign-changing brackets, initially `(199,201)`,
`(441,443)`, `(624,627)`, `(924,927)`, `(1083,1087)`, account for all
five zeros. They are distinct and therefore simple. Their reciprocal
pole amplitudes `A_j=-1/(rho_j F'(rho_j))` have certified alternating
signs `+,-,+,-,+`. Write `x_j=1/rho_j`, so
`x_1>...>x_5>1/R`. After subtracting these five poles, Cauchy's estimate
gives, at **every** coefficient index,

```
h_n=sum_(j=1)^5 A_j*x_j^n + e_n,
|e_n|<=M*R^(-n),
M=1/(min_circle|P|-tau)+sum_j |A_j|/(R/rho_j-1).
```

The certified upper bound on `M` is below `3.593e8`. This coefficient
estimate does not assume any information about zeros outside the circle.

## 2. Determinant expansion that retains pole cancellation

The dual Jacobi-Trudi identity gives

```
D_r(m)=det[h_(r+i-j)]_(0<=i,j<m),  m=1,2,3,4.
```

For `|T|=m`, put

```
W(T)=(-1)^(m(m-1)/2)*product_(j in T) A_j
     *product_(i<j in T)(x_i-x_j)^2/(x_i*x_j).
```

The pure-pole determinant equals
`sum_(|T|=m) W(T)*(product_(j in T)x_j)^r`. The leading subset
`T={1,...,m}` has strictly positive weight `W_m`; its rate is
`lambda_m=product_(j=1)^m x_j`. Every other subset has smaller rate.

For residual columns, expand the determinant by columns before taking
absolute values. A repeated pole label gives proportional columns and
vanishes exactly. For every remaining injective assignment, expand by
row permutations and use `|e_(r+i-j)|<=M R^(-r-i+j)`.
The resulting finite sums give certified bounds

```
|D_r(m)/(W_m*lambda_m^r)-1| <= E_m(r)
E_m(r)=sum_l c_(m,l)*q_(m,l)^r,
c_(m,l)>=0, 0<q_(m,l)<1,  r>=m-1.
```

The implementation records every `c` and `q` with outward rational
enclosures. The strict `q<1` checks make each `E_m(r)` decreasing for
all larger ranks, without extrapolating from samples. Tests compare the
five-pole Vandermonde formula and size-four residual envelope against
direct determinants of perturbed synthetic sequences.

At rank 82, the upper bounds for `E_1,...,E_4` are respectively below
`2.803e-27`, `1.088e-11`, `4.396e-12`, and `0.852075`.
Thus all four determinants are strictly positive for every `r>=82`.

## 3. The normalized ratio stays below one

The exact rank-shift normalization yields

```
t_r(3)=(r+3)/3 * D_r(2)D_r(4)/D_r(3)^2.
```

The leading exponential rates simplify because
`lambda_2*lambda_4/lambda_3^2=x_4/x_3`. Hence, for `r>=82`,

```
t_r(3) <= (r+3)/3 * (W_2 W_4/W_3^2)*(x_4/x_3)^r
          *(1+E_2(r))*(1+E_4(r))/(1-E_3(r))^2.
```

The right side at rank 82 is below `3.586e-11`. Its error factor
decreases with rank. The remaining `(r+3)(x_4/x_3)^r` factor also
decreases: its successive ratio at rank 82 is below `0.683722` and
decreases thereafter. Consequently `0<t_r(3)<1` throughout the tail.

For ranks 1..81, `dual_grid` computes certified dual determinants
`D_r(m)>0` at `m=1,2,3,4` and verifies `0<t_r(3)<1` directly.
The dual/direct identity is cross-checked on overlapping small blocks.
The finite bridge meets the tail at rank 82 with no gap.

## Completion boundary and replay

This fixes `m=3` while `m` is held constant. Certifying another finite
number of shifts would still leave infinitely many interior shifts.
The all-shift cumulative rank budget needs an argument whose control is
uniform in **both** `r` and `m`; this certificate does not provide one.
It also does not extend the low-anchor degree-16 reference sign, which
has an [explicit counterexample](RH_LOW_ANCHOR_REFERENCE_COUNTEREXAMPLE_2026_09_23.md).

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/coefficients.py --max-n 200 --bits 4096 --accuracy 128 --theta-max-n 8 --output research/certified_xi/coefficients_200.json
uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/pole_shift_three.py --coefficients research/certified_xi/coefficients_200.json --output research/certified_xi/pole_shift_three.json
uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/certified_xi -q
```

The saved artifacts contain exact rational enclosures, the complete
512-arc contour record, five pole brackets and derivative bounds,
all residual error terms, and the 81-rank bridge. Their input and source
hashes bind the result to the code and coefficient certificate.
