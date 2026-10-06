# Positive correction and a cumulative budget at shift two

## Statement and scope

For the actual Xi coefficient array, use the normalization of the
[three-pole theorem](RH_UNIFORM_SHIFT_TWO_2026_09_19.md):

    t_r(2)=(r+2) D_r(1)D_r(3)/(2 D_r(2)^2),
    delta_r(2)=-log t_r(2), delta_0(2)=0,
    v_r(2)=delta_r(2)-delta_(r-1)(2),
    C_r(2)=delta_(r+1)(2)-2delta_r(2)+delta_(r-1)(2).

Then, for every integer r>=1,

    C_r(2)>11/[100(r+2)^2]>0.                         (1)

For every integer r>=90 the sharper bounds are

    1/[2(r+2)^2]<C_r(2)<3/[2(r+2)^2].                (2)

Thus v_r(2) increases strictly to the fixed limiting slope beta from
the [exponential boundary theorem](RH_SHIFT_TWO_EXPONENTIAL_TUBE_2026_09_20.md).
There is an exact convergent cumulative identity

    sum_(r=1)^infinity C_r(2)=beta-delta_1(2),         (3)

whose certified value is approximately 0.286623351129241. All its
nonempty finite partial sums are positive and strictly increasing.
For r>=90, the remaining gain satisfies

    1/[2(r+2)]<beta-v_r(2)<3/[2(r+1)].               (4)

This is an analytic-numerical proof at one fixed shift, using the existing
coefficient and pole certificates. It is not Lean formalized. It does not
prove the uniform interior budget, positivity at every shift, or RH.

## 1. Cancel the common affine model before bounding the error

The exponential boundary theorem proves, with fixed actual A>0, 0<q<1,
and beta=-log q,

    delta_r(2)=beta*r-log(r+2)-log A+epsilon_r,
    |epsilon_r|<=K(r), r>=45.                        (5)

Here the explicit function K is obtained from the three relative
determinant-error envelopes E_m(r)=sum_l c_(m,l) q_(m,l)^r:

    K(r)=-log(1-E_1(r))-2log(1-E_2(r))-log(1-E_3(r)).

All c are nonnegative and all geometric rates are strictly between zero
and one. With sigma the largest saved rational rate bound,

    K(r+j)<=sigma^j K(r), r>=45, j>=0.               (6)

Indeed E_m(r+j)<=sigma^j E_m(r), and the positive power series for
-log(1-x) gives -log(1-s*x)<=s[-log(1-x)] for 0<=s<=1.

Taking the second difference of (5), the same beta*r and log A cancel
exactly. Bounding their values independently would lose this cancellation.
Writing s_r=-log(1-1/(r+2)^2), we obtain

    |C_r(2)-s_r|<=K(r-1)+2K(r)+K(r+1), r>=46.       (7)

No differentiability of a rank interpolation is assumed in (7).

## 2. A single tail comparison covers every later rank

Set R=90 and let E be the saved outward rational upper bound for
K(R-1)+2K(R)+K(R+1). Put kappa=E*(R+2)^2. The ball computations certify

    kappa<0.472069179,
    sigma*((R+3)/(R+2))^2<0.799019581<1,
    (R+2)^2/((R+2)^2-1)+kappa<1.472187341.           (8)

By (6)-(7), |C_(R+j)-s_(R+j)|<=E*sigma^j. The successive ratio of
E*sigma^j*(R+j+2)^2 is at most the middle quantity in (8), so

    |C_r-s_r|<=kappa/(r+2)^2, every r>=R.             (9)

For 0<x<1, integrating 1/(1-t) between 0 and x gives
x<=-log(1-x)<=x/(1-x). Consequently

    1/(r+2)^2<=s_r<=1/((r+2)^2-1).

Combining with (9), the weighted lower bound is 1-kappa>1/2.
The weighted upper bound is at most the last expression in (8), since
x^2/(x^2-1) decreases for x>1. This proves (2) uniformly.
The continuation is an analytic inequality, not an extrapolation from
the finitely many tested ranks.

## 3. Certified finite bridge

Fresh dual determinants from coefficients_120.json compute all ratios
t_r(2) needed through rank 90. With t_0(2)=1, evaluate

    C_r(2)=2log t_r(2)-log t_(r-1)(2)-log t_(r+1)(2)

using FLINT balls at 2048-bit precision, for every r=1,...,89. Each
enclosure satisfies (r+2)^2 C_r(2)>11/100. The smallest weighted
enclosure occurs at r=1, near 0.11002074652665131. The finite bridge
and tail meet without a gap. Since the tail lower constant 1/2 is
larger than 11/100, this proves (1).

The generator rejects an unresolved inequality; it does not classify
an enclosure overlapping the threshold as positive. The JSON records
the bridge, exact rational bounds, and input/base/source hashes.

## 4. Cumulative gain and the boundary interpretation

The definition gives C_r=v_(r+1)-v_r exactly. Equation (5) and
K(r)->0 imply v_r->beta. Summing the telescoping identity and taking
the limit proves (3). In particular, this is a cumulative theorem,
not a sum truncated at the available coefficients. For r>=90, (2) gives

    (1/2) sum_(k=r)^infinity (k+2)^(-2)
      < beta-v_r
      < (3/2) sum_(k=r)^infinity (k+2)^(-2).

For the positive decreasing function x^(-2), integration gives

    1/(r+2) < sum_(k=r)^infinity (k+2)^(-2) < 1/(r+1).

This proves (4).

The same C_r equals 2log B_r(2)-log B_r(1)-log B_r(3), where

    B_r(m)=(r+m) D_(r+1)(m)D_(r-1)(m)/(r D_r(m)^2).

This follows by substitution of t_r and cancellation of the determinant
logs and normalization factors. Positivity of these B factors uses only
the already proved positive determinants at shifts 1, 2, and 3. It does
not assume t_r(3)>0 or D_r(4)>0. Those would go beyond this certificate.

Positive correction at shift two provides stronger exterior boundary
information for a future comparison over m>=3. It does not justify
discarding negative interior corrections: the existing finite experiment
certifies C_r(4)<0 for ranks 34 through 46. A successful uniform interior
argument must control their cumulative effect and neighboring compensation.

## Reproduction and validation

From the repository root:

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/shift_two_correction.py --base research/certified_xi/pole_shift_two.json --coefficients research/certified_xi/coefficients_120.json --output research/certified_xi/shift_two_correction.json
uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/certified_xi -p 'test_shift_two_correction.py' -v
```

Regression checks independently compare the neighboring-B formula with
the ratio formula, check finite telescoping, compare later direct
determinants with (2) and (4), and reject an unresolved earlier tail head.
The tests complement the uniform argument above; they do not replace it.
