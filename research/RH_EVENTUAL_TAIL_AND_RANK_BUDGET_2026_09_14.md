# Eventual discrete tail and a cumulative rank budget

This pass derives a non-effective eventual discrete scaled-deficit estimate
from a published asymptotic expansion, and formalizes an abstract cumulative
rank-budget deduction. The continuous theta derivative estimate, an explicit
threshold, and a uniform Xi-specific rank budget remain open. The asymptotic
argument below is a mathematical derivation, not a Lean-checked theorem or a
claim of a new result in the literature.

## 1. Published input and normalization

Use gamma(n)=n! mu_n and w=W(2n/pi). Theorem 1.4 of
[O'Sullivan, Zeros of Jensen polynomials and asymptotics for the Riemann xi function](https://arxiv.org/html/2007.13582)
gives arbitrarily long expansions with rational coefficient functions c_j(w).
For the present deduction use five orders, with relative remainder
O(log^5(n)/n^5). The rational coefficient functions have size O(log^j(n)).
In the notation below the logarithm of the leading expression is F+P,
up to an irrelevant constant. The source is used for that expansion only;
it does not assert our continuous scaled-deficit curvature bound or an
all-rank result. Its normalization is the same gamma as the repository.

Define smooth functions for sufficiently large real x:

```
w(x) = W(2x/pi)
F(x) = x [1 + 2 log w - log(16x) - 2/w]
P(x) = 7w/4 + (1/2) log(w/(1+w))
T(x) = log(1 + sum_(j=1)^4 c_j(w)/x^j)
S(x) = constant + F(x) + P(x) + T(x).
```

The logarithm in T is defined eventually since its argument tends to one.
The published expansion implies, at integer n,

```
log gamma(n) = S(n) + R_n,    R_n=O(log^5(n)/n^5).
```

We do not differentiate R_n, or pretend an integer expansion alone supplies
bounds on a continuously interpolated remainder.

## 2. A qualitative eventual discrete inequality

Let Delta2 f(x)=f(x-1)-2f(x)+f(x+1). Since
q_n=n/(n+1) * gamma(n-1)gamma(n+1)/gamma(n)^2,

```
log q_n = log(n/(n+1)) + Delta2 S(n) + O(log^5(n)/n^5).
```

The last estimate uses only a sum of three bounded remainders. Define the
smooth model z(x)=log(x/(x+1))+Delta2 S(x). We can differentiate this model:
all of its terms are explicit rational/Lambert/logarithmic functions.
The identities

```
w' = w/[x(1+w)]
F' = log(w^2/(16x))
F'' = (1-w)/[x(1+w)]
```

give, for some fixed finite power M,

```
z(x) = -a(x)/x + E(x),   a(x)=2w/(1+w),
E^(j)(x)=O(log^M(x)/x^(2+j)),  j=0,1,2.
```

Here is justification of the derivative remainder bookkeeping. Every rational
c_j(w) has at most polynomial growth at infinity, and so do its finitely many
w-derivatives. Repeated application of w'=w/[x(1+w)] shows that each further
x-derivative of P or T gains a factor 1/x, up to a fixed logarithmic power.
Also F^(k)=O(x^(1-k)) for k>=2. The identity
Delta2 F(x)=integral_(-1)^1 (1-|s|) F''(x+s) ds and symmetry of its kernel
bound Delta2 F-F'' and its first two derivatives by the corresponding fourth
through sixth derivatives. The P and T terms and the expansion of
-log(1+1/x) give the displayed E estimates. All claims here concern S, not R.

For large x, z<0. Put

```
f_*(x) = log((x+1)(1-exp(z(x))))
f_0(x) = log(2w/(1+w)).
```

Factoring -z=a/x times 1+O(log^M(x)/x), and using
(1-exp z)/(-z)=1+O(z), gives

```
(f_* - f_0)^(j)(x)=O(log^M(x)/x^(1+j)),  j=0,1,2.
```

This assertion includes derivative bounds because it is an expansion of the
explicit smooth model using smooth elementary functions near nonzero limits.
Direct differentiation yields

```
f_0'  = 1/[x(1+w)^2]
f_0'' = -Q(x)
Q(x)  = (w^2+4w+1)/[x^2(1+w)^4] > 0.
```

In particular Q(x) is asymptotic to 1/(x^2 log^2 x). Integrating the second
derivative against the same tent kernel, and using Q(x+s)/Q(x) -> 1 uniformly
for |s|<=1, proves

```
-Delta2 f_*(n) = Q(n)(1+o(1)).
```

It remains to transfer this to the true sequence. Since log q_n=z(n)+Rtilde_n
with Rtilde_n=O(log^5(n)/n^5), exponentiating changes q by that order. Forming
epsilon_n=(n+1)(1-q_n) loses one power of n, giving

```
epsilon_n = (n+1)(1-exp z(n)) + O(log^5(n)/n^4).
```

The model tends to 2, so epsilon_n is eventually positive and taking logs is
stable. Thus log epsilon_n=f_*(n)+O(log^5(n)/n^4). Its second finite difference
has an error of the same order without differentiating the remainder. Finally
log^5(n)/n^4=o(Q(n)), so

```
2 log epsilon_n - log epsilon_(n-1) - log epsilon_(n+1)
    = Q(n)(1+o(1)) > 0 eventually.
```

This establishes eventual strict discrete log-concavity as a consequence of
the cited arbitrary-order expansion and the argument above. It provides no
explicit N. The existing certified checks through center 118 therefore do not
close the interval between that finite range and the unknown eventual regime.
Nor can second finite differences control (log epsilon(x))'' at every real x:
an effective differentiated theta remainder is still required for that route.

## 3. Finite calibration of the predicted scale

`tail_and_rank_budget.py` compares Q(n) with actual finite differences from the
coefficient balls. For centers n=2,10,50,118, the curvature/Q ratios are
approximately 0.09099, 0.40016, 0.72229 and 0.83239. All 117 tested curvatures
are positive. Each comparison is a ball enclosure at a finite index; none is
used as a fitted asymptotic remainder or a tail certificate.

## 4. An all-rank budget that permits negative corrections

For the normalized determinants A_r and factors B_r from the preceding note,
write delta_r=-log t_r and C_r=2 log B_r-log B_r,- -log B_r,+.
Fix an interior shift m>=2 and suppress m. With delta_0=0,

```
delta_(r+1)-delta_r = delta_r-delta_(r-1)+C_r
                      = delta_1 + sum_(k=1)^r C_k.
```

Equivalently,

```
delta_r = r delta_1 + sum_(k=1)^(r-1) (r-k) C_k
A_r = A_1^r product_(k=1)^(r-1) B_k^(r-k).
```

The second identity follows by iterating the normalized condensation
factorization; it does not express Xi as an independently positive product.
B_1(m)=epsilon_m, so the theta estimate controls precisely the first correction.

A sufficient cumulative condition is

```
sum_(k=1)^R max(0,-C_k(m)) <= delta_1(m)/2   for every R and m>=2.
```

It implies every slope is at least delta_1/2 and hence
`delta_r(m)>=r delta_1(m)/2>0` when delta_1>0. It permits negative C_k and does
not require their individual log-concavity. The fraction 1/2 is a trial budget,
not a fitted theorem; any fixed fraction strictly below one would suffice.

`Reinmann/TuranDeficit.lean` now proves the exact cumulative slope identity
and the resulting linear lower bound, for an arbitrary real sequence with
the recurrence and cumulative budget as explicit hypotheses. No Xi budget
or determinant identity was added as an axiom.

For Xi, positivity needed to define these logarithms must not be assumed at
all ranks. A valid proof would establish the budget on each already-positive
finite prefix and use it in the next condensation step; t_r<=1 then gives
B_r>=1 and positivity of A_(r+1). This prefix extension must work simultaneously
at neighboring shifts and with a separate shift-one boundary argument. Simply
postulating a positive infinite determinant array would be circular.

The new finite scan checks 4,347 contiguous rank prefixes, through correction
rank 46 where the input table permits them. Every half-base loss budget is
strictly positive. The maximum upper bound for loss/delta_1 is less than
0.051206. This does not bound the omitted ranks: a new analytical summability
or cumulative-loss theorem must supply that uniform control.

## Replay and artifacts

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/tail_and_rank_budget.py --coefficients research/certified_xi/coefficients_120.json --laboratory research/certified_xi/laboratory_120.json --output research/certified_xi/tail_and_rank_budget_120.json
uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/certified_xi -v
lake build
bash scripts/verify_axiom_clean.sh
```

The JSON records exact rational bounds, coefficient/laboratory hashes and all
numerical dependency hashes. Prefix gaps terminate a scan rather than being
silently skipped. Tests check model differentiation with exact dual numbers,
positive-domain failure, degenerate deficits, cumulative transport and gaps.
The analytic asymptotic proof above and the finite ball checks have distinct
trust boundaries; neither is represented as a completed continuous tail or
all-rank Xi theorem.

## Validation completed

- Certified-Xi suite: 28 tests passed.
- `lake build`: passed, 3,524 jobs; both new rank-budget lemmas elaborate.
- `bash scripts/verify_axiom_clean.sh`: passed, 103 audited theorems, no sorry/admit or custom axioms.
- Generator: completed with 117 positive discrete curvature samples and 4,347 positive finite half-base budgets.
- Numerical dependency hashes and exact rational budget bounds: verified.
- `git diff --check`: passed.

The asymptotic deduction is presented for mathematical review; it is not
validated by the unit tests or formalized by the two algebraic Lean lemmas.
