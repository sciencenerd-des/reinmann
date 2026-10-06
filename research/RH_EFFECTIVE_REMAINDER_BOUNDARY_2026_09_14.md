# Effective theta-series remainder and boundary control

There is now an explicit uniform bound for replacing the theta kernel by its
first summand, including logarithmic moment orders 0 through 4. This controls
one component of the effective remainder problem. It does not yet control
the error of a saddle approximation to that first-summand integral.
The shift-one boundary also has an exact reciprocal-coefficient reduction and
extended finite certificates. No uniform all-rank Xi budget is proved.

## Uniform theta-series remainder

Write Phi=phi_1+R, where

```
phi_j(u)=4 pi^2 j^4 exp(9u/2-pi j^2 exp(2u))
         * (1-3/(2 pi j^2 exp(2u))).
I_k(x)=integral_0^infinity u^(2x)(2 log u)^k Phi(u) du
J_k(x)=integral_0^infinity u^(2x)(2 log u)^k phi_1(u) du.
```

These are the kth parameter derivatives of the respective zero-order
moments. Their differentiation is justified on compact parameter ranges by
the existing logarithmic-moment domination argument.

Fix X>=0, U>=1, V>U, h>0 and k in {0,1,2,3,4}. Define E=exp(2U) and

```
rho = 16 exp(-3 pi E) /
      [(1-16 exp(-5 pi E))(1-3/(2 pi E))].
```

For every u>=U, 0<=R(u)<=rho phi_1(u). To see this, divide by phi_1, discard
the negative term in each omitted summand, and bound the remaining sum by
sum_(j>=2) j^4 exp(-pi(j^2-1)E). Its initial term is 16 exp(-3pi E), and its
successive ratios are at most 16 exp(-5pi E). The denominator correction in
phi_1 increases with u. All denominators are checked positive with balls.

For 0<=u<=U, the full kernel is bounded by

```
B(U)=4 pi^2 exp(9U/2-pi)/(1-16 exp(-3pi)).
```

This follows by discarding negative summands and applying a geometric ratio
bound to sum j^4 exp(-pi j^2). Consequently the absolute low-region moment
of either R or phi_1 is bounded by

```
N_k(x)=B(U) [2^k k!/(2x+1)^(k+1)
       + (U^(2x+1)-1)/(2x+1) * (2 log U)^k].
```

The first term is the exact integral of u^(2x)|2 log u|^k on [0,1]. The
second bounds the logarithm by log U on [1,U]. For k=0 the logarithmic
factor is one; for U=1 the second term vanishes.

A positive contribution to J_k from [V,V+h] is at least

```
L_k(x)=h V^(2x)(2 log V)^k
       * 4 pi^2 exp(9V/2-pi exp(2(V+h)))
       * (1-3/(2 pi exp(2V))).
```

All factors except V^(2x) are independent of x. Dividing each integral in
N_k by V^(2x) shows N_k(x)/L_k(x) decreases with x, because u<V throughout
the low region. Put beta=N_k(X)/L_k(X). If beta<1, the signed J_k is positive
for every x>=X: even orders are positive integrals, while at odd orders the
negative contribution on [0,1] is no greater than N_k.

Let P denote the first-summand moment over [U,infinity). Since U>=1 its
integrand is nonnegative. In both parity cases P<=J_k+N_k. Therefore

```
|I_k-J_k| <= N_k + rho P <= rho J_k + (1+rho) N_k,
J_k >= L_k-N_k,
|I_k(x)-J_k(x)|/J_k(x) <= rho+(1+rho) beta/(1-beta)  for every x>=X.
```

This is a uniform analytical inequality, with FLINT used to evaluate its
explicit constants. It uses neither pointwise sampling nor a fitted error bar.

With V=U+1/4 and h=1/8, the maximum bound over k=0..4 is:

| Threshold X | Cutoff U | Relative error bound for every x>=X |
|---:|---:|---:|
| 256 | 1 | less than 9.757e-30 |
| 4096 | 2 | less than 5.379e-223 |
| 65536 | 3 | less than 8.290e-1651 |

The exact rational upper bounds are in `certified_xi/effective_theta_remainder.json`.
The first-summand moments themselves have not been replaced by a saddle model
in this statement. In particular, a small fixed relative moment error can
still dominate a very small curvature after cancellation at sufficiently large
x. To finish the continuous theta estimate one needs effective first-summand
saddle bounds and propagation of both error sources through G, with cutoffs
chosen as functions of the parameter where necessary.

## Exact shift-one boundary

Let a_n=mu_n/mu_0 and define h_n by

```
H(z)=1/(sum_(n>=0) (-1)^n a_n z^n)=sum_(n>=0) h_n z^n.
```

As formal power series, h_0=1 and
h_n=sum_(j=1)^n (-1)^(j-1) a_j h_(n-j). Dual Jacobi-Trudi identities give

```
D_r(1)=h_r,    D_r(2)=h_r^2-h_(r-1)h_(r+1),    D_r(0)=1.
```

With the exponential reference normalization,
P_r(1)=1/r! and P_r(2)=1/[r!(r+1)!]. Hence

```
t_r(1)=A_r(0) A_r(2)/A_r(1)^2
      =(r+1)(1-h_(r-1)h_(r+1)/h_r^2).
```

For positive h_r, simultaneous next-column positivity and the strengthened
boundary inequality amount to the band

```
r/(r+1) <= h_(r-1)h_(r+1)/h_r^2 < 1.
```

The lower inequality is equivalent to log-convexity of r! h_r. It is a new
explicit target, not a proved all-rank property of these reciprocal
coefficients. `boundary_ratio_le_one_iff` in Lean proves the scalar algebraic
equivalence; it does not assert the analytic band or the general dual identity.

At shift zero A_r(0)=1 at every rank, so its multiplicative correction is
B_r(0)=1. The boundary correction is consequently

```
C_r(1)=2 log B_r(1)-log B_r(2),
```

with no fictitious t_r(0), negative coefficient moment, or epsilon_0. The
cumulative slope and loss-budget arguments now apply at m=1 with this
separately derived correction. Positivity must still be established on each
finite prefix before using logarithms; assuming it at all ranks would be
circular.

## Finite boundary and high-rank stress tests

`boundary_budget.py` certifies 0<t_r(1)<1 for ranks 1..119 using the original
121 coefficient balls and formal reciprocal coefficients. It checks selected
dual identities against fresh direct determinants. The existing rank table
allows 47 boundary correction prefixes; every half-base loss budget passes.

`dual_rank_budget.py` extends the stress test without generating new Xi
coefficients. It evaluates the dual m-by-m determinant for D_r(m), rather
than an r-by-r determinant. This gives ratios for r<=113 and m<=7 using
matrices of size at most eight. It checks 560 interior prefixes at centers
m=2..6, through correction rank 112, and 113 boundary prefixes. All half-base
budgets pass. The largest interior loss/base upper bound is less than
0.051787; the boundary loss is zero on these prefixes. This extends the
previous scan's approximately 0.051206 maximum and is still below 1/2.
These are finite tests, not a uniform bound or a reason to assume omitted
ranks have no further negative corrections.

The boundary regression control uses coefficients (1,1,0.9,0.801). Its
reciprocal coefficients begin (1,1,0.1,0.001), giving t_2(1)=2.7>1. Thus
positive coefficients and positive reciprocal coefficients alone do not
establish the required boundary band, even on a short finite prefix.

## Replay

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/effective_theta_remainder.py --output research/certified_xi/effective_theta_remainder.json
uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/boundary_budget.py --coefficients research/certified_xi/coefficients_120.json --laboratory research/certified_xi/laboratory_120.json --output research/certified_xi/boundary_budget_120.json
uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/dual_rank_budget.py --coefficients research/certified_xi/coefficients_120.json --output research/certified_xi/dual_rank_budget_120.json
uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/certified_xi -v
lake build
bash scripts/verify_axiom_clean.sh
```

The uniform theta inequality relies on the displayed analysis and FLINT
constant enclosures; it is not imported as a Lean theorem. The finite
boundary and rank artifacts rely on coefficient enclosures and determinant
identities. The uniform Xi cumulative budget, the all-rank boundary band,
and the complete effective curvature estimate remain open.

## Completed validation

- Certified-Xi suite: 33 tests passed, including uniform-constant checks,
  omitted-term ratio controls, insufficient-threshold rejection, neutral and
  adversarial boundary cases, and dual-grid range and positivity checks.
- `lake build`: passed, 3,524 jobs.
- `bash scripts/verify_axiom_clean.sh`: passed, 104 audited theorems, no sorry/admit or project-declared axioms.
- All three generators completed; their numerical dependency hashes and the
  reported rational error/budget bounds were checked.
- `git diff --check`: passed.

The formal addition is the scalar boundary equivalence. The analytic uniform
moment remainder proof is documented above and its constants are enclosed by
FLINT; it is not certified by the Lean kernel.

## Subsequent uniform boundary result

The [2026-09-15 continuation](RH_UNIFORM_BOUNDARY_CURVATURE_2026_09_15.md)
replaces the finite-only boundary result with a two-pole/Cauchy tail proof
and finite bridges. The interior rank budget and first-summand saddle error
are still open; the boundary inequality and boundary correction positivity
now hold for all ranks under the stated analytic-numerical trust boundary.
