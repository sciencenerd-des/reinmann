# Uniform shift-one boundary and effective curvature-error propagation

This pass closes the shift-one boundary subproblem under the repository's
analytic-numerical trust boundary. A finite contour computation and explicit
geometric remainder bounds prove the strengthened boundary inequality at every
rank, and prove positive boundary correction curvature at every rank. The
interior all-rank budget and an effective first-summand saddle remainder remain
open. This is not a Lean-checked analytic theorem or a proof of RH.

## Statement and normalization

Let a_n=mu_n/mu_0 and

```
E(z)=sum a_n z^n = xi(1/2+sqrt(z))/xi(1/2)
F(z)=E(-z)
H(z)=1/F(z)=sum h_n z^n near z=0.
```

The square root notation denotes the entire folded function, not a branch
choice in the certified polynomial calculations. Coefficients a_n are positive
by the theta moment identity, independently of RH. The certificate establishes

```
h_n > 0,
0 < t_n(1)=(n+1)(1-h_(n-1)h_(n+1)/h_n^2) < 1  for every n>=1,
C_r(1)=delta_(r+1)(1)-2delta_r(1)+delta_(r-1)(1) > 0  for every r>=1,
delta_n(1)=-log t_n(1),  delta_0(1)=0.
```

As previously derived, t_n(1) is the normalized Toeplitz boundary ratio. Thus
these are boundary statements for unbounded rank, not all-shift assertions.
Positive C_r(1) implies the boundary cumulative negative loss is exactly zero.

## 1. Certifying exactly two zeros in a bounded disk

Use the degree-120 polynomial P(z)=sum_(n=0)^120 (-1)^n a_n z^n from the
coefficient balls. Put R=600 and S=1200. Positive coefficients imply

```
|F(z)-P(z)| <= E(S)(R/S)^121 = tau,  |z|<=R.
```

Indeed each omitted factor (R/S)^n is at most (R/S)^121, and the sum of
a_n S^n is E(S). The computation uses the original xi special-function
formula at the real argument 1/2+sqrt(S), giving E(S) about 2.322194329e8
and tau less than 8.736e-29. Similarly,

```
|F'(z)-P'(z)| <= (121/R) tau,  |z|<=R,
```

because n(R/S)^n decreases for all n>=121. The corresponding ratio
condition is checked explicitly.

Partition |z|=600 into 256 arcs. For each midpoint c, translate P exactly in
ball arithmetic and write P(c+w)=sum b_j w^j. Every point in that arc satisfies
|w|<=600*pi/256. Therefore

```
|P(z)-P(c)| <= sum_(j>=1) |b_j| (600*pi/256)^j.
```

The computed image disk excludes zero on every arc, and its lower modulus
bound exceeds tau. The smallest certified polynomial lower bound exceeds
1.1323e-6. Taylor translation is important: direct interval Horner evaluation
on a wide z-ball would lose the cancellation in P near its positive zeros.

Each arc image lies in a disk excluding zero. Its possible arguments lie in
an interval of width less than pi, so its argument change is the principal
argument of the endpoint quotient. Summing the enclosed increments gives a
winding enclosure strictly inside (1.75,2.25) and containing 2. Since the
winding number is an integer, it equals 2. The argument principle counts two
zeros of P, with multiplicity. Rouche's theorem transfers that count to F.
No root table or global zero hypothesis is an input.

Separate real sign-changing brackets inside (199,201) and (441,443), evaluated
with the same polynomial-tail error, give two distinct real zeros R1,R2.
The total zero count forces both to be simple and excludes any other zeros
inside the disk. Refined enclosures give

```
R1 approximately 199.790454832386859464
R2 approximately 441.926150574082490320.
```

Polynomial derivative balls plus the derivative tail enclose the full
F' at these roots. The normalized pole amplitudes -1/(Ri F'(Ri)) have
opposite signs:

```
A approximately 50.871036332161575 > 0
-B approximately -2664.551870803 < 0.
```

## 2. A Cauchy bound for every reciprocal coefficient

The function

```
H(z) - A/(1-z/R1) + B/(1-z/R2)
```

has its two poles removed and is analytic throughout the disk. On its boundary
it is bounded by

```
M = 1/(min_circle|P|-tau) + A/(R/R1-1) + B/(R/R2-1).
```

Every quantity is enclosed using root/amplitude balls, not rounded decimals.
The resulting upper bound is below 890633. Cauchy's coefficient estimate gives

```
h_n = A alpha^n - B beta^n + e_n,
|e_n| <= M R^(-n),
alpha=1/R1 > beta=1/R2 > 1/R.
```

This is a bound for every coefficient index, not an extrapolation from a
finite table. Removing the two poles requires no information about zeros
outside |z|=600.

## 3. Effective boundary tail from rank 26

Set T=(alpha-beta)^2/(alpha beta), s=beta/alpha and g_n=A alpha^n-B beta^n.
The exact identity

```
g_n^2-g_(n-1)g_(n+1)=A B T (alpha beta)^n
```

gives a positive main term. Define the positive geometric sums

```
p_n = (B/A)s^n + (M/A)(1/(R alpha))^n
v_n = M/(B T) (1/(R beta))^n [2+R alpha+1/(R alpha)]
    + M/(A T) (1/(R alpha))^n [2+R beta+1/(R beta)]
    + 2M^2/(A B T) (1/(R^2 alpha beta))^n.
```

Then |h_n/(A alpha^n)-1|<=p_n. Expanding the three errors in the determinant,
and bounding |g_j| by A alpha^j+B beta^j, gives

```
|(h_n^2-h_(n-1)h_(n+1))/(A B T (alpha beta)^n)-1| <= v_n.
```

Every geometric base is strictly below one, so p_n and v_n decrease.
At n=26 the certificate verifies p_n<1/2 and v_n<1. These imply h_n>0 and
positive determinant gap for every n>=26. They also imply

```
t_n(1) <= 8(n+1)(B/A) T s^n.
```

The right side is below 8.160e-6 at n=26 and decreases thereafter; the
successive-ratio condition s(n+2)/(n+1)<1 is checked at the threshold.
Thus 0<t_n(1)<1 for every n>=26. Fresh reciprocal-coefficient calculations
certify ranks 1..25, so the finite bridge leaves no gap. Positivity at index
zero is h_0=1. No higher finite ranks are needed for this tail argument.

## 4. Uniform positivity of the boundary correction

The preceding coefficient and determinant estimates give

```
delta_n(1)=constant+n log(alpha/beta)-log(n+1)+E_n,
|E_n| <= -log(1-v_n)-2 log(1-p_n).
```

Where p_n,v_n<1/2, the right side is at most 2v_n+4p_n. Put

```
rho=max(s,1/(R alpha),1/(R beta),1/(R^2 alpha beta)) < 1.
```

For n>=K-1, the geometric sums are bounded by their values at K-1 times
rho^(n-K+1). The second difference of the model is

```
log((r+1)^2/(r(r+2))) >= 1/(r+1)^2.
```

The absolute error of that second difference is at most

```
(8v_(K-1)+16p_(K-1)) rho^(r-K),  r>=K.
```

At K=61, the certificate verifies

```
(8v_60+16p_60) * 62^2 < 0.889,
rho*(63/62)^2 < 0.761.
```

Hence the error stays strictly smaller than 1/(r+1)^2 for all r>=61:
the error times (r+1)^2 decreases geometrically. Thus C_r(1)>0 throughout
that unbounded range. Fresh dual determinant calculations certify C_r(1)>0
for r=1..60. Together these establish zero negative correction loss at the
boundary for every rank.

The identity C_r(1)=2 log B_r(1)-log B_r(2) uses B_r(0)=1. Its factors are
positive because the already-proved boundary inequalities imply positivity
of D_r(1) and D_r(2) for every r. It does not require assuming every interior
determinant positive.

## 5. Explicit propagation of saddle errors into curvature

`curvature_error.py` implements an independent conditional error-transfer
lemma. Let q,L,M approximate q,ell',ell'' respectively, and suppose their
absolute errors are e0,e1,e2. Enclose the perturbed q in (0,1), let Q be its
upper bound, d its deficit lower bound, A=|L|+e1, B=|M|+e2. For

```
F(q,L,M)=-1/(x+1)^2-q M/(1-q)-q L^2/(1-q)^2,
```

the mean-value theorem on the perturbation box gives

```
|F_true-F_model| <= [B/d^2+(1+Q)A^2/d^3] e0
                  + 2Q A/d^2 e1 + Q/d e2.
```

These coefficients bound the absolute partial derivatives of F. This keeps
the reference cancellation in F_model, while making the permissible errors
explicit. The routine refuses to certify a sign if the perturbed deficit
may vanish or the curvature enclosure crosses zero.

It also converts relative errors in three moment approximations into log-moment
errors. If |I_k/Jhat_k-1|<=eta_k is understood as the absolute inequality
|I_k-Jhat_k|<=eta_k |Jhat_k|, Jhat_0>0 and eta_0<1, put
A0=|Jhat_1/Jhat_0|, B0=|Jhat_2/Jhat_0|. Valid bounds are

```
error(log I_0) <= -log(1-eta_0)
ep = error(I_1/I_0) <= A0(eta_1+eta_0)/(1-eta_0)
error((log I_0)'') <= B0(eta_2+eta_0)/(1-eta_0)+ep(2A0+ep).
```

Add neighboring errors with weights 1,2,1 for ell and its derivatives. An
absolute log-q error e gives absolute q error at most |q_model|(exp(e)-1).
These bounds feed the curvature-transfer lemma.

If eta bounds the omitted-theta error relative to the first summand, and sigma
bounds its saddle error relative to the proposed model, a valid combined
relative error is sigma+eta(1+sigma). The omitted-theta bounds are available;
the required effective sigma functions are not. The module labels successful
outputs as conditional on supplied errors and never derives a saddle remainder
from sampled agreement. Thus it completes error propagation, not the missing
saddle estimate itself.

## Scope, trust, and replay

The uniform boundary result is an analytic-numerical certificate based on
FLINT ball arithmetic, the classical theta/Taylor identification, coefficient
positivity, winding/argument principle, Rouche, Cauchy, and determinant identities.
The analytic argument is documented here, not checked by Lean. It makes no
novelty claim and does not establish the interior cumulative rank budget or RH.
The prime-defined program remains separate and uses no output from this route.

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/pole_boundary.py --coefficients research/certified_xi/coefficients_120.json --output research/certified_xi/pole_boundary.json
uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/certified_xi -v
```

The JSON includes all 256 contour lower bounds and argument increments, the
function/derivative tails, signed root brackets and amplitudes, Cauchy constant,
tail inequalities, finite bridges, input hash and numerical source hashes.
The tests include known polynomial root counts, a contour through a root,
wrong expected count, excessive truncation error, exact two-pole determinant
algebra, failed tail criteria, full Xi replay and curvature perturbation corners.

## Validation completed

- Certified-Xi suite: 37 tests passed, including a complete replay of the
  uniform boundary certificate and both finite bridges.
- All recorded numerical source hashes, contour lower bounds, winding bounds,
  tail inequalities and finite-bridge lengths were checked.
- `git diff --check`: passed.
- No Lean source changed in this pass. The new complex-analysis argument and
  perturbation lemma are documented mathematical proofs with numerical checks,
  not additions to the Lean kernel's theorem set.

The remaining work is to prove effective first-summand saddle error functions
and feed them through the transfer lemma, and to control the cumulative loss
uniformly at interior shifts m>=2. The boundary result supplies a completed
input to that program; it does not imply those interior estimates.
