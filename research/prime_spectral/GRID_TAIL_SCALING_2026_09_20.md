# Remove the forced grid factor before testing quotient convergence

Follow-up: the [spectral-sum budget](QUOTIENT_COEFFICIENT_BUDGET_2026_09_20.md)
supplies an explicit bound on the quotient polynomial and its Taylor tail.
A sequence-wide bound on its spectral sum remains unproved.

## Results and scope

Let L=log(C)>0 and N>=1 be the support length and mode cutoff of the
existing prime-defined quotient construction. Assume its finite gates:
a simple even lowest eigenvector, nonzero normalization at the origin,
and a positive quotient metric. Let B be its 2N-dimensional quotient
matrix and P_(N,L) the origin-normalized entire Fourier profile.

There is an exact entire factorization

    P_(N,L)(z)=R_(N,L)(z)*G_(N,L)(z),
    R_(N,L)(z)=det(zI-B)/det(-B),
    G_(N,L)(z)=product_(k>N) [1-(zL/(2pi*k))^2].       (1)

The polynomial R uses only the prime-defined quotient, is normalized at
zero, and has only real zeros. It is a separate, concrete convergence
target with the forced exterior grid zeros removed.

For L_j tending to infinity, convergence of the unmodified P_j to
Xi(z)/Xi(0), locally uniformly on the complex plane, necessarily requires

    L_j^2/N_j -> 0, equivalently N_j/(log C_j)^2 -> infinity. (2)

This is stronger than the previously proved N_j/L_j -> infinity.
It is necessary, not sufficient. No convergence to Xi, uniform finite
gates, or RH theorem is proved here. The condition (2) concerns P, not
an asserted necessary scaling for the newly separated polynomial R.

## 1. Exact removal of the exterior grid

The existing quotient theorem proves Q(z)=det(zI-B) is an even polynomial
with only real zeros and Q(0)!=0. Evenness follows from the even Fourier
coefficients; Q(0)!=0 follows from the nonzero central coefficient.
Its Fourier identity gives P as a sine factor times Q divided by the
full grid polynomial on -N,...,N. Cancel those finite grid factors using
the [sine product, DLMF 4.22.1](https://dlmf.nist.gov/4.22#E1).
Both sides normalize to one at zero, giving (1). The product G converges
uniformly on compact sets because sum k^(-2) converges. Removable grid
singularities are handled by the entire product identity.

Pair the real nonzero roots of Q as +/-lambda_l, with multiplicity.
Then for every real y>=0,

    R(iy)=product_(l=1)^N (1+y^2/lambda_l^2)>=1,
    P(iy)>=G(iy)>0.                                 (3)

Thus the quotient polynomial cannot cancel positive imaginary-axis
growth contributed by the exterior grid product. This is a consequence
of the established real-zero finite gates; it is not presumed for an
arbitrary matrix or unchecked Fourier vector.

## 2. Effective upper and lower bounds

For any disk |z|<=rho, expansion of the absolutely convergent product
and product(1+a_k)<=exp(sum a_k) for a_k>=0 give

    |G(z)-1|<=exp[rho^2 L^2/(4pi^2 N)]-1.             (4)

Here sum_(k>N) k^(-2)<=1/N follows by integration. This estimate
needs no spectral data or Xi coefficients and holds for every N>=1.
In particular (2) makes G tend to one uniformly on every compact set.

For y>=0 put x=yL/(2pi). Since log(1+t)>=t/(1+t),

    log G(iy)=sum_(k>N) log(1+x^2/k^2)
      >= x^2/[(N+1)*(1+(x/(N+1))^2)].               (5)

We used k>=N+1 to bound the denominator and
sum_(k>N) k^(-2)>=1/(N+1). The right side also bounds log P(iy)
from below by (3). These two effective formulas are implemented with
FLINT balls in `grid_tail.py`.

## 3. Necessary scaling for the unmodified Xi target

Suppose P_j converges locally uniformly to normalized Xi and L_j->infinity.
The existing forced-zero argument first implies N_j/L_j->infinity.
If (2) fails, take a subsequence for which L_j^2/N_j>=epsilon>0.
For any fixed y>0, x_j/(N_j+1) tends to zero and N_j/(N_j+1) tends
to one. Equations (3)-(5) and convergence imply

    log[Xi(iy)/Xi(0)] >= epsilon*y^2/(4pi^2).         (6)

This uses the limit at a fixed y. Only after taking that limit do we
let y increase in the resulting inequality for Xi; no interchange of
a moving-height limit with local uniform convergence is involved.

Write Xi(z)=xi(1/2+iz). The
[xi functional equation and definition, DLMF 25.4.3–4](https://dlmf.nist.gov/25.4#E3)
give Xi(iy)=xi(1/2+y). For large positive y, all factors in the defining
expression are positive. For real s>=2, the Dirichlet series gives
1<=zeta(s)<=1+1/(s-1), by the decreasing-function integral bound.
[Stirling's expansion, DLMF 5.11.1](https://dlmf.nist.gov/5.11#E1)
then yields

    log[Xi(iy)/Xi(0)]=(y/2)log y+O(y)=o(y^2).

This unconditional growth estimate contradicts (6) for sufficiently
large y. Therefore (2) is necessary. No assumption about the locations
of Xi zeros was used in the growth estimate.

## 4. What remains at critical scaling

For completeness, if N_j/L_j->infinity and L_j^2/N_j->alpha with
0<=alpha<infinity, then locally uniformly

    G_j(z) -> exp[-alpha*z^2/(4pi^2)].               (7)

On each fixed disk, all individual factors are eventually close to one.
Expand log(1-w)=-w+O(|w|^2) uniformly there. The quadratic term is
-z^2 L_j^2/(4pi^2) sum_(k>N_j)k^(-2), whose limit is
-alpha*z^2/(4pi^2). The remainder is bounded by a constant times
rho^4 L_j^4/N_j^3 and tends to zero. Exponentiating proves (7).
Thus critical N proportional to L^2 leaves an explicit Gaussian factor,
although N/L already tends to infinity. Formula (3), rather than a
mere assertion about that Gaussian, is what rules it out for the
unmodified Xi target.

## 5. Separating the convergence questions

Under (2), equation (4) gives G_j->1 locally uniformly. On each compact
set it is eventually nonvanishing and its reciprocal tends to one.
Consequently

    P_j -> F locally uniformly iff R_j -> F locally uniformly. (8)

The quantitative finite decomposition also gives

    sup_|z|<=rho |P_j-R_j|
      <= sup_|z|<=rho |R_j| * (exp[rho^2 L_j^2/(4pi^2 N_j)]-1).

A bound on R_j is still needed to turn this into an absolute error
estimate. It must not be inferred from the grid estimate alone.

Alternatively, studying R_j directly removes the grid factor without
requiring it to be close to one. This changes the convergence target
from the original Fourier profiles to normalized characteristic
polynomials and requires its own justification. It does not prove
that these polynomials approach Xi. Their coefficients and zeros are
computed solely from prime-defined finite matrices.

The missing arithmetic work is now explicit: prove the finite gates
along a sequence, obtain compact bounds for R_j, and identify its
locally uniform limit with Xi. Normalization at zero and real zeros
alone cannot identify that limit.

## Implementation and validation

`quotient_polynomial_profile` evaluates det(zI-B)/det(-B), rejecting an
unresolved zero denominator. The separate finite quotient gate is still
required for the real-zero conclusion. No Xi coefficient or zero data
enter the implementation.

Four tests check complex-disk and imaginary-axis bounds against the
explicit sine/finite-product formula, test the lower bound for a fresh
certified prime profile, verify P=R*G at a complex argument, and exercise
invalid domains and normalization failures. Finite tests validate the
implementation; the pathwise claims are the analytic proofs above.

```sh
uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/prime_spectral -v
```

The proof is not Lean formalized. The independent prime convergence
program and RH remain open.
