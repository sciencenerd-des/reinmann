# A coupled density budget on a complete Weil support cell

The new [implementation](../../experiments/prime_spectral/weil_profile_cell_budget.py)
certifies an increment budget for the exact origin-normalized even ground
profiles throughout `17<=C<=19`, at Fourier cutoff `N=8`. It includes
moving spatial endpoints, all 32 support subcells, and their certified
candidate-to-ground transfer errors. By the
[full parity certificate](WEIL_FULL_CELL_GATES_2026_10_05.md), these are
also the simple full ground profiles.

For **every** two supports `C1<=C2` in this cell, the certificates give

| Frequency strip, all real parts | Exact profile increment bound |
|---|---:|
| `abs(Im z)<=2/5` | `<0.085421` |
| `abs(Im z)<=1` | `<0.203537` |

The first bound improves the corresponding termwise density bound,
`<1.473447`, by more than a factor of 17. The candidate-to-ground
transfer contribution in that first budget is below `1.475e-18`.
The spatial endpoint flux is explicitly bounded, rather than treating
the zero-extended moving-support density as differentiable in L2.

This is a finite C0 increment theorem. It proves neither a derivative
bound for the exact ground profile nor its total variation over arbitrary
partitions. It does not establish a summable budget along an infinite
support/rank path, identify a limit with Xi, or prove RH.

## 1. Coupled projective density derivative

On one support subcell write `x=L-L0`, `L=log C`. Let `p_j(x)` be the
physical even coefficients of the degree-64 validated polynomial candidate,
obtained from its fixed exact orthogonal center eigenbasis. Put `g=p_0`.
The interval enclosure protects `g>0` throughout the subcell. The
candidate's normalized Fourier profile is the characteristic transform
of the signed density

```
rho(L,t) = [g+sqrt(2) sum_(j=1)^N p_j cos(2pi*j*(t/L+1/2))]/(L*g),
           |t|<=L/2.
```

Its integral is one exactly. Candidate kernel positivity is unnecessary
for the derivative estimate. Set `s=t/L`. Form these complete polynomials
before enclosing the temporal variable:

```
C0 = -g^2,
Cj = sqrt(2) * [L*(p_j' g-p_j g')-p_j g],
Sj = sqrt(2) * 2pi*j*p_j*g,
F(L,s) = C0 + sum Cj*cos(2pi*j*(s+1/2))
            + s*sum Sj*sin(2pi*j*(s+1/2)).
```

Ordinary differentiation at fixed physical `t` gives the exact identity

```
partial_L rho(L,t)=F(L,t/L)/(L^2*g^2).
```

Thus both the quotient-rule cancellation `p_j' g-p_j g'` and the signed
combination of coefficient drift with basis dilation are retained before
range evaluation. A common candidate scale `p_j=a(L)c_j` cancels from
the quotient-rule term identically. Taking separate bounds on `p_j' g`
and `p_j g'` would miss this cancellation.

The factor `L^2` belongs to the pointwise physical density derivative.
The integral uses `dt=L ds`, leaving only `L*g^2` in its denominator.
The independent analytic-series test checks this normalization directly.

The numerator is even in `s`. Equal interval tiles cover `[0,1/2]`,
including their endpoints. Arb trig enclosures bound the entire spatial
tile after the temporal polynomials have been enclosed on the entire
support subcell. Integrating these interval absolute bounds controls
`integral |F| ds`; the tile centers are not samples used as a proof.
The current certificates use 128 spatial tiles on the half interval.

For strip height `sigma>=0`, differentiating the moving-endpoint integral
and then taking absolute values yields

```
|d P_candidate(L,z)/dL|
 <= exp(sigma*Lmax/2) * [integral_(-1/2)^(1/2) |F(L,s)| ds/(L*g^2)
                        + |g+sqrt(2)*sum p_j|/(L*g)],
    abs(Im z)<=sigma.
```

The second term is the combined flux of the two moving spatial endpoints:
each endpoint moves with speed `1/2`, and their Fourier factors combine
into `cos(zL/2)`. The constant-mode check gives precisely
`d sinc(zL/2)/dL=[cos(zL/2)-sinc(zL/2)]/L`.
Absolute bounds on the interior and flux are taken only at this last step.
The resulting bound is uniform in the real part of `z`, so it avoids an
unbounded explicit `|z|` factor from separately differentiating sinc terms.

## 2. Recompute the ground transfer on the desired strip

The even eigenfamily certificate protects the unit candidate origin by
`c>d`, where `d` is the exact-to-candidate unit ground-vector distance.
Its Fourier-functional norm bound is

```
W_sigma = sqrt(sinh(sigma*Lmax)/(sigma*Lmax)),  W_0=1.
```

Therefore the established origin-normalized transfer proof supplies

```
delta_i(sigma)=W_sigma*d_i/(c_i-d_i)*(1+1/c_i).
```

The generator recomputes this bound on the requested strip from the
saved certified vector distance and origin lower bound. It does not
extrapolate a profile certificate valid only at height `2/5` to height
one. Height one includes the entire band containing possible nonreal
Xi zeros and a nonempty Euler region for a prospective identification
argument; summability and identification on that strip remain missing.

## 3. Transfer and telescope over the support cell

Let `V_i` be the candidate derivative bound on subcell `i`, with width
`w_i`, and let `delta_i` be its uniform exact-ground transfer bound.
For two points inside a subcell, the fundamental theorem of calculus
and the triangle inequality give

```
|P_ground(b,z)-P_ground(a,z)| <= V_i*(b-a)+2*delta_i.
```

For points spanning several subcells, telescope the exact profiles at
all shared boundaries. Continuity of the exact finite matrix and its
simple protected-origin ground family supplies the same exact profile
at each boundary. The local polynomial candidates may differ there;
using their individual transfer errors covers these discrepancies.
Consequently

```
|P_ground(L2,z)-P_ground(L1,z)|
 <= sum_(visited i) [V_i*visited_width_i+2*delta_i]
 <= sum_(all i) V_i*w_i + 2*sum_(all i) delta_i.
```

This proof applies to any two supports in the closed 17–19 cell,
including `C=17` and `C=19`. Its matrix branch is the right branch at
17 and the left branch at 19. Profiles are continuous at prime thresholds;
only derivatives jump. No endpoint jump in the profile is inserted.
The spatial endpoint flux above is a different boundary effect and is
included in each `V_i`.

The term `2*delta_i` is a C0 transfer allowance. Summing it over finer
and finer partitions would be invalid as a total-variation argument.
The certificate makes no exact-ground derivative or arbitrary-partition
variation claim.

## 4. What the odd-resolvent normalization does and does not change

Let `E,O` denote even and odd Weil blocks, `T=E_(1:N,1:N)-lambda I`,
`K=diag(1,...,N)`, `f=E_(1:N,0)`, and `a=K f`. The exact displacement
identity in the previous audit gives

```
O K-K E_(1:N,1:N)=-sqrt(2)*a*ones^T,
T=K^(-1)(O-lambda I)K+sqrt(2)*f*ones^T.
```

Origin-normalizing the boundary-normalized odd-resolvent reconstruction
therefore produces exactly the existing even constrained Schur solve.
It does not provide a new inverse bound or remove its gap dependence.
The independent integral-matrix tests verify this block identity at both
prime endpoints to interval precision; the written displacement proof
establishes it at arbitrary finite rank.

There is a useful exact determinant consequence. If
`h=(O-lambda I)^(-1)a`, the matrix determinant lemma gives

```
det T/det(O-lambda I)
 = 1+sqrt(2)*ones^T K^(-1)h = v_0/S,
S/v_0 = det(O-lambda I)/det T.
```

For a simple full ground with protected `v_0!=0`, both `O-lambda I`
and `T` are positive definite: `T` is the restriction of the positive
semidefinite ground-shifted even matrix to the origin-zero subspace,
which excludes its kernel. Their determinant ratio is strictly positive.
Thus the boundary and Fourier origin have the same sign at every such
finite rank. This refines the absolute boundary-rigidity theorem under
these additional ground and origin hypotheses. It does not prove
positivity of the entire spatial kernel.

In spectral form this gives the arbitrary-finite-rank factorization

```
S/v_0 = product_j [lambda_(odd,j)-lambda]
        / product_j [lambda_(origin-constrained,j)-lambda].
```

Here the constrained eigenvalues are those of the unshifted even tail
principal block. These are finite products; infinite-product bounds or
uniform asymptotics are not asserted. A smooth support branch also has

```
d/dL log(S/v_0)
 = Tr[(O-lambda I)^(-1)(O'-lambda' I)]
   - Tr[T^(-1)(E_tail'-lambda' I)].
```

This is a coupled trace identity whose two terms can be large. Bounding
them separately is not a uniform cancellation estimate. The identity
makes the remaining relative boundary-control target explicit, while
the density budget above provides the actual effective finite result.

## 5. The infinite-path budget still needed for RH

A sufficient convergence program now has explicit local constituents.
Along a sequence of finite full ground profiles, bound every support
transition by the density/transfer budget and every rank transition by
an independently certified rank-comparison bound. If the sum of those
transition bounds is finite on a strip, the profiles are uniformly
Cauchy there; its tail sum bounds the convergence error. This follows
directly from telescoping and completeness, not from the finite checks.

For a strip of height greater than `1/2`, also prove that the resulting
analytic limit equals normalized Xi on a set with an accumulation point
inside that strip, for example by a prime-defined Euler-region comparison.
The identity theorem then identifies the limit throughout the connected
strip. Each finite profile has only real zeros by the exact quotient
proof; Hurwitz's theorem rules out nonreal zeros of the nonzero limit.
The origin normalization gives limit value one at zero. The usual
critical-strip location of nontrivial zeta zeros then yields RH.
These are conditional implications using established complex analysis.
Their sequence-wide hypotheses are not proved here and the new proof
is not Lean formalized.

The [earlier Euler-region audit](PRIME_EULER_REGION_UNIQUENESS_2026_09_23.md)
provides a separate conditional identification route for the quotient
polynomials. Those polynomials and the current whole Fourier profiles
have different exterior-grid factors; their convergence hypotheses must
be kept distinct. In particular no finite density budget establishes
Euler-region agreement or a uniform all-rank recurrence. The theta
reference-curvature and interior all-rank obligations remain open.

## Artifacts and verification

- [Height 2/5 certificate](weil_profile_cell_budget_17_19_8_degree64.json)
- [Height 1 certificate](weil_profile_cell_budget_17_19_8_degree64_strip1.json)
- [Tests](../../experiments/prime_spectral/test_weil_profile_cell_budget.py)

Tests replay both whole-cell budgets, verify the physical derivative
against independent analytic series at three support centers and three
physical positions, verify quotient-rule cancellation under a common
candidate scale, check both endpoint flux factors for a constant mode,
and compare original endpoint profiles and explicit candidate derivatives
at real and imaginary frequencies against the budgets. The determinant
ratio is checked against the original boundary/origin ratio. Invalid
covers, origins, strip heights, and subdivision settings fail closed.
The numerical endpoint comparisons supplement the displayed whole-cell
proof; they are not its source of uniformity.

Validation: all 140 prime-spectral tests passed in 218.694 seconds.
Both new certificates' source and input hashes match the current files;
Python compilation, new-file whitespace checks and `git diff --check`
passed.

```sh
uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/prime_spectral -p test_weil_profile_cell_budget.py -v
```
