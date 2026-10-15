# Analytic domain and mass bounds for the Xi coefficient candidate

Written mathematical argument, 2026-10-10. The Hilbert-space and closed-graph
arguments below have not been formalized in Lean or independently reviewed.
The companion Lean files check the coefficient-domain construction and exact
coherent-state identities. Neither layer proves symmetry or RH.

## Gaussian growth from the arithmetic theta kernel

Use the classical representation

```text
ξ(s) = 2 ∫_0^∞ Φ(u) cosh((s-1/2)u) du,
Φ(u) = Σ_(j≥1) (4π²j⁴ exp(9u/2) - 6πj² exp(5u/2)) exp(-πj² exp(2u)).
```

The normalization is that of Romik,
[Orthogonal polynomial expansions for the Riemann xi function, (1.8)–(1.11)](https://www.math.ucdavis.edu/~romik/data/uploads/papers/riemannxi.pdf).
Evenness changes the full Fourier integral to twice the half-line cosine
integral; substituting `t=-i(s-1/2)` gives the displayed formula. Local dominated
convergence extends the integral to all complex s.

For `u≥0`, every summand is positive. Define the finite numerical constant
`C₀ = Σ_(j≥1) j⁴ exp(-π(j²-1))`. Termwise domination gives

```text
0 < Φ(u) ≤ 4π² C₀ exp(9u/2 - π exp(2u)).
```

For any `0<b<1/2`, let

```text
C_b = 2 ∫_0^∞ Φ(u) exp(u/2 + u²/(4b)) du.
```

This is finite: the upper integrand is bounded by a constant times
`exp(5u + u²/(4b) - π exp(2u))`, which is integrable at infinity; it is
continuous at zero. The inequalities
`|cosh((s-1/2)u)| ≤ exp((|s|+1/2)u)` and
`|s|u ≤ b|s|² + u²/(4b)` then prove the global bound

```text
|ξ(s)| ≤ C_b exp(b|s|²).                                    (1)
```

The bound and its constants use the theta/integer series, not the locations
of zeros. No RH or spectral-reality premise occurs.

## Bounded arithmetic row functionals

Let H be the Fock space with

```text
f(z)=Σ c_n z^n,    ||f||² = Σ n! |c_n|²
                         = (1/π) ∫_ℂ |f(z)|² exp(-|z|²) dA(z).
```

The equivalence follows by integrating monomials in polar coordinates, first
for polynomials and then for square-summable coefficient limits. In particular,
`|f(z)|≤||f|| exp(|z|²/2)` by Cauchy–Schwarz, so these limits define entire
functions and each coefficient evaluation is continuous.

For every integer `n≥0`, (1) and the elementary gamma integral give

```text
||z^n ξ||² ≤ C_b² n! / (1-2b)^(n+1).                       (2)
```

Indeed the polar-coordinate radial integral is
`2 ∫_0^∞ r^(2n+1) exp(-(1-2b)r²) dr = n!/(1-2b)^(n+1)`.

Write `a_k=ξ⁽ᵏ⁾(0)/k!`. The coefficients are real, since the theta integral
gives `ξ(conjugate z)=conjugate ξ(z)`. For any `c∈H`, the row

```text
R_n(c) = Σ_(k≥0) (k+n)! a_k c_(k+n) = η(c,z^n ξ)
```

converges absolutely. Cauchy–Schwarz and (2) yield the explicit bound

```text
|R_n(c)| ≤ C_b sqrt(n!) / (1-2b)^((n+1)/2) * ||c||.         (3)
```

Consequently `K_ξ = intersection_(n≥0) ker R_n` is a closed complex subspace
of H. Equivalently it is the orthogonal complement of the closed span of
`{z^n ξ : n≥0}`. This defines the arithmetic state space using ξ and
integer-indexed operations, rather than assigning a basis to its zeros.

## Closed operator on an explicit domain

On H the maximal differentiation operator is

```text
(Ac)_n=(n+1)c_(n+1),
Dom(A) = {c∈H : Σ n! |(n+1)c_(n+1)|² < ∞}.
```

It is closed. If `c_j→c` and `Ac_j→d` in H, continuity of each coordinate
implies `d_n=(n+1)c_(n+1)` for every n. Since `d∈H`, this is exactly
`c∈Dom(A)` and `Ac=d`.

For `c∈K_ξ∩Dom(A)`, the absolutely convergent row identities give
`R_n(Ac)=R_(n+1)(c)=0`; hence `Ac∈K_ξ`. Restrict A to
`Dom(A_ξ)=K_ξ∩Dom(A)`, with codomain `K_ξ`, and set

```text
T_ξ = -i(A_ξ - 1/2).
```

The restriction is closed because K_ξ is closed and the graph of A is closed.
The scalar multiple and bounded scalar shift preserve closedness. This argument
does not establish density of the restricted domain, identify the adjoint,
describe the full spectrum, or establish self-adjointness. None of these claims
is inferred from closedness.

## Exact states and mass

For every complex s, `v_s(z)=exp(sz)` has coefficients `s^n/n!`, and

```text
||v_s||² = exp(|s|²),    A v_s = s v_s,
R_n(v_s) = s^n ξ(s).
```

Thus `v_s∈K_ξ iff ξ(s)=0`. At every such zero it lies in the restricted
derivative domain, since `||A v_s||²=|s|² exp(|s|²)<∞`.
The normalized state `u_s=exp(-|s|²/2)v_s` satisfies

```text
||u_s||² = η(u_s,u_s)=1,
T_ξ u_s = -i(s-1/2)u_s.                                  (4)
```

This establishes finite nonzero selected-state masses and domain membership
at every zero, without a height cutoff or an RH assumption, in the written
Hilbert-space construction. A critical-strip ζ zero is a ξ zero by the
nonvanishing prefactor in the completed-product identity.

For explicit coefficient truncations, write `r=|s|²` and
`p_n=exp(-r) r^n/n!`. The degree-N truncation `u_s^[N]` has mass
`q_N=Σ_(n=0)^N p_n`. If `N+2>r`, comparison of consecutive tail terms gives

```text
0 ≤ 1-q_N ≤ B_N := p_(N+1)/(1-r/(N+2)),
q_N ≥ max(exp(-r), 1-B_N) > 0.
```

The last strict inequality follows from `exp(-r)>0`, even if `1-B_N≤0`.
There is just one nonzero residual coefficient:

```text
T u_s^[N] - λ(s) u_s^[N] = i s (u_s)_N e_N,
||residual||² = r p_N,
|d(u_s^[N],residual)| ≤ 2 sqrt(r p_N q_N).
```

These elementary bounds explain the numerical diagnostics and provide actual
mass and paired-residual budgets for the finite vectors. They do not place the
truncations in `K_ξ`: polynomial truncation need not preserve the Xi row
constraints. Nor do they bound the independent operator-symmetry defect to zero.
These truncation estimates are written arguments, not additional Lean theorems.

The missing hypothesis is still substantive. The natural Fock pairing gives
`η(T_ξu_s,u_s)-η(u_s,T_ξu_s)=-2i(Re(s)-1/2)`. An independent arithmetic argument
that makes this vanish at every zero would prove RH. Neither (1)–(4) nor
closedness supplies that argument.

Continue the full objective by testing arithmetic changes to the form or the
realization, with both selected-state mass and symmetry checked. Do not declare
the objective complete on the basis of this nonsymmetric candidate.
