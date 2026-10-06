# A quantitative Weil-form projection budget for the prolate candidate

The [leakage sampling estimate](PROLATE_LEAKAGE_SAMPLING_2026_09_23.md)
controls the failure of the compact prolate candidate to be exactly
inversion-even. The [finite-Fourier diagonal](PROLATE_FOURIER_DIAGONAL_2026_09_23.md)
controls its ordinary `L2` projection error. Here those bounds are
combined with the logarithmic-order form of the prime-defined Weil
operator. The result is a **candidate approximation in the Weil form
norm**, not a comparison with the Weil ground state.

Put `C=lambda^2`, `L=log C`, `I=[-L/2,L/2]`, and
`K_C(t)=E(h_I)(exp(t))` on `I`, with midpoint values at its finitely
many jumps. Let `S K_C(t)=(K_C(t)+K_C(-t))/2`, and let `P_N` be the
orthogonal projection onto the constant and first `N` even cosine
modes. All functions below are extended by zero outside `I` when a
whole-line Fourier transform is taken. Write

```
q_log[H]=integral_R log(e+|xi|)*|hat(H)(xi)|^2 dxi.
```

The Fourier convention here is `exp(-2*pi*i*xi*t)`; changing to the
paper's unitary angular-frequency convention only changes absolute
constants.

## A BV-to-logarithmic-form estimate

If `H` has compact support, `||H||_2<=X`, and whole-line total
variation at most `W`, integration by parts against its derivative
measure gives `|hat(H)(xi)|<=W/(2*pi*|xi|)` for nonzero `xi`. For
every `Omega>=1`, Plancherel on the low frequencies and direct
integration on the high frequencies give

```
q_log[H]
 <= X^2*log(e+Omega)
    + W^2/(2*pi^2*Omega)*(log(e+Omega)+1).         (1)
```

The estimate includes endpoint jumps of the zero extension. It is
useful precisely because bounded variation alone does not bound
`q_log` uniformly, while the *combination* of a small `L2` norm and
polynomially bounded variation does.

## The odd candidate component is small in the Weil form

The leakage estimate gives, uniformly on `I`,

```
||K_C-S K_C||_infinity
  =O(C^(9/2)*exp(-pi*C/4)).                          (2)
```

The earlier variation estimate gives
`V_C=Var_I(K_C)=O(C^4*log C)`. Reflection and zero extension make
the whole-line variation of `K_C-S K_C` at most
`2*V_C+O(||K_C-S K_C||_infinity)`. Its squared `L2` norm is at most
`L*||K_C-S K_C||_infinity^2`. Apply (1) with
`Omega=exp(pi*C/2)` to obtain

```
q_log[K_C-S K_C]
  =O(C^10*(log C)^2*exp(-pi*C/2)).                  (3)
```

The extra logarithm is a harmless conservative allowance for the
variation term.

For clarity about the prime-defined form, [equations (3.19)–(3.20)
of Connes–Consani–Moscovici](https://arxiv.org/html/2511.22755v1)
split `QW_lambda` into an archimedean Fourier multiplier, two pole
evaluations, and the prime-power correlations. The archimedean
multiplier is bounded in absolute value by an absolute constant times
`log(e+|xi|)`. Cauchy–Schwarz gives `||T(n)||<=2*n^(-1/2)` for the
correlation operator in (3.20), hence

```
sum_(2<=n<=C) Lambda(n)*||T(n)||
  <=4*sqrt(C)*log C.
```

The two pole-evaluation functionals on `I` have norm `O(C^(1/4))`,
so their quadratic contribution has operator norm `O(sqrt C)`.
Consequently there is an absolute `B` such that, for `C>=2`,

```
|QW_lambda(H,H)|
  <= B*q_log[H]+B*sqrt(C)*log(e*C)*||H||_2^2.     (4)
```

The form domain includes these compactly supported BV functions by
(1) and form closure. Combining (2)–(4) yields

```
|QW_lambda(K_C-S K_C,K_C-S K_C)|
  =O(C^10*(log C)^2*exp(-pi*C/2)).                (5)
```

Reflection commutes with `QW_lambda`, so its even and odd components
are form-orthogonal. Equation (5) therefore also bounds the absolute
difference between the Weil energies of `K_C` and `S K_C`. It says
that the candidate's small reflection defect remains small under
the logarithmic Weil form. It says nothing about the parity of the
*true lowest Weil eigenvector*.

## Projecting the even candidate into the finite Weil matrix

Let `T_N=S K_C-P_N S K_C`. The [variation Fourier-tail estimate](PROLATE_FOURIER_DIAGONAL_2026_09_23.md)
gives

```
||T_N||_2^2 <= L*V_C^2/(2*pi^2*N)
             =O(C^8*(log C)^3/N).                    (6)
```

The same coefficient bound shows that each nonconstant cosine mode
of `P_N S K_C` has interval variation at most `(4/pi)*V_C`.
The constant mode has zero interval variation. Its endpoint magnitude
is bounded by `||K_C||_infinity`; the other endpoint contributions
sum to `O(V_C*log(e+N))`. The prolate sup estimate gives
`||K_C||_infinity=O(C^(3/2))`. Thus the whole-line zero extension of
`T_N` has

```
Var_R(T_N)=O((N+1)*C^4*log C).                     (7)
```

Use (1) with `Omega=N^3*C^2`. Equations (6)–(7) yield

```
q_log[T_N]
  =O(C^8*(log C)^3*(log(e+N)+log C)/N).          (8)
```

Then (4) gives

```
|QW_lambda(T_N,T_N)|
  =O(C^(17/2)*(log C)^4*(1+log(e+N)/log C)/N).   (9)
```

In particular, the same polynomial diagonal `N(C)=ceil(C^9)` used
for the candidate's Xi profile satisfies

```
q_log[T_(N(C))]
  +sqrt(C)*log(e*C)*||T_(N(C))||_2^2
    =O(C^(-1/2)*(log C)^4) -> 0.                 (10)
```

This is a quantitative approximation of the **even prolate
candidate** in a shifted Weil-form norm. The faster diagonal
`N(C)=ceil(C^13)` also controls the energy and Rayleigh quotient.
To see this without treating the Weil form as a bounded operator,
define the positive dominating form

```
H_C(H)=B*q_log[H]+B*sqrt(C)*log(e*C)*||H||_2^2,
```

increasing the absolute constant `B` from (4) if necessary.
The Hermitian Weil form satisfies `-H_C<=QW_lambda<=H_C` as
quadratic forms. Its Riesz representative in the `H_C` Hilbert space
is therefore a self-adjoint contraction, so the cross term obeys
Cauchy–Schwarz in that norm. The elementary
prolate sup bound gives `||K_C||_infinity=O(C^(3/2))`; combining this
with `Var_I(K_C)=O(C^4*log C)` in (1), for example with
`Omega=C^6`, gives

```
H_C(S K_C)=O(C^(7/2)*(log C)^3).                 (11)
```

At `N=ceil(C^13)`, equation (9) gives
`H_C(T_N)=O(C^(-9/2)*(log C)^4)`. Hence polarization and (11) give

```
|QW_lambda(S K_C,S K_C)
  -QW_lambda(P_N K_C,P_N K_C)|
    =O(C^(-1/2)*(log C)^4) -> 0.                  (12)
```

The odd component changes the energy by only the exponential
quantity (5), because reflection makes the even and odd components
form-orthogonal. Thus (12) also holds with `K_C` in place of
`S K_C` in its first term.

For the Rayleigh quotient, [Lemma 7.3 of the cited paper](https://arxiv.org/html/2511.22755v1)
and the nonzero Hermite-limit normalization imply
`F_0(K_C)=integral_I K_C(t)dt -> c*Xi(0)!=0` for some fixed
nonzero `c`. Projection preserves this integral exactly, so
`||K_C||_2^2` and `||P_N K_C||_2^2` are both bounded below by
`c_0^2/L` for all sufficiently large `C`. Orthogonality of `P_N`
also gives

```
||K_C||_2^2-||P_N K_C||_2^2
  =||K_C-P_N K_C||_2^2
  =O(C^8*(log C)^3/N)
   +O(C^9*log(C)*exp(-pi*C/2)).                    (13)
```

The numerator energies are `O(C^(7/2)*(log C)^3)` by (5) and
(11). Combining (12)–(13) with the origin lower bound proves

```
Rayleigh_Weil(P_(ceil(C^13)) K_C)
  -Rayleigh_Weil(K_C) -> 0.                        (14)
```

All constants in this paragraph are asymptotic; the published
prolate-to-Hermite `O(lambda^-2)` estimate does not supply a usable
finite-cutoff constant. Equation (14) is a candidate-to-Galerkin
comparison, not a candidate-to-ground comparison. It does not imply
that either Rayleigh quotient is small relative to the Weil gap.

## A gap-aware projection budget

The absolute convergence in (14) is not the rate needed by the
[strip residual gate](STRIP_RESIDUAL_TRANSFER_2026_09_23.md). Here is
the rate obtainable from the bounds above. For `N>=C^9`, write
`D=1+log(e+N)/log C`. Equations (9) and (11), form
Cauchy–Schwarz, and the exponential odd-component bound (5) give

```
|QW(K_C,K_C)-QW(P_N K_C,P_N K_C)|
  =O(C^6*(log C)^(7/2)*sqrt(D/N)
     +C^(17/2)*(log C)^4*D/N
     +C^10*(log C)^2*exp(-pi*C/2)).               (15)
```

The denominator difference in (13) is
`O(C^8*(log C)^3/N+C^9*log C*exp(-pi*C/2))`.
Both squared norms are at least `c_0^2/log C`; the projected energy
is `O(C^(7/2)*(log C)^3)` for `N>=C^9`. Applying
`|a/x-b/y|<=|a-b|/x+|b|*|x-y|/(x*y)` therefore yields

```
|Rayleigh_Weil(P_N K_C)-Rayleigh_Weil(K_C)|
  =O(C^6*(log C)^(9/2)*sqrt(D/N)
     +C^(23/2)*(log C)^8*D/N
     +poly(C,log C)*exp(-pi*C/2)).                (16)
```

The second displayed polynomial term also absorbs the smaller
`C^(17/2)*(log C)^5*D/N` contribution from (15).
The implied constants are not currently effective. Equation (16)
is nevertheless a precise **conditional scale test**: if a continuous
even candidate had Rayleigh quotient at least `m_C>0` below the
continuous second even eigenvalue, then a mode cutoff satisfying

```
C^6*(log C)^(9/2)*sqrt(D/N)=o(m_C),
C^(23/2)*(log C)^8*D/N=o(m_C),
poly(C,log C)*exp(-pi*C/2)=o(m_C)                (17)
```

would preserve the Rayleigh-below-second gate in the finite even
Galerkin space, because its second Ritz eigenvalue is no smaller
than the continuous second even eigenvalue. Ignoring logarithms and
the displayed `D` factor,
the first requirement asks for `N` substantially larger than
`C^12/m_C^2`. If `m_C` is exponentially small, the polynomial
diagonal `N=C^13` does not meet this relative budget. The missing
input is a continuous candidate margin `m_C` and a compatible lower
spectral separation; neither follows from prolate concentration or
inversion symmetry. The cutoff-13 exact candidate fails the finite
gate at modes 4, 8, 12, and 16, but these checks cannot decide the
continuous margin or an increasing-support path. Even if (17) held,
the strip theorem would still need a residual-over-clearance bound;
the Rayleigh estimate alone does not supply it.
Alternatively, the [Rayleigh-excess strip transfer](STRIP_RESIDUAL_TRANSFER_2026_09_23.md)
uses `(mu_N-lambda_(0,N))/(lambda_(1,N)-lambda_(0,N))` instead of
an operator residual. That ratio is compatible with form estimates,
but still needs effective finite eigenvalue bounds. Min-max places
each Ritz eigenvalue above its continuous counterpart; it does **not**
by itself lower-bound the *difference* of the two Ritz eigenvalues.

The need for a *relative* budget is not peculiar to the estimates.
For the exact positive matrices
`A_epsilon=diag(epsilon^2,epsilon,1)` and unit vectors
`w_epsilon=sqrt(1-epsilon^(1/2))*e_0+epsilon^(1/4)*e_2`, the
candidate tends to the ground vector in ordinary norm and its
Rayleigh quotient tends to the ground energy. Yet its Rayleigh excess
is asymptotic to `epsilon^(1/2)`, while the second-eigenvalue gap is
asymptotic to `epsilon`; the excess-to-gap ratio diverges as
`epsilon^(-1/2)`. This is a logical counterexample to promoting
absolute form convergence into the strip theorem's gap condition.

The remaining spectral problem is now more sharply isolated: obtain
a growing-support estimate comparing this form-controlled prolate
vector with the actual Weil ground eigenspace, together with a
uniformly usable spectral gap and the all-support simple-even input.
The cutoff-13 exact prolate candidates fail the finite residual-and-gap
test at modes 4, 8, 12, and 16 by the separate
[error-transfer certificates](exact_prolate_gate_13_4.json), and none
of (1)–(17) changes that fact or proves RH.
