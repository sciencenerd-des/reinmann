# A cross-form sign obstruction to Weil semigroup positivity

The small-support simple-even theorem of
[Suzuki, Theorem 1.4](https://arxiv.org/html/2606.09096v2)
uses positivity improvement for a limiting small-support operator.
The **full** semilocal Weil operator cannot have a positivity-preserving
heat semigroup at the larger supports used by the prime-defined
experiments. The obstruction is an explicit pair of disjoint
nonnegative test functions, derived from the exact local Weil form.
It rules out a direct global Perron–Frobenius extension of that
particular strategy; it does not rule out simple-even ground states
by another argument.

## Exact cross-form calculation

Write the log-support interval as `I=(-a,a)` with `a>1/2`, so the
prime-power cutoff is `C=exp(2a)>e`. Choose a nonzero nonnegative
`eta in C_c^infinity(-1,1)` and, for sufficiently small `epsilon>0`,
put

```
f(t)=eta((t+1/2)/epsilon),
g(t)=eta((t-1/2)/epsilon).
```

Their supports are disjoint and lie inside `I`. Their positive-shift
correlation `q(f,g)(r)` is nonnegative, nonzero, and supported in
`(1-2epsilon,1+2epsilon)`; `q(f,g)(0)=0`. Because
`log 2 < 1 < log 3`, choose `epsilon` small enough that this support
contains no `log n` for any integer `n>=2`. Every prime-power term
in the cross form then vanishes exactly.

The [Connes–Consani–Moscovici formulas (3.13)–(3.18)](https://arxiv.org/html/2511.22755v1)
give, when `q(0)=0` and the prime samples vanish,

```
QW_a(f,g)=integral_0^infinity K(r) q(f,g)(r) dr,
K(r)=exp(r/2)+exp(-r/2)
     -exp(r/2)/(exp(r)-exp(-r)).                    (1)
```

At `r=1`, `exp(r)-exp(-r)>1`, so `K(1)>exp(-1/2)>0`.
Continuity makes `K` strictly positive on the chosen correlation
support after reducing `epsilon` if needed. Hence

```
QW_a(f,g)>0,  f>=0, g>=0, f(t)g(t)=0 for all t.  (2)
```

This is an exact sign conclusion for every `a>1/2`, independent of
RH, numerical eigenvalues, or a fitted Xi profile. In particular it
applies to each integer prime-power cutoff `C>=3` in the experiments.

## Consequence for the heat semigroup

Let `A_a` be the lower-bounded self-adjoint operator associated with
the closed Weil form. The smooth compactly supported `f,g` above lie
in its form domain. If `exp(-t A_a)` preserved pointwise nonnegativity
for every `t>=0`, then `f,g>=0` and `<f,g>=0` would imply
`<exp(-t A_a)f,g> >=0`, with value zero at `t=0`.
The spectral theorem gives the right derivative for form-domain
vectors, so

```
0 <= d/dt|_(t=0+) <exp(-t A_a)f,g>
   = -<A_a f,g> = -QW_a(f,g),
```

contradicting (2). Thus the semigroup is **not** positivity preserving
for `a>1/2`; a fortiori it is not positivity improving there.

This does not contradict Suzuki's theorem: its positivity-improving
form is a limiting small-support operator, and the theorem asserts
simple-even ground states only for sufficiently small `a`. Finite
positive spatial kernels at cutoff 13 or higher also do not imply
positivity preservation of the entire heat semigroup.

The remaining large-support simple-even gate needs a different
mechanism, such as a ground-state-specific comparison or a spectral
inequality that allows positive disjoint cross terms. The prolate
approximation, joint support-mode convergence, and RH remain open.
