# A proved leading-model sign, a coupled transfer criterion, and a false shortcut

## Outcome of this proof attempt

This note proves an unbounded curvature theorem for the **leading Lambert
model**, and gives an exact derivative criterion for transferring its sign to
the true moments. It also proves that real-zero structure and double-Turan
inequalities do not imply the repository's normalized-deficit concavity.

It does **not** prove uniform sign control for the degree-16 integral model,
the true Xi deficit, or the uniform interior rank budget. Those claims must
not be inferred from the theorem below. The leading model is a simpler,
explicit reference function; replacing the degree-16 model by it does not
remove the need for an error theorem. No claim of priority or novelty in the
literature is made for these elementary deductions.

## 1. Unbounded leading-model theorem

For x>0 let

    w = W(2x/pi),
    a = 2w/(1+w), H0 = a/x,
    f0(x) = log((x+1)(1-exp(-H0(x)))),
    Q(x) = (w^2+4w+1)/(x^2(1+w)^4).

**Theorem.** For every real x>=256,

    f0''(x) <= -0.822 Q(x) < 0.

The implementation saves a slightly stronger exact rational margin, rather
than using the decimal in this statement.

### Proof

Define

    g(h) = log(integral_0^1 exp(-h t) dt)
         = log((1-exp(-h))/h), h>0.

Normalize exp(-h t) on [0,1] to a probability density. Differentiating this
finite integral yields

    g'(h) = -E_h[t] <= 0,
    g''(h) = Var_h(t) <= 1/4.

For completeness, t^2<=t on [0,1] gives Var(t)<=m-m^2<=1/4, where m=E[t].
No unproved concavity claim about the theta kernel enters this argument.

The decomposition

    f0 = log(a) + log(1+1/x) + g(H0)

is exact. Differentiating w exp(w)=2x/pi gives w'=w/[x(1+w)], and direct
algebra then gives

    (log a)'' = -Q,
    H0' = -2w^2(w+2)/(x^2(1+w)^3),
    H0'' = 2w^3(2w^2+8w+9)/(x^3(1+w)^5) > 0.

Since w^2(w+2)<(1+w)^3, |H0'|<=2/x^2. Consequently

    f0'' = -Q + (2x+1)/(x^2(x+1)^2)
                 + g''(H0)(H0')^2 + g'(H0)H0''
          <= -Q + 2/x^3 + 1/x^4.

The last term involving H0'' is nonpositive. Also

    Q >= 1/[x^2(1+w)^2],
    (2/x^3+1/x^4)/Q <= (2/x+1/x^2)(1+w)^2 = B(x).

Both terms of B decrease with w, hence with x. Indeed x=(pi/2)w exp(w), and

    d/dw log((1+w)^2/(w exp(w)))
       = 2/(1+w)-1/w-1 = -(w^2+1)/(w(1+w)) < 0,
    d/dw log((1+w)^2/(w^2 exp(2w)))
       = 2/(1+w)-2/w-2 < 0.

FLINT evaluates B(256)<0.178 with outward rational bounds. Thus
B(x)<0.178 for every x>=256, giving f0''<=-0.822Q. This is a finite evaluation
of the endpoint of an analytically proved monotone bound, not extrapolation
from a sample grid. The saved certificate includes the exact rational upper
bound for B(256) and lower bound for 1-B(256). QED.

The new theorem is about f0, not the curvature expression formed from the
three degree-16 model-moment triples. They have not been identified.

## 2. An exact coupled transfer criterion

Suppose the true ratio q is positive and write H=-log q. If H>0, set

    r = H/H0 - 1,
    f = log((x+1)(1-q)).

For C^2 functions with H>0 the identity

    f = log(a) + log(1+1/x) + log(1+r) + g(H)

gives the rigorous one-sided estimate

    f'' <= -Q + 2/x^3 + |r''|/(1+r)
                    + (H')^2/4 + max(-H'',0).

We dropped the nonpositive term -(r')^2/(1+r)^2 and used -1<=g'<=0.
This estimate retains cancellations before bounding errors. In particular:

**Conditional transfer theorem.** On an interval contained in [256,infinity),
if H>0, |r|<=1/2, |r''|<=Q/8, |H'|<=2/x^2 and H''>=0 throughout the
interval, then

    f'' <= -(0.822-1/4)Q = -0.572Q < 0.

**Proof.** The preceding estimate is at most
-Q+2/x^3+1/x^4+2|r''|, and section 1 bounds the middle two terms by 0.178Q.
All hypotheses are interval hypotheses, not statements at selected points. QED.

This reduces the continuous curvature problem to specific estimates for H
and its relative second derivative. Those estimates are **not established
for Xi by the current moment error files**. The conditional theorem must not
be presented as an unconditional Xi theorem.

### How to preserve neighboring-parameter cancellation

Let K(x)=log I(x), where I is the true theta moment integral, and let

    c(x) = 2x(2x-1)/((2x+2)(2x+1)),
    H(x) = -log c(x) - [K(x-1)-2K(x)+K(x+1)].

For any C^2 function R,

    R(x-1)-2R(x)+R(x+1)
      = integral_{-1}^1 (1-|s|) R''(x+s) ds.

This follows by integrating twice, or by applying the fundamental theorem
of calculus on each half-interval. The tent kernel is nonnegative and has
integral 1. Thus, if K=S+R with R of class C^4, the errors in H,H',H'' are
bounded respectively by

    sup_[x-1,x+1] |R''|,
    sup_[x-1,x+1] |R'''|,
    sup_[x-1,x+1] |R''''|.

Large constant and linear errors cancel identically. Independent pointwise
error bounds lose that fact. But no derivative bounds on R follow merely
from a small bound on |R|: an arbitrarily small oscillatory remainder can
have large derivatives. Nor do the separate degree-16 moment models become
derivatives of one common S automatically. Constructing that common smooth
expansion with certified residual derivatives is the unresolved next step.

## 3. Exact counterexample to a literature shortcut

Consider the entire function

    F(z)=(1+z) exp(z), mu_n=(n+1)/n!, gamma_n=n!mu_n=n+1.

Its only zero is -1. It is also a compact-uniform limit of the polynomials
(1+z)(1+z/N)^N, all of whose zeros are negative real. Its coefficient sequence
is PF-infinity: the finite-product coefficient sequences have totally
nonnegative Toeplitz matrices by repeated multiplication of nonnegative
bidiagonal Toeplitz matrices and Cauchy-Binet; each finite minor passes to the
coefficientwise limit. This conclusion uses only finite determinants and limits.

For every integer n>=1,

    T_n = gamma_n^2-gamma_(n-1)gamma_(n+1) = 1,
    T_n^2-T_(n-1)T_(n+1) = 0, n>=2.

Thus ordinary and double-Turan inequalities hold. But the normalized deficit is

    epsilon(x) = 1 + x/(x+1)^2 = (x^2+3x+1)/(x+1)^2.

Its continuous logarithmic curvature is

    (log epsilon)'' = (2x^3+x^2-8x-5)
                     /[(x+1)^2(x^2+3x+1)^2] > 0, x>=3.

Writing x=y+3 makes the numerator
2y^3+19y^2+52y+34, which is strictly positive for y>=0. Discretely,

    epsilon(x)^2-epsilon(x-1)epsilon(x+1)
      = -(2x^5+5x^4-6x^3-25x^2-20x-5)
          /[x^2(x+1)^4(x+2)^2] < 0, x>=3.

After x=y+3 the numerator before the minus sign is
2y^5+35y^4+234y^3+731y^2+1018y+439. At x=3 the slack is exactly -439/57600.
Therefore even complete real-zero information does not, by itself, imply
this stronger normalized-deficit property. This is not a counterexample
for Xi: it rules out a general-purpose implication we might otherwise misuse.

The normalized rank-two quantity can still be log-concave: here
A2(x)=gamma(x)^2 epsilon(x)=x^2+3x+1. This illustrates why failure of the
sufficient epsilon condition does not contradict total positivity.

## 4. Literature checked and what it supplies

- [Csordas and Dimitrov, Conjectures and Theorems in the Theory of Entire Functions](https://www.dcce.ibilce.unesp.br/~dimitrov/papers/varga.pdf)
  studies double-Turan inequalities and sufficient kernel concavity hypotheses.
  Its coefficient Turan difference T_n is not this repository's epsilon_n.
- [Planat and Sole, Second-Level Concavity of the Riemann Xi Kernel, arXiv v1, August 2026](https://arxiv.org/html/2608.19160v1)
  claims a proof of log-concavity of s'^2-ss'', for s(t)=Phi(sqrt(t)), with
  double-Turan consequences. This is a recent preprint; its supplied certificates
  were not independently replayed here. It is neither an imported premise nor
  a proof of the normalized-deficit or all-rank claims in this repository.
- [O'Sullivan, Zeros of Jensen polynomials and asymptotics for the Riemann xi function](https://arxiv.org/html/2007.13582v2)
  supplies arbitrary-order asymptotic expansions and a generalized Laplace
  integral theorem. An asymptotic error statement is not differentiated here
  without an independently justified derivative remainder estimate.

## 5. Verification and exact completion boundary

`Reinmann/CurvatureControls.lean` verifies five algebraic lemmas: the constant
Turan difference, the explicit failure at center 3, the two shifted polynomial
positivity facts, and the final scalar error-budget sign deduction. It does
not formalize the calculus, the entire-function classification, or the Xi
transfer hypotheses. All five lemmas report only the standard Lean axioms.

`lambert_curvature.py` saves the rational endpoint bound and exact counterexample
values. Tests compare the leading-model theorem with direct derivatives and
check the tent identity on a polynomial with large affine terms. Such tests
check implementation consistency; the proof of the unbounded claim is in
section 1.

Replay:

```sh
lake build Reinmann.CurvatureControls
uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/lambert_curvature.py --output research/certified_xi/lambert_curvature.json
uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/certified_xi -p 'test_*.py'
```

Completed: uniform sign of the explicit leading model, a proved conditional
coupled transfer, and an exact nonimplication control. Unfinished: the Xi
residual derivative bounds, uniform degree-16 model sign, the compact bridge,
and the uniform interior cumulative rank budget. The existing shift-one boundary
certificate is unaffected. The requested RH-scale proof has not been obtained.

Validation completed: 53 certified-Xi tests passed; the new Lean module built
and printed only standard axioms for its five lemmas; saved source hashes,
the numerical endpoint margin and control signs were checked; `git diff --check`
passed. The rest of the Lean library was not rebuilt in this continuation.
