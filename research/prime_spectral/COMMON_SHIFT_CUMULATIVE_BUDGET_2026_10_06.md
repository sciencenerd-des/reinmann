# Two telescoping energies and a conditional cumulative rank budget

This note derives an absolute cumulative profile estimate on compact sets
at a **common spectral parameter**. It supplies a different sufficient
interface from summing the earlier single-step square-root bounds. Its
energy hypotheses and the ground-parameter transfer are not proved for
the unbounded Weil family. The finite common-shift test is markedly worse
than the paired-step test. Neither this note nor its certificate proves RH.

## 1. A positive Gram increment, with both sources retained

Fix support length L and spectral parameter nu. Let H_N be the first N
noncentral even Fourier modes, and let T_N be nested principal restrictions
of one real symmetric form T=C-nu I. Assume every T_N is positive definite.
Let b_N and f_N(z) be restrictions of common source vectors, with f(z)
holomorphic in z. Define

```
u_N=T_N^-1 b_N,
g_N(z)=T_N^-1 f_N(z),
P_N(nu,z)=f_0(z)-f_N(z)^T u_N,
E_N=b_N^* T_N^-1 b_N,
D_N(z)=f_N(z)^* T_N^-1 f_N(z).
```

The source b is real; f may be complex. The transpose in the holomorphic
profile and the conjugate transpose in the positive dual energy are distinct.
All embeddings below extend smaller vectors by zero.
Galerkin orthogonality gives, for M>N,

```
du=u_M-u_N,       dg(z)=g_M(z)-g_N(z),
du and dg(z) are T-orthogonal to H_N,
||du||_T^2=E_M-E_N,
||dg(z)||_T^2=D_M(z)-D_N(z),
P_M(nu,z)-P_N(nu,z)=-<du,T dg(z)>.                    (1)
```

For example, the first orthogonality follows by testing both equations
against x in H_N: `<x,T u_M>=<x,b_M>=<x,b_N>=<x,T u_N>`.
Expanding the two energies, the cross terms vanish. The profile identity
follows by expanding `<u_M,T g_M>-<u_N,T g_N>` and eliminating both
mixed terms. Since du is real, the remaining pairing is holomorphic.

More generally, for any finite collection of common sources S_N,

```
G_N=S_N^* T_N^-1 S_N,
G_M-G_N is positive semidefinite.                      (2)
```

An independent exact factorization is obtained by writing
`T_M=[[T_N,B],[B^*,F]]`. Its Schur complement
`D=F-B^* T_N^-1 B` is positive, and

```
S_eff=S_new-B^* T_N^-1 S_old,
G_M-G_N=S_eff^* D^-1 S_eff.                            (3)
```

Equation (3) proves (2) even when an increment is singular or zero.
No simple-eigenvalue assumption is needed for these mathematical identities.
The current numerical implementation uses certified simple spectral
enclosures as one way of evaluating positive inverses.

## 2. A genuinely cumulative estimate

For any increasing rank chain N_0<...<N_J, set
`Delta E_j=E_(N_(j+1))-E_(N_j)` and similarly Delta D_j(z).
From (1), then Cauchy–Schwarz over the rank index,

```
sum_(j=a)^(J-1) |Delta P_j(nu,z)|
 <= sum_j sqrt(Delta E_j*Delta D_j(z))
 <= sqrt[(E_(N_J)-E_(N_a))*(D_(N_J)(z)-D_(N_a)(z))].    (4)
```

The **dual increment**, rather than the whole dual energy, is paired
with each primal increment. Both factors telescope. This is the crucial
distinction from a one-energy square-summability argument.

There is also an absolute budget for the sum of compact uniform norms.
Let K be compact and choose a bounded open set Omega and r>0 so that
every radius-r disk centered in K lies in Omega. The finite vector-valued
function dg_j(z) is holomorphic; its squared T norm is subharmonic.
The disk mean-value inequality therefore gives

```
sup_(z in K) ||dg_j(z)||_T^2
 <= (1/(pi*r^2))*integral_Omega ||dg_j(z)||_T^2 dA(z).
```

Apply this to (1), then apply Cauchy–Schwarz over j and telescope:

```
sum_(j=a)^(J-1) ||Delta P_j(nu,.)||_K
 <= sqrt[(E_(N_J)-E_(N_a))/(pi*r^2)
          *integral_Omega (D_(N_J)(z)-D_(N_a)(z)) dA(z)]. (5)
```

Consequently the following are sufficient for an infinite cumulative
budget at this fixed support and parameter:

```
sup_N E_N=E_infinity<infinity,
sup_N integral_Omega D_N(z) dA(z)=D_Omega,infinity<infinity. (6)
```

The tail of the absolute compact-norm sum is bounded by
`sqrt[(E_infinity-E_(N_a))*D_Omega,infinity/(pi*r^2)]`, which tends to
zero. This proves absolute convergence in the compact uniform norm,
including for the chain of **every integer rank**. It does not require
the separate series `sum sqrt(Delta E_j)` to converge. Positivity permits
Tonelli and passage to the increasing-rank limit.

No all-rank estimate in (6) is supplied by the finite certificate below.
For a growing-support path, the support dependence of E, D, Omega and
the spectral parameter must also be controlled. Fixed-support absolute
convergence alone does not identify Xi.

### What these energy hypotheses mean for the infinite fixed-support operator

The primal bound has a direct simplification. If nu is no greater than
every even Ritz minimum lambda_N, then `A_N-nu I` is nonnegative. When
T_N is positive, its scalar Schur complement gives

```
0<=E_N=b_N^* T_N^-1 b_N<=a-nu.
```

Thus the primal energy is automatically bounded at such a common shift.
The integrated dual bound is the substantive missing input.

It cannot secretly bypass the origin-constrained gap at fixed support.
Suppose the infinite constrained form T is nonnegative, has compact
resolvent, and the nested Fourier spaces form a core. These are the
fixed-support framework properties established by the logarithmic
diagonal plus bounded perturbation; nonnegativity here requires choosing
nu at or below the limiting even ground eigenvalue.
For any bounded nonempty open Omega, the following are equivalent:

```
T>=kappa I for some kappa>0,
sup_N integral_Omega D_N(z) dA(z)<infinity.             (6a)
```

The forward implication follows from `D_N(z)<=||f_N(z)||^2/kappa`
and the uniform Fourier-functional bound on bounded Omega.
For the converse, if the gap vanishes, compact resolvent and positivity
give a nonzero vector h with Th=0. Take core approximants x_N with
`||x_N-h||_form->0`, so `q_T(x_N)->0`. The inverse variational principle
implies

```
integral_Omega D_N(z) dA(z)
 >=integral_Omega |f_N(z)^T x_N|^2 dA(z)/q_T(x_N).
```

The numerator tends to the integral of the squared Fourier transform
of h. That transform is entire and is not identically zero, by
injectivity of the Fourier transform of a compactly supported L2
function. Its integral over a nonempty open set is therefore positive.
The denominator tends to zero. If an approximant has zero energy
already, strict positivity of the finite T_N has failed. Otherwise
the displayed bound diverges, contradicting the integrated dual bound.

At nu equal to the infinite even ground eigenvalue, a positive
constrained gap in turn is equivalent to a simple even ground with
nonzero origin coordinate. A gap excludes any ground vector with zero
origin; two independent ground vectors would have a linear combination
with zero origin. Conversely, for a simple unit even ground u and
next-even gap Delta>0, every unit vector x with zero origin satisfies
`|<u,x>|^2<=1-|u_0|^2`, so

```
<x,(A-lambda_0 I)x> >=Delta*|u_0|^2 >0.                (6b)
```

Thus the two-energy theorem is a useful cumulative transfer once its
input is proved. In this framework it also gives an exact diagnostic
of that input; it does not prove simple-even origin control by changing
the name of the gap assumption. Odd/even separation and the spatial
boundary remain separate requirements.

## 3. Transfer to the actual changing ground parameter

The ground profile uses nu=lambda_N at each rank; (4)–(6) require the
same nu. That mismatch cannot be omitted. Here is an explicit sufficient
ground Cauchy estimate at fixed support.

Assume the rank-N and rank-M ground vectors are simple and have nonzero
Fourier origin. Let delta=lambda_N-lambda_M>=0. Assume the constrained
ground blocks, hence the intervening old-rank spectral window, have a
common lower bound kappa>0. Assume all origin coupling vectors have
norm at most B. Set nu=lambda_M.

The scalar secular function
`s_N(t)=a-t-b_N^* (C_N-t I)^-1 b_N` satisfies
`s_N'(t)=-1-||(C_N-t I)^-1 b_N||^2`.
Since `s_N(lambda_N)=s_M(lambda_M)=0`,

```
E_M(nu)-E_N(nu)=s_N(lambda_M)
 <=delta*(1+B^2/kappa^2).                              (7)
```

Moreover `D_M(z)-D_N(z)<=D_M(z)<=W_sigma(L)^2/kappa`
on the entire closed strip `|Im z|<=sigma`, where
`W_sigma(L)=sqrt[sinh(sigma L)/(sigma L)]` and W_0=1.
The resolvent identity bounds the old-ground shift by

```
||u_N(lambda_N)-u_N(lambda_M)|| <=delta*B/kappa^2.
```

Combining with (4) for the endpoint pair gives

```
sup_(|Im z|<=sigma) |P_M(lambda_M,z)-P_N(lambda_N,z)|
 <=W_sigma(L)*[sqrt(delta*(1+B^2/kappa^2)/kappa)
                +delta*B/kappa^2].                    (8)
```

If kappa is uniform over every rank at this fixed support, semiboundedness
and nested minimization make lambda_N converge. Thus delta tends to zero
uniformly over all M>=N as N tends to infinity, and (8) proves a ground-profile
Cauchy property on the strip. An effective rate also needs a tight lower
enclosure of the limiting eigenvalue; a crude semiboundedness constant
does not give that rate. Equation (8) is a Cauchy estimate, not by itself
an absolute-variation budget for the changing ground parameters.

One input to (8) is already effective on 17<=C<=19. From the
[rank-independent displacement bound](WEIL_INFINITE_RANK_TAIL_2026_10_06.md),
`|b_j^(disp)|<3.157010` and the even origin coupling is
`b_j^(origin)=sqrt(2)*b_j^(disp)/j`. Hence, at **every rank**,

```
||b^(origin)||^2 <=2*B_disp^2*sum_(j>=1) 1/j^2
                =pi^2*B_disp^2/3,
||b^(origin)|| <5.726184.                              (9)
```

The remaining constrained gap kappa has **not** been proved uniformly
in rank. The previous finite-count theorem bounds how many dangerous
modes exist; it does not make their eigenvalues uniformly positive.
These claims include the input cell's endpoints, but do not bound a
path through increasing prime-support cells.

## 4. Boundary evaluation is an actual obstruction to this generic budget

Fourier evaluation at z is a bounded L2 functional on a fixed support.
Spatial boundary evaluation is different. On the noncentral even space,
its unscaled coefficient vector is `beta_N=sqrt(2)*(1,...,1)`.
Take the even Dirichlet vector with coefficients `1/sqrt(N)` in modes
1 through N and zero origin coordinate. It has norm one and
`|beta_N^* d_N|^2=2N`.

The fixed-support logarithmic Weil form has
`<d_N,T_N d_N><=c_L*log(e+N)` for sufficiently large N, by its
[logarithmic form norm and bounded perturbation estimates](FIXED_SUPPORT_FORM_CORE_2026_09_23.md).
For positive T_N, the inverse variational principle gives

```
beta_N^* T_N^-1 beta_N
 =sup_(x!=0) |beta_N^* x|^2/<x,T_N x>
 >=2N/[c_L*log(e+N)] -> infinity.                      (10)
```

Thus replacing the Fourier dual by the generic boundary dual violates
the bounded-energy hypothesis. This theorem cannot supply uniform
boundary control through an arbitrary inverse estimate. Boundary control
must use the specific eigenvector/source cancellations or the exact
displacement/parity rigidity argument. The required all-rank parity
separation and eigenfunction boundary control remain open.

## 5. Finite test: the joint bound loses rank alignment

The [generator](../../experiments/prime_spectral/common_shift_rank_budget.py)
uses the same saved rank-12 matrix for every principal block at cutoff 13,
with common nu equal to its certified lowest eigenvalue. All three
constrained blocks at ranks 4, 8 and 12 pass positive spectral isolation.
The source Gram matrices are evaluated at 1024 bits; old matrix inputs,
source hashes, nesting and energy telescoping are checked.

| Fourier point | Paired-step Cauchy sum upper | Joint telescoped Cauchy upper | Signed cumulative common-shift change, approximate |
|---|---:|---:|---:|
| 4 | <28.90494 | <33064.773 | 0.1731473 |
| 8 | <24.57849 | <34218.969 | 0.1259533 |
| i | <3.029265 | <3243.823 | -0.01921565 |

The joint bound is over 1,000 times worse than the paired-step bound
at all three points. Most primal energy enters in the first step, while
most dual energy enters later. A single product of total energies loses
that rank alignment. The exact theorem is valid; its crude numerical
consequence is inadequate here. The small signed sum is not a certified
all-rank tail estimate, and the older common-shift profiles are not the
older ground profiles.

The [certificate](common_shift_rank_budget_13_4_8_12.json) saves this
negative diagnostic without relabeling it as a ground convergence proof.
Tests include exact signed cancellation with positive incremental
energies, an independent nondiagonal direct inverse, zero sources,
invalid gates, finite data replay, and (8) applied to actual ground
vectors of synthetic nested matrices with a verified finite gap.

The next useful estimate is a uniform, cancellation-sensitive control
of the integrated dual energy or its deflated counterpart, together with
the ground-parameter and boundary gates. Uniform theta curvature, the
interior all-rank RH budget and Xi identification remain unproved.
The new mathematical statements are written proofs, not Lean formalizations.
