# A finite-Fourier diagonal for the prolate candidate

The [prolate candidate audit](PROLATE_CANDIDATE_GATE_2026_09_23.md)
projects `k_lambda=E(h_lambda)` into the **even** Fourier space of the
finite Weil matrix. At a fixed support the candidate need not be exactly
inversion-even: the numerical reflection defect is not a proof of exact
symmetry. The following estimate handles that distinction and makes
the Fourier truncation error explicit. It does **not** compare the
candidate with the Weil ground state.

## Exact projection identity

Let `C=lambda^2` be an integer, `L=log C`, and `I=[-L/2,L/2]`. Put
`K_C(t)=k_lambda(exp(t))`, where `h_lambda` is extended by zero outside
`[-lambda,lambda]`. For `j>=0`, set `omega_j=2*pi*j/L`,
`b_0=L^(-1/2)` and `b_j=(2/L)^(1/2)` for `j>=1`. The coefficient in
the same orthonormal even basis as the certified Weil matrix is

```
w_j = b_j * sum_(n=1)^C n^(-1/2)
      * integral_(n/lambda)^lambda x^(-1/2) h_lambda(x)
          cos(omega_j*(log(x/n)+L/2)) dx.                    (1)
```

Indeed `k_lambda(u)=u^(1/2) sum_(n<=lambda/u) h_lambda(nu)`;
interchange the finite sum and integral in `t=log u`, then use `x=nu`.
Formula (1) gives a direct route to interval coefficient enclosures
without quadrature across a prime-sum threshold. The existing
`prolate_candidate_diagnostic.py` uses equivalent piecewise quadrature;
its prolate eigenfunctions and coefficients remain floating estimates.

Let `S K(t)=(K(t)+K(-t))/2`, and let `P_N` be the orthogonal projection
onto the constant and the first `N` even cosine modes. Then
`P_N K=P_N S K` exactly. In particular,

```
F_0(P_N K)=F_0(K),
F_z(S K)=[F_z(K)+F_(-z)(K)]/2,
F_z(K)=integral_I K(t) exp(i*z*t) dt.                        (2)
```

The first identity means that Fourier truncation creates **no origin
normalization error**. The second shows why exact inversion symmetry
at a fixed `lambda` is unnecessary for convergence to an even limit.

## A quantitative tail theorem

For any real or complex `K` of bounded variation on `I`, put
`V=Var_I(K)`. The even function `S K` has equal endpoint values, and
`Var_I(S K)<=V`. Integration by parts against the periodic Fourier
modes therefore gives, for the orthonormal even coefficient `w_j`,

```
|w_j| <= sqrt(2*L)*V/(2*pi*j),                 j>=1,
||S K-P_N K||_2 <= sqrt(L)*V/(pi*sqrt(2*N)).    (3)
```

Here the variation includes interior jumps. The second inequality uses
`sum_(j>N) j^(-2) <= 1/N` and Parseval. For `sigma>=0`, Cauchy-Schwarz
gives on the entire horizontal strip `|Im z|<=sigma`

```
||F_z||_(L2(I)^*) <= sqrt(L)*H_sigma(L),
H_sigma(L)=sqrt(sinh(sigma*L)/(sigma*L)),
H_0(L)=1.
```

Combining this with (2) and (3) proves the effective bound

```
sup_(|Im z|<=sigma) |F_z(P_N K)-F_z(S K)|
    <= L*V*H_sigma(L)/(pi*sqrt(2*N)).                     (4)
```

If `F_0(K)!=0`, the same right side divided by `|F_0(K)|` bounds the
difference of the **origin-normalized** profiles, with no additional
denominator-loss factor. For any tolerance `epsilon>0`, it suffices to
take

```
N >= L^2*V^2*H_sigma(L)^2
     / (2*pi^2*epsilon^2*|F_0(K)|^2).                     (5)
```

This is an upper bound on the modes needed for a prescribed strip
profile error once a rigorous variation upper bound and an origin
lower bound are supplied. It is not a claim that the current floating
prolate solve supplies either bound.

For the actual compactly supported prolate input, write
`M_0=sup_[0,lambda]|h_lambda|` and
`M_1=sup_[0,lambda]|x*h_lambda'(x)|`. Between its finitely many
thresholds `t_n=log(lambda/n)`, each summand in `K_C(t)` has derivative
`exp(t/2)*(h_lambda(x)/2+x*h_lambda'(x))`, where `x=n*exp(t)`.
At a threshold its jump has magnitude
`exp(t_n/2)*|h_lambda(lambda)|`. Summing the continuous variation and
all jumps gives the conservative but explicit estimate

```
Var_I(K_C) <= C*sqrt(lambda)
              * [L*(M_0/2+M_1)+|h_lambda(lambda)|].       (6)
```

The right side is finite for every fixed prolate eigenfunction. More
effective estimates would make (5) practical, but (6) can already be
bounded using only an elementary prolate eigenvalue estimate. In the
scaled coordinate `z=x/lambda`, put `c=2*pi*C` and let `H_0,H_4` be
orthonormal even eigenfunctions of

```
P_c H = -d/dz[(1-z^2)H']+c^2*z^2*H,
```

corresponding to the first and third even eigenvalues. Min-max on the
span of the normalized Legendre polynomials of degrees `0,2,4` gives
`chi_4<=20+c^2`: the derivative part has eigenvalues `0,6,20` there,
and multiplication by `c^2*z^2` is bounded above by `c^2`.
Set `T=20+2*c^2`, so `chi_j+c^2<=T` for `j=0,4`.

The regular endpoint condition gives `[(1-z^2)H_j']_(z=1)=0`.
Integrating the differential equation from `z` to `1` yields, for
`0<=z<1`, `|H_j'(z)|<=T*||H_j||_infinity/(1+z)`; integrate from
`-1` for negative `z`. Thus `||H_j'||_infinity<=T||H_j||_infinity`.
A function with maximum magnitude `M` and Lipschitz constant at most
`T*M` has magnitude at least `M/2` on a one-sided interval of length
`1/(2*T)`. Its squared integral over `[-1,1]` is at least
`M^2/(8*T)`. Consequently

```
||H_j||_infinity <= sqrt(8*T)*||H_j||_2.
```

For any linear combination `h_lambda(lambda*z)=a*H_0(z)+b*H_4(z)`, let
`R=sqrt(|a|^2+|b|^2)`. Cauchy-Schwarz on the two coefficients gives

```
M_0 <= 4*sqrt(T)*R,
M_1 <= 4*T^(3/2)*R,
Var_I(K_C) <= 4*C*sqrt(lambda)*sqrt(T)*R
              * [L*(T+1/2)+1].                            (7)
```

These are explicit, intentionally coarse estimates; `R/|F_0(K_C)|`
is scale invariant and can be inserted into (5). They show that the
Fourier-mode cutoff can be chosen effectively from a nonzero origin
bound, without assuming an unproved derivative estimate for the exact
prolate eigenfunctions.

## Consequence and remaining gate

[Connes–Consani–Moscovici, Lemma 7.3](https://arxiv.org/html/2511.22755v1)
establishes, with a suitable scalar normalization of `h_lambda`, that
`F_z(K_C)` converges to Xi uniformly on closed substrips of
`|Im z|<1/2`. Xi is even and `Xi(0)!=0`. By (2), `F_z(S K_C)` has the
same limit. For any sequence `C -> infinity`, choose `N(C)` satisfying
(5) with an error tending to zero on an expanding sequence of closed
substrips. Then the **finite even Fourier projections in the Weil
matrix spaces** have origin-normalized profiles converging locally
uniformly to `Xi(z)/Xi(0)`.

In fact a single explicit polynomial diagonal suffices. The paper's
Lemma 7.2 gives `||h_lambda-h||_infinity=O(lambda^(-2))` on
`[-lambda,lambda]`, where `h` is a fixed Gaussian times a polynomial.
Therefore `||h_lambda||_(L2(-lambda,lambda))=O(1)` and, in the scaled
coordinate of (7), `R=O(lambda^(-1/2))=O(C^(-1/4))`.
Since `T=20+8*pi^2*C^2=O(C^2)`, equation (7) yields

```
Var_I(K_C)=O(C^4*log C).                               (8)
```

For `N(C)=ceil(C^9)`, use `H_sigma(L)<=C^(sigma/2)` in (4) to get,
for every fixed `0<=sigma<1/2`,

```
sup_(|Im z|<=sigma) |F_z(P_(N(C)) K_C)-F_z(S K_C)|
    = O(C^(sigma/2-1/2)*(log C)^2) -> 0.             (9)
```

The implied constant may depend on `sigma` and the normalization in
Lemma 7.2, but the exponent `9` is explicit and independent of `sigma`.
Because the zeroth Fourier mode is preserved, (9) also applies after
origin normalization for sufficiently large `C`.

This removes Fourier truncation, including possible finite-support
reflection asymmetry, as a logical obstacle to constructing a diagonal
family of *candidate profiles*. The subsequent
[Weil-form projection budget](PROLATE_WEIL_FORM_PROJECTION_2026_09_23.md)
uses the leakage estimate and logarithmic form symbol to make the
candidate projection error small in the Weil form norm along this
same diagonal, and its Rayleigh difference small along `N(C)=ceil(C^13)`.
Neither result supplies a residual-over-gap estimate. The hard step
remains to show that the corresponding Weil ground-state profiles
follow a suitable diagonal. The finite cutoff-13 candidates fail the
raw residual-and-gap gate, and no uniform simple-even theorem or
prolate-to-Weil profile transfer has been proved. RH remains open.
