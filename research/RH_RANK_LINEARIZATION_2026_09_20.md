# Correlated error amplification in the exact repeated-root control

Follow-up: the [forced-mode Green budget](RH_RANK_GREEN_BUDGET_2026_09_20.md)
derives an exact cancellation condition and a uniform bound when the
forcing satisfies it. This supplies a conditional way to remove the
growing modes, without asserting those conditions for Xi.

## Result and scope

The rectangular-width obstruction does not disappear merely by assuming
that errors are smooth or even constant across shifts. In the exact
control E_N(z)=(1+z/N)^N, a constant initial curvature perturbation has
linearized response

    e_r(m)=r(r+N)/(N+1), 1<=m<=N-1, r>=0.            (1)

This is the derivative of actual determinant curvatures under a positive
coefficient deformation, not just a formal solution of an unrelated
recurrence. The response grows quadratically despite exact neighboring
cancellation. More generally the full linearized system has spatial
modes with eigenvalues n(n-1), 2<=n<=N, and radial responses that are
polynomials of degree n. There is no rank-independent local Lipschitz
bound for this control's initial-data-to-curvature map.

These are statements about a solvable control, not estimates for Xi.
They do not imply a finite perturbation follows its derivative at all
ranks, or that Xi has these modes. They show which amplification a
recurrence-only stability argument must handle or explicitly exclude.

## 1. Linearization with both boundaries retained

The proved repeated-root formulas give, for 1<=m<=N-1,

    f_r(m)=log(1+r/(N-m)),
    Phi_(r,m)(x)=log[1+(m/r)(1-exp(-x))].

The unperturbed recurrence is

    Delta_r^2 f_r(m)=2Phi_(r,m)(f_r(m))
                     -Phi_(r,m-1)(f_r(m-1))
                     -Phi_(r,m+1)(f_r(m+1)).

At shift zero the flux Phi is zero. At shift N, t_r(N)=0 and its flux
is log(1+N/r). These fluxes stay fixed for a degree-N coefficient
perturbation with positive leading coefficient, so their derivatives
are zero. We never differentiate an infinite value delta_r(N).

For an infinitesimal error e, differentiation at the control gives

    Phi'_(r,m)(f_r(m))=m(N-m)/[r(r+N)],
    Delta_r^2 e_r=L_N e_r/[r(r+N)], r>=1,             (2)

where on the N-1 interior shifts

    (L_N p)(m)=2m(N-m)p(m)
       -(m-1)(N-m+1)p(m-1)
       -(m+1)(N-m-1)p(m+1).                         (3)

The boundary weights vanish at 0 and N, so no unspecified boundary
error occurs in (3). The rank-zero curvature has derivative e_0=0.

## 2. Complete spatial modes by elementary polynomial algebra

Put w(m)=m(N-m). For a polynomial p of degree d, (3) is exactly

    L_N p=-Delta_m^2(w*p).

If p is monic, w*p has leading term -m^(d+2). Its negative second
difference has degree d and leading coefficient (d+1)(d+2). Thus L_N
preserves each polynomial space of degree at most d and has diagonal
entries (d+1)(d+2) in the monomial basis. These entries are distinct
for d=0,...,N-2. Back substitution therefore constructs a unique
monic eigenpolynomial p_d of degree d with

    L_N p_d=(d+1)(d+2)p_d.                           (4)

Evaluation on 1,...,N-1 is an isomorphism from polynomials of degree
at most N-2 to all vectors on these shifts. Consequently (4) supplies
the complete spectrum, not a selected finite subset of modes.

These angular polynomials are, up to normalization and m=x+1,
Hahn polynomials Q_d(x;1,1,N-2). Substitution into the established
[Hahn difference equation, DLMF 18.22.10–11](https://dlmf.nist.gov/18.22#E10)
gives L_N=2I+the Hahn operator and eigenvalue 2+d(d+3).
The elementary triangular proof above is self-contained; no novelty
claim is made for this classical spectrum. The N=2 case is the
one-dimensional constant mode directly.

## 3. Exact radial polynomials

For order n=d+2, let lambda=n(n-1). Consider the polynomial operator

    T_N y=r(r+N)*Delta_r^2 y.

It preserves degree, with diagonal coefficient k(k-1) at degree k.
For n>=2, lambda differs from every lower-degree diagonal value.
There is therefore a unique monic degree-n polynomial satisfying

    T_N y=lambda*y.                                 (5)

Evaluation at r=0 and r=-N forces y(0)=y(-N)=0. Also y(1) cannot
vanish: if y(0)=y(1)=0, the rank recurrence determines y at every
positive integer to be zero, contradicting a nonzero polynomial.
Its sign at r=1 is positive. Indeed a negative value would give a
negative first difference; (2) with lambda>0 preserves negativity
and strictly decreasing values at all later integer ranks, contrary
to a monic polynomial's eventual positive sign. Normalize y_n(1)=1.
The same recurrence now shows y_n(r)>0 with increasing positive
first differences for every positive integer r.

The exact separated solutions of (2) with initial e_1=p_(n-2) are

    e_r(m)=y_n(r)*p_(n-2)(m), y_n(r) asymptotic to c_n*r^n,
    c_n>0.                                          (6)

Together these solve arbitrary linearized initial curvature vectors.
For the constant mode p_0=1, L_N p_0=2 and direct substitution gives

    y_2(r)=r(r+N)/(N+1),

proving (1). This mode has zero spatial second difference as an error
profile, but its *weighted* error flux has nonzero second difference.
Dropping the m-dependence of Phi' would incorrectly suppress it.

## 4. Realization by actual determinant derivatives

Let a_m=binomial(N,m)/N^m, 0<=m<=N. For any real vector p on the
interior shifts, choose real b_0=b_1=0 and define successively

    b_(m+1)=2b_m-b_(m-1)-p(m), 1<=m<=N-1.

Perturb the actual coefficients by

    a_m(epsilon)=a_m*exp(epsilon*b_m),

retaining zero coefficients beyond degree N. Every coefficient in
0..N stays positive for real epsilon. At rank one the factorial
normalization is independent of epsilon, so exactly

    delta_1(m;epsilon)=delta_1(m;0)+epsilon*p(m).

At epsilon=0 all determinants D_r(m), 0<=m<=N, are strictly positive
by the known control formula. For any fixed finite rank horizon,
continuity keeps this finite set positive in a neighborhood of zero.
The actual logarithmic determinant recurrence can therefore be
differentiated there. The boundary flux derivatives vanish as explained
above. Uniqueness of (2) proves that its derivative equals (6).
Since the horizon was arbitrary, this proves the derivative formula
at epsilon=0 for every fixed integer rank, without asserting a single
nonzero epsilon neighborhood works at every rank simultaneously.

For p=1 the coefficients are b_m=-m(m-1)/2. This differs from -m^2/2
by a linear scaling term, which cancels from every curvature.

If a rank-independent local Lipschitz constant C bounded the output
curvature sup norm by C times the initial curvature sup norm for all
these perturbations and ranks, differentiating along this direction
would imply r(r+N)/(N+1)<=C for every r, a contradiction. This excludes
such an unweighted uniform stability claim. It does not exclude
rank-dependent bounds, weighted norms, or estimates using extra
Xi-specific constraints on the admissible perturbations.

## 5. Implication for the missing Xi bound

The joint error term identified in the width note must be controlled
with its parameter-dependent coefficient and rank propagation included.
Small spatial differences of e alone are insufficient even in a
fully positive exact control. A viable proof could control the growing
mode projections, exploit a one-sided invariant satisfied by Xi's
specific remainder, or derive a weighted estimate that is still smaller
than the available positivity margin. None of these Xi hypotheses has
been established here. The uniform interior budget and RH remain open.

## Validation

`rank_linearization.py` constructs the eigenpolynomials using exact
FLINT rational polynomial arithmetic and checks their polynomial
identities. Tests cover all modes for degrees 2 through 12. Separate
checks differentiate the original Toeplitz determinants using

    d(log det M)/d epsilon = trace(M^(-1) M'),

with exact rational matrices, and compare the resulting curvature
derivatives with the predicted modes for N=4,6 and several ranks.
These independent finite algebra checks validate the implementation;
the all-degree and all-rank arguments are the proofs above. This work
is not Lean formalized.
