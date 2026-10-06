# An exact forced-mode budget with growing-mode cancellation

## Result and scope

The [linearization control](RH_RANK_LINEARIZATION_2026_09_20.md) exhibits
polynomially growing rank modes. This note gives an exact Green formula
and a sufficient all-rank bound for a forced mode when its growing
amplitude cancels. It is a theorem for the specified scalar control
equations, not a proved estimate for the Xi remainder.

For the simplest mode at N=2, suppose

    e_0=0, e_1=a,
    e_(r+1)-2e_r+e_(r-1)=2e_r/[r(r+2)]+F_r, r>=1.

If, for a fixed B>0,

    |F_r|<=2B/[r(r+2)],
    a+sum_(k=1)^infinity F_k/(k+1)=0,                 (1)

then the following bound holds at every integer rank:

    |e_r|<=B*r/(r+1)<B, r>=1.                       (2)

Equality in the first bound is attained by a=1/2, B=1,
F_r=-2/[r(r+2)], e_r=r/(r+1). Thus the estimate accommodates
cancellation of the entire growing amplitude without imposing a
positive leftover slope margin.

A nonzero mismatch in the second condition of (1) instead gives
quadratic growth in this model. Passing a finite approximate balance
check is not an infinite cancellation certificate.

## 1. General scalar mode and a decaying companion

Fix integers N>=2 and 2<=n<=N. Put

    V_r=n(n-1)/[r(r+N)].

Let y be the exact degree-n polynomial solution established in the
linearization note, normalized by y_0=0 and y_1=1. For every r>=1,
y_r>0 and Delta_r^2 y_r=V_r*y_r. Define

    d_r=y_r*sum_(j=r)^infinity 1/(y_j*y_(j+1)), r>=1,
    d_0=1.                                          (3)

Since y_r is asymptotic to c*r^n with c>0, the sum converges and

    d_r is asymptotic to r^(1-n)/[c*(2n-1)].

Subtracting the sums in (3) gives the exact Wronskian identity

    y_r*d_(r+1)-y_(r+1)*d_r=-1, r>=1.                (4)

It implies Delta_r^2 d_r=V_r*d_r for r>=2. At r=1,
y_2=2+V_1 and (4) give d_2=(2+V_1)*d_1-1, which is the
same recurrence with d_0=1. Thus both boundary data are specified.
The d_r are positive and tend to zero. Their second differences are
positive, so their backward slopes increase. None can be nonnegative,
which would prevent convergence to zero. Hence 0<d_r<1 for r>=1.

## 2. Finite Green identity

For any real forcing sequence, let

    Delta_r^2 e_r=V_r*e_r+F_r, e_0=0, e_1=a.

Define W_r=y_r*e_(r+1)-y_(r+1)*e_r. Direct subtraction of the two
recurrences, including W_0=0, gives

    W_r-W_(r-1)=y_r*F_r.

Summing once over W and then over e_r/y_r yields

    e_r=y_r*a+sum_(k=1)^(r-1) G(r,k)*F_k,
    G(r,k)=y_r*d_k-d_r*y_k
          =y_r*y_k*sum_(j=k)^(r-1) 1/(y_j*y_(j+1)). (5)

In particular G(r,k)>0 for 1<=k<r. Equation (5) is an exact
identity for finite ranks; no asymptotic or forcing-tail assumption
is used in its derivation.

## 3. The precise growing amplitude

Assume sum d_k*|F_k| converges. For fixed k,
G(r,k)/y_r tends to d_k and lies between zero and d_k. Dominated
convergence in (5), extending its kernel by zero for k>=r, proves

    lim_(r->infinity) e_r/y_r
      =a+sum_(k=1)^infinity d_k*F_k=:M.              (6)

Thus M=0 is necessary and sufficient for e_r=o(y_r). It does not
alone imply boundedness; the forcing envelope below supplies that.
When M=0, subtracting the infinite sum from the finite formula gives

    e_r=-y_r*sum_(k=r)^infinity d_k*F_k
         -d_r*sum_(k=1)^(r-1) y_k*F_k.              (7)

This form keeps the cancellation of the growing term exact before
bounding the remaining terms. Taking separate absolute values in
the original initial-data and forcing terms would lose that benefit.

## 4. Uniform bound from a potential-sized forcing envelope

Suppose M=0 and |F_r|<=B*V_r. Absolute convergence in (6) holds
because d_r*V_r=O(r^(-n-1)). Equation (7) implies

    |e_r|<=B*[y_r*sum_(k=r)^infinity d_k*V_k
              +d_r*sum_(k=1)^(r-1) y_k*V_k].        (8)

To evaluate the positive bracket, use u_r=1-d_r. It satisfies u_0=0,
u_1=1-d_1, and Delta_r^2 u_r-V_r*u_r=-V_r. Since u_r is bounded,
u_r/y_r tends to zero, so (6) proves its growing amplitude vanishes.
Applying (7) to this explicit solution identifies the bracket in (8)
as 1-d_r. Therefore, for every integer r>=0,

    |e_r|<=B*(1-d_r)<=B.                            (9)

This is an all-rank stability theorem conditional on an exact signed
moment identity, not an unconditional stability assertion about the
recurrence. The growing modes found previously remain present when
that identity fails.

## 5. Exact implementation for N=n=2

Here the fundamental solutions are elementary:

    y_r=r(r+2)/3, d_r=1/(r+1).

They satisfy the recurrence and Wronskian exactly, so (6) and (9)
reduce to (1)-(2). The helper uses a finite rational forcing prefix
F_1,...,F_(R-1), followed by the specified analytic tail

    F_r=-2T/[r(r+2)], r>=R, |T|<=B.

Its signed tail moment is exactly

    sum_(r=R)^infinity d_r*F_r=-T/[R(R+1)],           (10)

because 2/[r(r+1)(r+2)]=1/[r(r+1)]-1/[(r+1)(r+2)].
The classifier computes

    M=a+sum_(r=1)^(R-1) F_r/(r+1)-T/[R(R+1)]

as an exact fraction. It certifies the conditional bounded response
only for M=0 and verified forcing bounds. A nonzero rational M is
classified as a growing mode in this scalar control, however small
its magnitude. No tolerance can turn a mismatch into a balance proof.

Tests compare (5) with direct recurrence for a signed forcing sequence,
verify the saturating bounded solution exactly, check a mixed-sign
prefix with its infinite tail, and detect a head mismatch of 10^(-12).
The last mismatch changes e_r by exactly 10^(-12)*r(r+2)/3.

## 6. What this does and does not supply for Xi

The preceding result specifies a concrete way to overcome amplification:
prove a signed moment identity for the full residual and a compatible
forcing bound. Neither is supplied by small pointwise errors or finite
positive determinant checks. In a nonlinear argument the forcing also
contains the nonlinear remainder and boundary discrepancies; it cannot
be replaced silently by the truncation error alone.

The Xi problem is not identified with this finite repeated-root system.
An application needs an appropriate Xi reference operator, its Green
bounds, source identification, and head/boundary control established
without presuming future positive determinants. Even in the control,
choosing a new initial a to cancel M is not allowed when a is fixed by
actual input data. The certificate here only checks the stated model.
The uniform Xi interior budget and RH remain unproved.

Reproduction:

```sh
uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/certified_xi -p test_rank_green_budget.py -v
```

The proof uses exact recurrence identities, convergence of positive
series, and dominated convergence. The implementation uses rational
arithmetic. No Lean formalization is claimed.
