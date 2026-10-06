# Certified finite gates for the prime-defined Weil program

## What is established

The existing arithmetic Weil form now has an interval implementation.
At prime-power support cutoff 13, both mode cutoffs N=4 and N=8 have:

- A positive definite finite Weil matrix.
- A simple lowest eigenvalue, in the even reflection subspace.
- Nonzero boundary evaluation of its lowest eigenvector.

The inputs are prime powers, logarithms, elementary integrals and the
archimedean constant. No Xi coefficients, zeta zeros or fitted zero data
are used. This is still the finite Weil form, not the spectrum of the
perturbed scaling operator.

The construction follows the matrix definition in
[Connes, Consani and Moscovici, *Zeta Spectral Triples*](https://arxiv.org/html/2511.22755v1).
Its Theorem 1.1 uses finite simplicity, even parity and nonzero boundary
normalization. Its section 8 distinguishes infinite-dimensional simplicity
and parity from the additional approximation needed for convergence.
The computations here verify only the stated finite gates; they neither
prove those infinite-dimensional assertions nor convergence to Xi.

## 1. Remove the integration singularity algebraically

Let L=log(cutoff), q=q(U_m,U_n), q0=2 if m=n and 0 otherwise. The
archimedean integrand is

    [exp(y/2)q(y)-q0]/[2sinh(y)].

The floating implementation used a pointwise special case at zero. For
rigorous analytic quadrature we remove the singularity as a function.
Define sinc(z)=sin(z)/z and sinhc(z)=sinc(iz), both with value 1 at zero.
For m!=n,

    q(y)/y=-(2/L)cos(pi(m+n)y/L)sinc(pi(m-n)y/L).

For m=n and omega=2pi*n/L,

    [q(y)-2]/y=-(2/L)cos(omega*y)
                 -omega^2*y*sinc(omega*y/2)^2,
    expm1(y/2)/y=(1/2)exp(y/4)sinhc(y/4).

Thus the diagonal integrand is evaluated as

    {[expm1(y/2)/y]q(y)+[q(y)-2]/y}/[2sinhc(y)],

and the off-diagonal integrand as

    exp(y/2)[q(y)/y]/[2sinhc(y)].

These expressions are analytic at zero and agree with the original
integrand away from zero. They take the endpoint value q0/4-1/L.
Their only possible nearby denominator zeros come from sinhc, not the
removable endpoint. FLINT complex integration includes its error enclosure;
nonfinite output is rejected. The exact archimedean tail beyond L remains
q0*log(tanh(L/2))/2. Prime powers at the endpoint contribute exactly zero.

The pole integral and regularized archimedean integral are evaluated with
512-bit balls and tolerance 2^-240. The reported intervals include
quadrature and rounding error, rather than differences between refinements.

## 2. Interval inertia rather than floating eigenvalue residuals

For a real symmetric target matrix enclosed entrywise, interval LDL
elimination is performed on A-tI. If every pivot excludes zero, the
number of negative pivots is the number of eigenvalues below t, by
congruence invariance of inertia. Every arithmetic operation retains
its interval error. An unresolved pivot aborts this calculation; no
sign is inferred from its midpoint.

A Gershgorin row-sum bound supplies initial eigenvalue brackets.
Bisection uses exact rational midpoints and the certified inertia count.
The endpoint intervals are saved after 160 bisections. The implementation
is deliberately unpivoted: even a nonsingular matrix can have a zero
leading pivot, and that case is reported as unresolved rather than
silently accepted.

The closed correlation formulas imply A_(m,n)=A_(n,m)=A_(-m,-n).
This is an algebraic symmetry of the target, not an inference from
numerically overlapping entries. In the orthonormal even basis

    e_0, (e_n+e_-n)/sqrt(2), n=1,...,N,

and corresponding odd basis, the form separates into two real blocks.
We enclose the first two even eigenvalues and the first odd eigenvalue.
If the upper endpoint of the first even eigenvalue is below both other
lower endpoints, the global lowest eigenvalue is simple and even.

## 3. Nonzero boundary evaluation without a computed eigenvector

In the even basis boundary evaluation is, up to a nonzero common factor,

    ell(x)=x_0+sqrt(2)*sum_(j=1)^N x_j.

Its kernel is spanned by V_j=e_j-sqrt(2)e_0. Let u be a certified upper
bound for the first even eigenvalue. We certify

    V^T(A_even-uI)V > 0

by interval LDL. If a lowest eigenvector x had ell(x)=0, it would lie
in this kernel and its quadratic value for A_even-uI would be
(lambda_min-u)||x||^2<=0, contradicting strict positivity. Hence boundary
evaluation is nonzero and can be used for normalization.

This avoids declaring a small floating eigenvector component nonzero.
The artifact saves every pivot for both full-matrix positivity and the
boundary-kernel restriction.

## 4. Results and the remaining convergence requirement

Both cutoffs use all prime powers through 13; the mode spaces differ.
Rounded descriptions of the saved rational enclosures are:

| N | Dimension | Lowest eigenvalue, approximately | Certified gap exceeds |
|---|---:|---:|---:|
| 4 | 9 | 9.6792618605e-15 | 3.9294e-12 |
| 8 | 17 | 7.6743925564e-23 | 3.9071e-20 |

These are eigenvalues of the finite Weil form, not zeta ordinates.
The gap is much smaller in the second calculation; two cutoffs do not
establish an asymptotic decay law or a uniform lower bound.

A basic quantitative requirement for the next step can be stated without
speculation. If A has simple first eigenvalue lambda0 and gap g>0, then
for any unit candidate x,

    1-|<x,v0>|^2 <= [<x,Ax>-lambda0]/g.

Expand x in an orthonormal eigenbasis to prove the inequality: every
orthogonal component costs at least g in the Rayleigh quotient. Thus
an energy comparison that is merely small in absolute size need not
control the eigenvector when the gap is tiny. A convergence proof must
control the relevant error relative to spectral separation, or supply
a different argument valid without uniform separation.

No omitted-mode error bound, increasing-support comparison, perturbed
operator implementation, or normalized determinant convergence theorem
has been proved in this pass. Those remain necessary work for the
arithmetic route to address RH. The Xi coefficient experiments remain
independent and supply no inputs to these finite matrices.

## Replay and trust boundary

    uv run --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/certified_weil.py --cutoff 13 --modes 4 --output research/prime_spectral/certified_weil_13_4.json
    uv run --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/certified_weil.py --cutoff 13 --modes 8 --output research/prime_spectral/certified_weil_13_8.json
    uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/prime_spectral -p 'test_*.py'

The trust boundary is FLINT ball integration/arithmetic, the documented
Weil-form identity, finite-dimensional inertia and the arguments above.
This is not Lean formalized. Tests include the removable complex identity,
known inertia and eigenvalue cases, unresolved-pivot rejection, agreement
with the old floating formula, and the finite gates. Floating agreement
is only a regression check, not the basis for certification.

Validation: all 9 prime-program tests passed.
