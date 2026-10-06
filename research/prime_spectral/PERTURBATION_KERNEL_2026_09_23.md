# Certifying the cutoff-31 prime kernel by a matrix perturbation bound

## Result and scope

At prime-power cutoff 31 and mode count 16, the same finite Weil matrix
used by the prior prime program has a certified positive, simple even
lowest eigenvalue and a nonzero boundary evaluation. Its normalized
spatial Fourier kernel is strictly positive across the whole support.
The certified variance is approximately 0.06465747725090082.
Consequently the established exact quotient construction supplies a
finite origin-normalized polynomial and Fourier profile with only real
zeros at this configuration.

The earlier direct interval eigenpair routine could not isolate the
even-block spectrum at this cutoff. The present certificate proves that
result was unresolved because of interval conditioning. It does not
prove uniform finite gates, a variance bound along an infinite path,
convergence to Xi, or RH.

## 1. Transfer from a midpoint matrix to the defining interval matrix

Let A be an actual real symmetric even or odd block defined by the
certified prime and archimedean integrals. Its computed interval entries
are A_ij in balls X_ij. Let M_ij be the exact dyadic midpoint of X_ij.
The code checks that M is symmetric. Put

    d=max_i sum_j radius(X_ij).

Every possible symmetric A in the entry balls satisfies

    ||A-M||_2 <= ||A-M||_infinity <= d.              (1)

The first inequality uses symmetry and the row-sum bound; it is not a
claim that independently selected nonsymmetric entries are eigenvalue
candidates. The actual defining matrix is symmetric by its formulas.

FLINT's certified Rump eigenpair algorithm isolates all eigenvalues of
the exact midpoint matrix M. Midpoints propose the eigenvalue ordering,
but strict separation of the returned intervals establishes it. Let
mu_0<mu_1 be the two smallest midpoint eigenvalues. The min-max
characterization of symmetric eigenvalues and (1) give, for the actual
block eigenvalues lambda_j,

    |lambda_j-mu_j|<=d.                               (2)

This inference requires no attempt to diagonalize the interval matrix
entrywise. We verify mu_0>d and mu_1-mu_0>2d for each block. Across the
even and odd blocks we also verify

    min(mu_1_even-d_even,mu_0_odd-d_odd)
       -(mu_0_even+d_even)>0.                         (3)

Thus the full matrix is positive and its lowest eigenvalue is simple
and even. At cutoff 31, mode 16, the midpoint even eigenvalues begin near

    mu_0=2.90381023884891566e-44,
    mu_1-mu_0=2.36690111299544875e-38,

while d_even<3.779e-71. The odd first eigenvalue is near 4.02776e-41
with d_odd<3.621e-71. These are certified intervals and strict
inequalities, not sampled floating eigenvalues.

## 2. Bounding the actual eigenvector

Let u be a unit real eigenvector for mu_0, obtained from the certified
midpoint eigenvector enclosure. The real part is a real eigenvector
because M and mu_0 are real; its norm is checked nonzero. Let v be the
unit eigenvector for the actual lowest eigenvalue, signed so its inner
product with u is nonnegative. Project

    (M-lambda_0 I)v=-(A-M)v

onto u's orthogonal complement. The inverse there has norm at most
1/(mu_1-lambda_0), and by (2) the denominator is at least
mu_1-mu_0-d. Therefore

    ||v-<v,u>u||_2 <= d/(mu_1-mu_0-d).

The chosen sign and unit norms imply

    ||v-u||_2 <= sqrt(2)*d/(mu_1-mu_0-d)=:eta.       (4)

Every component of the actual v lies in the corresponding midpoint
component interval widened by eta. The midpoint intervals themselves
remain present in the calculation; eta is not substituted for their
finite precision. At cutoff 31, eta_even is near 2.26e-33.

In the even orthonormal coordinates the boundary evaluation is

    b=v_0+sqrt(2)*sum_(n=1)^N v_n.

The enclosed b is strictly positive, near 1.245757248e-21, so the
normalization is nonzero. The small size of b makes it crucial to keep
all component correlations that can cancel before dividing by b.

## 3. Proving positivity of the full spatial kernel

The normalized Fourier coefficients are c_0=v_0/b and
c_n=v_n/(sqrt(2)*b) for n>=1. The positivity certificate forms the
Bernstein coefficients of the boundary-anchored polynomial in
u=(1+cos(2pi*t/L))/2. It first computes the *numerator*

    b+sqrt(2)*sum_(n=1)^N v_n*(T_n(1-2u)-1),

and divides each resulting Bernstein coefficient by b only at the end.
This is algebraically identical to the previous positive-kernel gate.
It retains cancellation among the v_n before division by a boundary
value of order 10^(-21). Dividing each interval component separately
would produce unnecessarily wide enclosures here.

All 17 Bernstein coefficients are strictly positive. The first is near
one and is anchored at one exactly in the underlying identity. Since
the Bernstein basis is nonnegative and sums to one, the actual kernel
is positive for every t in the full support interval. The normalized
mass c_0=v_0/b is certified positive. The variance is computed as

    V=L^2*(v_0/12+sum_(n=1)^N v_n/(sqrt(2)*pi^2*n^2))/v_0,

with the common v_0 denominator retained. It lies in the saved positive
interval around 0.06465747725090082.

The exact displacement identity and quotient self-adjointness argument
from the earlier proof now apply. The matrix is positive, the lowest
vector is simple and even, and b is nonzero. No complex zero search or
identification with zeta ordinates enters the finite conclusion.

## 4. Reproduction and remaining gap

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/perturbation_kernel.py --cutoff 31 --modes 16 --output research/prime_spectral/perturbation_kernel_31_16.json
uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/prime_spectral -v
```

The artifact records the eigenvalue and vector error bounds, the
normalized boundary, every Bernstein coefficient, the variance and
source hashes. Tests include an exact diagonal transfer case, agreement
with the older cutoff-13 kernel, the cutoff-31 gate, and rejection of
unresolved separation and a sign-changing kernel. The proof relies on
the defining interval integrals, certified midpoint eigenpairs and the
explicit perturbation bounds (1)-(4). It is not Lean formalized.

The variance at cutoff 31 is larger than at cutoff 23 with the same 16
modes. This finite trend gives no uniform upper bound. For an unmodified
profile to approach Xi, the modes must also grow faster than the square
of log cutoff, and the spatial measures must be shown to converge to the
Xi theta measure. Those statements remain unproved. RH remains open.
