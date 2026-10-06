# Finite quotient operator, real-zero profile, and a necessary scaling condition

Update (2026-09-20): the [grid-tail factorization](GRID_TAIL_SCALING_2026_09_20.md)
strengthens the necessary scaling for the unmodified Xi target to
N/(log cutoff)^2 -> infinity. It also separates the normalized quotient
characteristic polynomial from the forced exterior grid product, with
an explicit complex-disk error bound. Convergence remains unproved.

## Result and scope

The prime-defined finite matrices at cutoff 13 now yield an explicit quotient
operator. For the stored N=8 certificate its dimension is 16. Its quotient
metric is certified positive. The exact identities below prove metric
self-adjointness and show that the associated entire Fourier profile has
only real zeros.

This implements the finite perturbation mechanism discussed in
[Connes--Consani--Moscovici](https://arxiv.org/html/2511.22755v1), rather than
identifying the eigenvalues of the Weil form with zeta ordinates. No Xi
coefficients or zero data enter the construction. No convergence to Xi is
proved. The written algebraic/analytic proof is not Lean formalized.

## 1. The exact rank-two displacement identity

Index the real symmetric Weil matrix A by i,j=-N,...,N. The off-diagonal
correlations are differences of sine functions divided by pi(j-i). Since
every contribution defining the Weil form is linear in the correlation,
there are real b_i such that

    A_ij=(b_i-b_j)/(i-j) for i!=j,
    b_0=0, b_-i=-b_i.

In particular b_i=i*A_(i,0). This is an identity of the defining integrals
and finite prime sums. It is not deduced from numerical agreement.

Put omega=2pi/L, D=diag(omega*i), and let e be the all-ones column. Then

    [A,D]=A D-D A=omega*(e b^T-b e^T).                  (1)

Let lambda be the simple first eigenvalue and c its real even eigenvector,
normalized by e^T c=1. The finite gate certificate and the enclosed projected
solve establish the existence of this normalization. Evenness gives b^T c=0.
For G=A-lambda I, equation (1) therefore implies

    G c=0, G D c=[A,D]c=-omega*b.                      (2)

Define the finite perturbed operator

    T=D-D c e^T.

It kills c. Substituting (1)-(2) gives the exact equality

    G T-T^T G=[A,D]-G D c e^T+e c^T D G=0.             (3)

The eigenvalue lambda is simple and lowest, so G is positive semidefinite
with kernel exactly span(c). It induces a positive inner product on the
quotient by that kernel, and (3) makes the induced operator self-adjoint.
Thus the quotient operator has only real eigenvalues.

## 2. Explicit quotient coordinates

Choose the representatives W_j=e_j-e_0 for all j!=0, spanning ker(e^T).
The projection onto this space along c is P=I-c e^T. Since e^T W_j=0,

    T W_j=D W_j=d_j e_j, P T W_j=d_j(e_j-c), d_j=omega*j.

In these coordinates the quotient matrix and metric are

    B_ij=d_j*(delta_ij-c_i), i,j!=0,
    K_ij=G_ij-G_(i,0)-G_(0,j)+G_(0,0).

The implementation encloses B and K and certifies K>0 with interval LDL.
It also checks that the displacement and K B-B^T K residuals enclose zero.
These residual checks can detect implementation disagreements, but their
inclusion of zero is **not** the proof of identities (1) or (3). Those
identities follow from the exact argument above.

## 3. Determinant and entire-profile identities

Set

    Q(z)=sum_(i=-N)^N c_i product_(j!=i)(z-d_j).

This polynomial has degree 2N and leading coefficient sum c_i=1. The
matrix determinant lemma gives, first away from the grid and then as a
polynomial identity,

    det(zI-T)=product_j(z-d_j)*[1+sum_j d_j*c_j/(z-d_j)]
             =z*Q(z).

The factor z accounts for the killed vector c. Thus Q(z)=det(zI-B).
Its zeros are real by quotient self-adjointness.

The origin-normalized entire Fourier profile is

    P_N(z)=sum_(n=-N)^N c_n*(-1)^n*sinc(pi*n-zL/2)/c_0.

The certified eigenvector has c_0!=0. At zero this gives P_N(0)=1.
Using sin(pi*n-zL/2)=(-1)^(n+1)sin(zL/2), one obtains

    P_N(z)= [2sin(zL/2)/(L*c_0)] * Q(z)/product_n(z-d_n). (4)

The apparent singularities at the real grid points are removable, as is
already clear from the sinc formula. Away from that grid, every zero
comes from either Q or sin(zL/2), both of which have only real zeros.
Hence the entire P_N has no nonreal zeros.

This is a finite-arithmetic real-zero approximant. Its zeros are not
identified with the zeros of Xi, and the quotient eigenvalues must not
be labeled zeta ordinates.

## 4. Forced grid zeros constrain every possible convergence path

Equation (4), or the sinc formula directly, gives exact zeros

    P_N(2pi*k/L)=0 for every integer |k|>N.              (5)

These exterior grid zeros are part of the finite approximant, even when
its quotient spectrum is well controlled. They yield a necessary condition
for a nonzero limit as support grows.

**Proposition.** Suppose L_j->infinity and the normalized profiles P_(N_j,L_j)
converge locally uniformly on the complex plane to a nonzero entire function.
Then N_j/L_j->infinity. Here L_j=log(cutoff_j).

**Proof.** If not, pass to a subsequence with N_j/L_j<=C. For any fixed
x>2pi*C choose an integer k_j nearest to xL_j/(2pi). For sufficiently
large j it satisfies k_j>N_j, while 2pi*k_j/L_j->x. Equation (5) makes
P_j zero at those points. Local uniform convergence and continuity imply
P(x)=0. This holds for a whole real interval, so the identity theorem
forces P to be identically zero, a contradiction. QED.

For the present normalization P_j(0)=1, a locally uniform limit cannot be
zero. Thus any successful increasing-support path must in particular satisfy

    modes/log(prime_power_cutoff) -> infinity.

This condition is necessary, not sufficient. It gives no convergence rate,
no uniform spectral simplicity or parity theorem, and no identification
with Xi. The summability and weighted-kernel targets in the previous note
remain open. Merely increasing both cutoffs without controlling their
relative growth can never establish the desired nonzero entire limit.

## Replay and validation scope

    uv run --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/quotient_operator.py --certificate research/prime_spectral/certified_weil_13_8.json --output research/prime_spectral/quotient_13_8.json
    uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/prime_spectral -p 'test_*.py'

Exact rational tests verify a nontrivial metric-adjoint example and the
characteristic polynomial identity. Interval tests verify the actual quotient
construction, the complex profile identity and the forced grid zeros.
The artifact records the quotient matrices and source hashes. The real-zero
claim relies on the written proof plus the certified finite hypotheses,
not on numerical sampling of roots or zero-enclosing residuals alone.

Validation: all 15 prime-program tests passed; input/source hashes match
and `git diff --check` passed.
