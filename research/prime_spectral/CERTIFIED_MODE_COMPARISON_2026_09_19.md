# Certified eigenvectors and the finite-mode convergence gap

## Result and scope

At the fixed arithmetic support cutoff 13, the certified lowest eigenvectors
for modes 4 and 8 can be compared in the same Hilbert space. Their unit-vector
distance is enclosed near 0.1376136120. Their boundary-normalized scales are
not identified with each other, and no different-support spaces are compared.

This is a finite comparison with rigorous interval errors. It proves neither
convergence nor divergence as the number of modes grows. In particular,
smallest-eigenvalue decay is not by itself an eigenvector convergence proof.

## 1. Enclosing the boundary-normalized eigenvector

Use the orthonormal even basis and the certified first eigenvalue interval
from [the finite gate certificate](CERTIFIED_WEIL_GATES_2026_09_19.md). Let
A be the even block, lambda its actual first eigenvalue, and

    ell(x)=x_0+sqrt(2)*sum_(j=1)^N x_j,
    V_j=e_j-sqrt(2)e_0.

The finite gate proof establishes that ell does not vanish on the simple
lowest eigenspace. Thus there is a unique eigenvector x with ell(x)=1.
Write x=e_0+Vy, where the columns of V span ker ell. Projecting the
eigenvalue equation onto that kernel gives

    K(lambda)y=-V^T(A-lambda I)e_0,
    K(lambda)=V^T(A-lambda I)V.                         (1)

The certificate proved K(u)>0 for an upper eigenvalue bound u. Since
lambda<=u, K(lambda)>=K(u)>0. Thus (1) has a unique solution, and the
actual normalized eigenvector must be that solution. This is why solving
the projected equation suffices; an arbitrary spectral parameter would
not necessarily solve the full eigenvector equation.

The implementation encloses K and its right side over the entire certified
eigenvalue interval and uses FLINT's rigorous linear solver. It never
substitutes the eigenvalue midpoint or the approximate-only solve mode.
The resulting vector encloses the exact boundary-normalized eigenvector.
Its positive norm and nonzero zeroth coordinate are checked before further
normalization. Unit vectors retain the orientation ell(x)>0.

## 2. Common embeddings and normalized entire profiles

For the same L, an even mode vector embeds into a larger even mode space
by padding with zeros. This uses the same orthonormal Fourier basis and
is an isometry. Different values of L are rejected by the comparison tool.

For each enclosed vector x, let a=x/x_0, so a_0=1 exactly. In the original
complex Fourier basis the coefficients are c_0=1 and
c_n=c_-n=a_n/sqrt(2) for n>=1. Define the centered, origin-normalized profile

    P_N(z)=(1/sqrt(L)) integral_0^L
             [sum_(n=-N)^N c_n U_n(t)] exp(-iz(t-L/2)) dt.

This is entire and P_N(0)=1. The zeroth coordinate check is essential for
this normalization. This profile is constructed from the prime-defined
matrix eigenvector, with no Xi coefficients or zero locations as input.

For two nested cutoffs at the same L, let d be the Euclidean distance
between their zero-padded even a vectors. Cauchy-Schwarz and orthonormality
give the rigorous compact-domain estimate

    sup_|z|<=T |P_M(z)-P_N(z)| <= exp(TL/2)*d.           (2)

Indeed the difference of the two bracketed Fourier sums has L2 norm d,
while the exponential has L2 norm at most sqrt(L)exp(TL/2). This controls
complex arguments, not only the real line.

Equation (2) is a bound between two finite profiles. It does not estimate
any subsequent modes or identify a limiting profile with Xi.

## 3. The observed finite gap

For cutoff 13, N=4 versus N=8, the interval calculation gives approximately

    unit eigenvector distance                 0.1376136120368440,
    origin-normalized coefficient distance   0.2698911863483721,
    Rayleigh excess / certified gap          247730.70364029196.

The first two quantities are distances after the explicit common embedding.
The entire-profile bound uses the second one in (2). All saved endpoints
are outward rational enclosures; these decimals are descriptive summaries.

Why is the last quantity relevant? The embedded smaller-space eigenvector
has Rayleigh quotient equal to its smaller-space eigenvalue, since the
matrix forms agree exactly on the nested subspace. The standard elementary
spectral estimate in the previous note bounds its squared component away
from the new lowest eigenspace by

    (lambda_small-lambda_large)/gap_large.

The certified ratio is much larger than one, so that estimate is vacuous
for this pair. The tiny first eigenvalues alone do not close an approximation
argument. This does not imply that another argument could not establish
convergence, or that the finite vectors must converge at a particular rate.

## 4. An explicit sufficient convergence target

At fixed L, suppose one can prove for a growing sequence N_k that

    sum_k ||a_(N_(k+1))-a_(N_k)||_2 < infinity,

using the same zero-padding embedding. Equation (2) then proves that P_(N_k)
is locally uniformly Cauchy on the entire plane. Its limit is entire and
has value one at zero, so it is not identically zero. This is an actual
sufficient convergence theorem, but its summable bound is not established
by one finite comparison.

If real-zero profiles were proved at every cutoff of that sequence, the
nonzero locally uniform limit would also have only real zeros: otherwise
a small disk around a nonreal limit zero, with nonzero boundary values,
would force nearby finite-profile zeros by Rouche's theorem. Two finite
spectral-gate certificates do not supply the all-cutoff premise.

Finally, neither fixed-support convergence nor real zeros alone identifies
the limit with Xi. For increasing support, one sufficient identification
criterion is convergence of centered spatial kernels to the desired Xi
kernel in each weighted L1 norm

    integral_R exp(T|t|)*|g_j(t)-g_Xi(t)| dt -> 0,

for every T>0, with the chosen normalization. Directly estimating the
Fourier integrals then gives local uniform convergence on |z|<=T. This
criterion is stated as a missing analytic target, not an established
estimate for the computed eigenvectors. No target kernel data are fed
into their construction.

## Replay and validation

    uv run --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/certified_mode_comparison.py --first research/prime_spectral/certified_weil_13_4.json --second research/prime_spectral/certified_weil_13_8.json --output research/prime_spectral/mode_comparison_13_4_8.json
    uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/prime_spectral -p 'test_*.py'

Source certificates and generator hashes are checked. Tests verify boundary
and unit normalization, the distance/inner-product identity, compact-bound
scaling, and rejection of mismatched support or uncertified inputs. The
analytic arguments remain written, not Lean formalized. The perturbed
operator and the all-mode/all-support convergence theorem remain open.

Validation: all 12 prime-program tests passed; input/source hashes match
and `git diff --check` passed.
