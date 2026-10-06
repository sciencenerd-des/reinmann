# Direct eigenvector cancellation behind the quotient coefficients

Follow-up: the [spatial-kernel certificate](POSITIVE_KERNEL_2026_09_22.md)
proves positivity on the whole support for both stored configurations
and rewrites the weighted sum as a normalized variance. Uniform spatial
concentration and identification with the Xi theta measure remain unproved.

## Result

The prime quotient's Taylor coefficients can be computed directly from
its even eigenvector, with one shared denominator, without matrix
inversion. This gives a sharper finite computation and expresses the
missing compactness estimate as a weighted arithmetic eigenvector bound.

Let c_-n=c_n be the even eigenvector in the quotient construction,
normalized by sum c_n=1, with c_0!=0. Put

    L=log(cutoff), x=z^2, a_n=(L/(2pi*n))^2,
    E(x)=product_(n=1)^N (1-a_n*x).

Then the normalized quotient polynomial satisfies the exact identity

    R(z)=E(x)-(2/c_0)*sum_(n=1)^N c_n*a_n*x
                                *product_(j!=n)(1-a_j*x).                (1)

In particular its positive spectral sum is

    S=trace(B^(-2))/2
     =(L/(2pi))^2 * sum_(n=1)^N (1+2c_n/c_0)/n^2.    (2)

These identities use no Xi coefficients or zeros. The real-zero and
positivity conclusions still require the established finite quotient
gates. The coefficient formulas themselves follow from the even-vector
construction and its nonzero origin normalization.

## 1. Derivation preserving the common denominator

The quotient/Fourier identity, grouped in the +/-n pairs, gives

    P(z)=sinc(zL/2) * [1+(2/c_0)*sum_(n=1)^N
                                           c_n*z^2/(z^2-d_n^2)],
    d_n=2pi*n/L.

The sine product is E(z^2) times the exterior grid factor G(z).
Divide the exact identity P=R*G and cancel each finite rational
factor algebraically. The result is (1), as a polynomial identity
including all formerly removable grid points. Its constant coefficient
is exactly one. Taking its z^2 coefficient gives minus (2).

If E_k denotes the elementary symmetric polynomial of degree k in
(a_1,...,a_N), and E_(k-1)^omit(n) omits a_n, then

    [z^(2k)]R=(-1)^k * [c_0*E_k
                   +2*sum_n c_n*a_n*E_(k-1)^omit(n)]/c_0.               (3)

Thus the numerator is linear in the eigenvector entries and the
normalizing denominator c_0 is shared. Formula (3) is invariant under
any common nonzero rescaling of the eigenvector. The implementation
forms that numerator first and divides only once per coefficient.
Repeated powers of an interval inverse matrix are unnecessary.

## 2. The exact missing compactness estimate

By the preceding spectral-sum theorem, the gated normalized quotient
family is locally bounded if and only if S is uniformly bounded.
Equation (2) makes this equivalent, along increasing L, to

    0 < H_N^(2)+2*sum_(n=1)^N c_n/(c_0*n^2) = O(L^(-2)),               (4)
    H_N^(2)=sum_(n=1)^N n^(-2).

Individual summands in (4) need not be positive. Bounding the positive
and negative eigenvector contributions separately by fixed constants
would generally leave S=O(L^2), which is insufficient for compactness.
The needed cancellation is both signed and quantitative.

Equation (4) is a necessary and sufficient reformulation of the
compactness requirement for this gated family. It is not an independently
proved estimate. The finite eigenvalue equations define the c_n, but no
uniform argument deriving (4) from their prime and archimedean terms has
been obtained here. Even a proof of (4) would give subsequential compactness,
not identification of the limit with Xi. All-order coefficient convergence
or a separate uniqueness theorem would still be needed.

The boundary normalization sum c_n=1 alone cannot prove (4): it is an
unweighted sum, whereas (4) depends on n^(-2) weights and division by c_0.
Nor is a bound on the ordinary eigenvector norm a substitute without
control of c_0 and the signed weighted cancellation.

## 3. Finite certified result

The same stored cutoff-13 certificates give

    S_4 near 0.0082346643621485372774939913557,
    S_8 near 0.01147998256748904.

The direct mode-8 enclosure is more than 10^10 times narrower than the
inverse-trace enclosure from the preceding implementation. Exact widths
and coefficient intervals are reproducible from the saved JSON; the
underlying finite input certificates have not changed. This is an
improvement in propagation of interval dependence, not an improvement
in the certified matrix entries themselves.

Using coefficients through degree six and the same factorial tail
bound gives

    sup_|z|<=1 |R_(13,4)(z)-R_(13,8)(z)| < 0.003275386.

The earlier inverse-trace result, below 0.003320983, remains valid.
All direct coefficient intervals overlap their independent trace-based
counterparts; full polynomial evaluations also agree with direct
normalized determinants. Neither pairwise comparison establishes
convergence or a uniform bound for later cutoffs.

## Implementation, reproduction, and trust boundary

`eigenvector_coefficients.py` constructs the finite products in (1),
truncated only after the requested coefficient order. Terms above that
order cannot influence the retained coefficients. It validates the
length, mode count, order and nonzero common denominator. The comparison
wrapper obtains its vector and quotient from the existing gated build,
and fails on disagreement with the inverse-trace coefficient enclosures.
The JSON records input and source hashes and a finite-only status.

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/eigenvector_coefficients.py --first research/prime_spectral/certified_weil_13_4.json --second research/prime_spectral/certified_weil_13_8.json --output research/prime_spectral/eigenvector_coefficients_13_4_8.json
uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/prime_spectral -v
```

Tests cover an exactly known vector, rescaling invariance, all polynomial
coefficients against independent determinant evaluations at complex
arguments, trace consistency and width improvement, and invalid domains.
The identity is proved algebraically above; overlaps are implementation
checks, not proofs of equality. No Lean formalization is claimed.
Uniform weighted eigenvector cancellation, convergence to Xi, and RH
remain unproved.
