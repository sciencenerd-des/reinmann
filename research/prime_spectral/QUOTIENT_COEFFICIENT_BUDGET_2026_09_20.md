# A spectral-sum compactness criterion for prime quotient polynomials

Follow-up: the [direct eigenvector formula](EIGENVECTOR_COEFFICIENTS_2026_09_20.md)
retains a common denominator and substantially sharpens the finite coefficient
intervals. It also expresses the required uniform spectral bound as an
explicit weighted eigenvector cancellation. That uniform estimate remains open.

## Results and scope

For a prime quotient passing the existing real-zero gates, write

    R(z)=det(zI-B)/det(-B)=product_(l=1)^N (1-z^2/lambda_l^2),
    S=sum_(l=1)^N lambda_l^(-2)=trace(B^(-2))/2.

Every lambda_l is real and nonzero. This follows from the finite quotient
proof, not from the sign of a sampled trace. Define positive elementary
symmetric coefficients e_k by R(z)=sum_(k=0)^N (-1)^k e_k z^(2k).
Then

    0<=e_k<=S^k/k!,
    |R(z)|<=exp(S*|z|^2).                            (1)

For the Taylor polynomial through degree 2K, uniformly on |z|<=rho,

    |R(z)-sum_(k=0)^K (-1)^k e_k z^(2k)|
      <= exp(S*rho^2)*(S*rho^2)^(K+1)/(K+1)!.        (2)

The tail is exactly zero if K>=N. These estimates lead to a concrete
finite comparison and a conditional convergence criterion. They do not
establish a uniform S bound or coefficient convergence along a growing
prime-support sequence, and do not prove RH.

## 1. Elementary symmetric bound and whole-disk tail

Set x_l=lambda_l^(-2)>0. The expansion of (sum x_l)^k contains k!
ordered copies of every product of k distinct variables, together with
nonnegative repeated-index terms. This proves k!*e_k<=S^k. Summing
absolute values proves (1). For x=S*rho^2, the Taylor remainder is at
most sum_(k=K+1)^infinity x^k/k!. The inequality
(K+1+j)! >= (K+1)!*j! bounds that sum by the right side of (2).

These are algebraic consequences of real, paired, nonzero zeros. They
must not be applied to a general matrix just because trace(B^(-2))
happens to be positive. The implementation obtains the actual quotients
through the existing finite gate and metric construction.

## 2. Compactness and identification are different requirements

For any sequence of such normalized polynomials, a uniform bound on S
implies uniform boundedness on every complex disk by (1). Conversely,
uniform boundedness even at one nonzero imaginary argument iy forces
S to be bounded, because

    R(iy)=product_l(1+y^2*x_l)>=1+y^2*S.

Thus one bounded positive spectral sum is exactly the compact-boundedness
condition for this family. It does not identify a limit.

For completeness, the subsequence argument requires no unstated normality
claim. Bound each coefficient by (1), extract a convergent subsequence
successively at each coefficient index, and take a diagonal subsequence.
The factorial tail bound (2) is uniform in the subsequence, so its power
series converge uniformly on every disk to an entire function F, F(0)=1.
Rouche's theorem on a small disk around a putative nonreal zero of F
would force a nonreal zero in sufficiently late polynomials. Therefore
F has only real zeros. This is the usual real-zero closure argument;
it supplies no reason that F equals Xi.

If instead *every* even Taylor coefficient of the full sequence converges
to that of a specified entire target F, then the sequence converges locally
uniformly to F. Indeed the coefficient at z^2 is -S, so its convergence
already bounds S; (2) then controls the tails uniformly while any fixed
finite coefficient prefix converges. Conversely local uniform convergence
implies coefficient convergence by Cauchy's integral formula.

Consequently, for these gated polynomials,

    all-order coefficient convergence to Xi(z)/Xi(0)
    is equivalent to local uniform convergence to that target.             (3)

This is a reduction of the missing theorem, not evidence that its
hypothesis holds. No finite set of coefficient comparisons proves (3).

## 3. Prime-only coefficient computation

The paired spectrum gives power sums

    s_j=sum_l x_l^j=trace(B^(-2j))/2.

Newton's identities compute e_0=1 and

    k*e_k=sum_(j=1)^k (-1)^(j-1)*e_(k-j)*s_j.        (4)

These formulas use the prime-defined quotient matrix directly. No Xi
coefficient, zero, or fitted parameter enters the construction. FLINT
ball matrix inverses and products enclose the traces, and ball arithmetic
encloses (4). A positive upper endpoint of S controls (2). Unresolved
invertibility, nonfinite coefficient bounds, or an unresolved positive
S fail rather than producing a certificate.

For two quotients with coefficient enclosures c_k and c'_k and Taylor
remainders T,T', the certified whole-disk comparison is

    sup_|z|<=rho |R(z)-R'(z)|
      <= sum_(k=0)^K |c_k-c'_k|*rho^(2k)+T+T'.       (5)

The two supports need not coincide: both polynomials use the same
physical complex argument z and origin normalization. This finite
comparison itself makes no nesting or convergence assertion.

## 4. Finite prime result at cutoff 13

Using the existing mode-4 and mode-8 finite certificates, K=3 and rho=1:

* S_4 is enclosed near 0.00823466436214853728.
* S_8 is enclosed by a ball centered near 0.0115 with radius below 0.000055.
* The Taylor tails are below 1.931740e-10 and 7.409310e-10 respectively.
* The full disk difference is below 0.003320983.

The higher-mode spectral sum is larger in these certificates. Neither
these two values nor the small Taylor tails prove a bounded S along
an infinite path. Most of the finite comparison bound comes from the
computed coefficient differences, not the omitted Taylor terms.

The saved JSON records exact rational bounds, coefficient intervals,
input/source hashes, and the finite-only status. Direct determinant
checks at interior complex points give a separate consistency check.
At the disk boundary the direct determinant interval was wider than
the coefficient-based bound; it was inconclusive as an independent
containment test. The disk-wide certificate rests on (1)-(5), not on
point sampling.

## 5. Remaining arithmetic target

This supplies the previously missing *form* of a compact bound for R:
prove S is bounded uniformly along an arithmetic sequence. Proving
convergence of S is stronger and still insufficient for identification.
The additional target is convergence of every coefficient from (4),
or another independently justified uniqueness theorem for subsequential
limits. Uniform finite quotient gates must also be established on the
chosen path. All these sequence-wide arithmetic facts remain open.

The exterior-grid bound from the previous note can now be multiplied
by exp(S*rho^2) to control the finite difference between the original
Fourier profile P and its quotient polynomial R. This is effective for
each gated matrix; it is uniform only if S is uniformly bounded and
L^2/N tends to zero. No unproved uniformity is imported here.

## Reproduction and validation

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/quotient_coefficient_budget.py --first research/prime_spectral/certified_weil_13_4.json --second research/prime_spectral/certified_weil_13_8.json --output research/prime_spectral/coefficient_budget_13_4_8.json
uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/prime_spectral -v
```

Tests cover exactly known diagonal spectra, the omitted-term bound,
independent determinant evaluations of the actual prime comparison,
and invalid domains. This is a written analytic proof with interval
implementation, not a Lean formalization or an RH proof.
