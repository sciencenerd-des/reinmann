# Higher-mode kernels through certified eigenpair isolation

## Result

At prime-power cutoff 13, modes 12 and 16 now pass the finite gates:
positive Weil matrix, simple even lowest eigenvalue, nonzero boundary
normalization, and a spatial kernel positive across its whole support.
The existing exact quotient argument therefore supplies a real-zero
finite polynomial and Fourier profile for both configurations.

The certified variances are near

    N=12: 0.053068211904122581994975046649583,
    N=16: 0.0489749940776518831131658.

The method uses the same defining interval matrix integrals and prime
sums as before. It replaces the numerically unresolved LDL/eigenvalue
bisection and projected eigenvector solve by certified eigenpair isolation.
No defining arithmetic input, quadrature tolerance, or Xi data is changed.
This extends finite evidence; it does not prove a uniform variance bound,
monotonicity for every N, growing-support convergence, or RH.

## 1. Observed certification failures and what they mean

With the original code, cutoff 13 at mode 12 passes the finite Weil gates,
but the subsequent quotient construction reports an unresolved LDL pivot.
At mode 16 the original gate calculation itself reports an unresolved
LDL pivot. Increasing bisection iterations to 200 did not resolve these
failures. None of these outputs certifies a negative eigenvalue.

The alternative computes certified isolated eigenpairs of the same even
and odd interval blocks at 512-bit working precision, using
`acb_mat.eig(right=True, algorithm='rump')`. Approximate eigenpair mode is
not used. All eigenvalues of each block are enclosed and strictly separated.
The lowest even eigenvalues are near

    N=12: 2.139707361258782510379362289370288292206448e-29,
    N=16: 8.568627478072444309520048969996567907e-35.

They are positive and lie strictly below both the next even eigenvalue
and the lowest odd eigenvalue. These new certificates establish that the
old unresolved signs are numerical certification limitations for these
inputs, rather than negative-spectrum findings.

## 2. Inference from the isolated blocks

The exact reflection symmetry decomposes the real symmetric Weil matrix
into the even and odd blocks already constructed by `certified_matrix`.
For each block the implementation requires finite eigenvalue enclosures,
compatibility with real eigenvalues, and pairwise strict ordering of their
real intervals. Midpoints propose the order, but do not certify it: every
adjacent interval pair is checked with a strict inequality.

Positive first eigenvalues in both ordered blocks prove positivity of the
full matrix. The strictly positive gap

    min(second_even,first_odd)-first_even

proves the lowest eigenvalue is simple and even. The entire real spectrum
is supplied by symmetry of the actual defining matrix, not by the mere
inclusion of zero in the imaginary parts of computed intervals.

Let v be the real part of the certified lowest even eigenvector, in the
orthonormal even coordinates. An eigenvector for a real eigenvalue of a
real matrix may be decomposed into real and imaginary parts, each satisfying
the same real eigenvalue equation. The implementation verifies

    b=v_0+sqrt(2)*sum_(n=1)^N v_n != 0.

This proves that the real part used is nonzero and that the actual
boundary evaluation does not vanish. Normalize

    c_0=v_0/b, c_n=v_n/(sqrt(2)*b), n>=1.

Then c_0+2 sum c_n=1 exactly. The raw b can have either sign; it is
its exclusion of zero, not a chosen eigenvector sign, that matters.
Positive c_0 and positive Bernstein coefficients are checked afterward.

## 3. Quotient and kernel conclusions

For the full matrix A and isolated lowest lambda, G=A-lambda I is
positive semidefinite with kernel exactly the normalized even eigenvector.
The exact rank-two displacement identity and quotient proof are unchanged.
They yield the positive quotient metric and self-adjoint induced operator.
There is no need to infer that exact identity from an interval residual.
The nonzero c_0 makes the origin-normalized polynomial and Fourier profile
well defined, and the established factorization proves their zeros real.

The Bernstein gate from `positive_kernel.py` is then applied using the
boundary-anchored polynomial. All coefficients are positive for modes 12
and 16. Thus the normalized spatial kernels are even probability densities
on the full support, and their variances follow from the exact Fourier
moment identity. The direct coefficient formula gives spectral sums near

    S_12=0.013209429545732594166863981676340,
    S_16=0.01439075815246235026688408.

Across the four certified mode counts 4,8,12,16, variance decreases while
the quotient spectral sum increases. Equation V/2=S+the exterior-grid sum
explains why these two finite trends need not have the same direction.
Neither finite trend is promoted to a theorem for later modes.

## 4. Reproduction and validation

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/isolated_kernel.py --modes 12 --output research/prime_spectral/isolated_kernel_13_12.json
uv run --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/isolated_kernel.py --modes 16 --output research/prime_spectral/isolated_kernel_13_16.json
uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/prime_spectral -v
```

The new method is separate from the old gate, preserving its stored
certificates and source hashes. New artifacts record both spectra,
boundary-normalized vectors, Bernstein coefficients, variance, quotient
coefficients, source hashes, and an explicitly finite status. Tests compare
with an exactly known spectrum and the previous mode-4 method, verify both
new mode counts, and reject unsupported dimensions.

The trust boundary includes FLINT certified eigenpair isolation in addition
to the existing interval matrix integration and written exact identities.
This is not a Lean proof. A uniform path of finite gates, a variance bound
along growing support, and identification of a weak limit with the Xi theta
measure remain unproved. RH remains unproved.
