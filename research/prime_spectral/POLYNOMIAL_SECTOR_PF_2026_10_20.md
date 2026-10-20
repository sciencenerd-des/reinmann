# The polynomial sector theorem is now formalized

The previously open polynomial obligation is proved in
`Reinmann/PolynomialSectorPF.lean`. It is a formalization of the classical
Schoenberg sufficiency theorem, not a new mathematical result and not yet a
proof of `KatkovaSectorBridge 43`.

## Exact result

`finitePF_of_sector_zero_free` states: if a real polynomial p has positive
constant coefficient and no complex zero with

\[
 |\arg z| < \frac{\pi r}{r+1},
\]

then its **ordinary** coefficient sequence is `FinitePF` through rank r.
Thus every arbitrary ordered minor through that rank is nonnegative.
There is no degree bound. The zero sector's boundary is included in the
allowed zero set, and roots need not be simple or have distinct moduli.

The equivalent root-location formulation is `finitePF_of_zero_sector`:
each complex root satisfies `pi - pi/(r+1) <= abs(arg z)`.
The proof also handles rank zero directly. Both statements use the actual
complex evaluation of the real polynomial, not an opaque sector certificate.

This matches [Katkova, p. 5, Theorem B](https://arxiv.org/pdf/math/0505174),
which attributes the polynomial result to Schoenberg's 1955 Palermo paper.
The source's printed PF44/angle-43*pi/44 mismatch remains untouched; applying
the proved formula to that angle gives the conservative rank 43.

## Arbitrary-minor quadratic proof

`Reinmann/QuadraticPF.lean` first proves
`arbitrary_minor_nonneg_of_tridiagonal` for arbitrary increasing integer row
and column selections of the symmetric Jacobi matrix with diagonal 2c and
adjacent entries 1. The proof is a strong induction on the selected size:

1. If the first selected row and column differ, the first row or first column
   has at most one nonzero entry. Expanding removes it and leaves a smaller
   ordered minor, multiplied by a nonnegative boundary entry.
2. If they agree, take the longest common consecutive prefix of the two
   selections. If it is the whole selection, the matrix is a contiguous
   tridiagonal block. Otherwise, one selection jumps at the first missing
   index, producing a zero off-diagonal rectangular block.
3. Simultaneously reindexing rows and columns splits the determinant into the
   prefix's Chebyshev determinant and a smaller arbitrary minor. There is no
   sign loss in this split.

The sine quotient then gives nonnegativity of all required blocks when
`0 <= phi <= pi/(r+1)`. The phi=0 case is proved separately using the
Chebyshev value at 1, so no division by sin(0) occurs. The upper angle is closed;
the largest permitted block may have determinant zero.

`finitePF_quadratic` transfers this result to the ordinary Toeplitz sequence
of `1 + 2*cos(phi)*X + X^2`, by an exact integer row shift. Positive variable
dilation preserves all minors by row and column powers, giving
`finitePF_scaled_quadratic`. `finitePF_conjugate_pair` then proves the actual
monic factor `X^2 - 2*re(z)*X + norm(z)^2` is PF-r whenever z is nonzero and
satisfies the closed sector bound. Its modulus is unrestricted.

## Assembly of general real polynomials

Mathlib's fundamental theorem of algebra supplies a root of every nonconstant
real polynomial viewed over the complex numbers. The sector excludes
nonnegative real roots. A real root gives a negative-root linear factor; a
non-real root gives the real conjugate quadratic divisor proved in Mathlib.
Each extracted factor has positive constant coefficient and positive degree.
The quotient inherits positive constant coefficient and the same root-sector
bound. Induction on degree, using the previously proved product closure,
therefore proves the result. Repeated roots are extracted repeatedly; no
genericity condition is introduced.

`finitePF_of_sector_polynomial_limit` composes this polynomial theorem with
the existing `AnalyticPFLimit` result. It permits unbounded approximant degrees
and asks for actual locally uniform convergence and the ordinary Taylor
identity of the target sequence. This is a general transfer theorem, not an
assertion that the necessary Xi approximants already exist in Lean.

## What remains for folded Xi

The general polynomial sector theorem, product closure, analytic limit passage,
positive Xi centre and `foldedXi_taylor` are proved. The remaining substantive
task is to identify the actual folded Xi function with its genus-zero zero
product, establish inverse-zero summability, and construct conjugation-stable
real polynomial approximants whose zeros inherit the sector bound. Generic
product convergence is already available, but does not identify its limit
with Xi. Target A's simple-zero and gap assumptions are not used here.

Neither `KatkovaSectorBridge 43` nor unconditional `finitePF43` is claimed.
The critical-strip angle theorem and the height-14.1 certificate retain their
existing interfaces. No height increase or RH claim is made.

## Verification and release

The fourteen public declarations in these two new modules have a separate
standard-axiom audit. Fresh source elaborations, explicit target build,
unchanged default build and root guard, and checksum-bound evidence are in
`verification_2026_10_20_polynomial_sector/`. The root import and its existing
1619-declaration audit remain unchanged. Warnings replayed from the older
Chebyshev module are preserved; the new source elaborations are checked
separately. No earlier manifest is rewritten.

Rebuild with `lake build Reinmann.PolynomialSectorPF`; replay the saved evidence
with `python3 experiments/prime_spectral/verify_polynomial_sector_pf.py`.
The latter is a receipt check, not a fresh build or hosted-CI assertion.

At preparation of this note, Target B's
[proof-source CI](https://github.com/sciencenerd-des/reinmann/actions/runs/39425081613)
still had a successful default job and a running numerical job. Its gated
table updates remain unapplied. Published versions remain unchanged.
