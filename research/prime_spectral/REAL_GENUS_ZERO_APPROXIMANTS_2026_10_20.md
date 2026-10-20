# Real genus-zero approximants and the conditional folded-Xi sector bridge

Three modules now construct the real polynomial approximants and assemble the
sector implication from explicit genus-zero product data. This discharges the
generic approximation construction left open in the polynomial-sector note.
It does not establish that the actual folded Xi function has the required
product representation, and does not prove `KatkovaSectorBridge 43` without
that input.

## Constructed approximants

Let `a : ι → ℂ` be nonzero indexed zeros, and let `sigma : ι → ι` be an
involution with `a (sigma i) = conj (a i)`. Assume

    Summable (fun i => ‖(a i)⁻¹‖).

For each finite index set s, close it under sigma and take the finite product
of `1 - X / a i`. `RealGenusZeroApproximants` proves that this complex
polynomial is the complexification of an actual real polynomial with constant
coefficient 1. Its complex evaluation is exactly the finite product, so real
coefficient extraction introduces no additional zeros. Extracting real parts
is not treated as a ring homomorphism.

Closing index sets under the involution is cofinal in the finite-set net. The
real polynomials therefore converge locally uniformly on the entire complex
plane to the infinite product. The construction permits repeated values of a,
real zeros fixed by sigma, and equal zero moduli. Indexed multiplicities are
retained; closing a finite set does not duplicate an index.

If every a i satisfies the closed sector inequality

    pi - pi / (r + 1) ≤ |arg (a i)|,

then the polynomial sector theorem proves PF-r for every approximant.
`finitePF_genusZero_product` passes this positivity to the product's ordinary
Taylor coefficients `iteratedDeriv n f 0 / n!`. A separate theorem proves these
coefficients have imaginary part zero. Positivity is derived from zero
locations, rather than assumed for the approximants. This concerns all ordered
Toeplitz minors through rank r, not just contiguous minors.

`finitePF_of_product_identity` transfers the result to an explicit real
coefficient sequence whenever `f(z) = C * product (1 - z/a i)`, C is nonnegative,
and the ordinary Taylor coefficient identity is supplied. No fixed-rank
reciprocal-PF transport is used.

## Squaring the strip geometry

`FoldedSectorGeometry.arg_square_sector` proves

    |Re v| ≤ |Im v| tan(theta)
      ⇒ pi - 2 theta ≤ |arg(v²)|

for nonzero v and `0 ≤ theta ≤ pi/4`. It uses cosine monotonicity on [0, pi]
and an exact squared-coordinate inequality, including the closed boundary.
`arg_folded_sector` specializes this to the existing `pfHalfAngle m` convention
for positive m and v = s - 1/2. This is elementary geometry; it asserts no zero
location by itself.

## Actual folded-Xi assembly, with the remaining inputs exposed

`XiGenusZeroSector.finitePF_xi_of_genusZero_product` specializes the generic
transfer to `foldedXi` and `XiMomentCoeff`. It reuses the already proved positive
constant coefficient and `foldedXi_taylor`; these are not new results here.
It still requires the exact identity

    foldedXi z = (XiMomentCoeff 0 : ℂ) * ∏' i, (1 - (a i)⁻¹ * z).

`katkovaSectorBridge_of_strip_indexed_product` additionally assumes that each
a i equals `(s i - 1/2)^2` for a critical-strip zero s i. The existing tangent
angle hypothesis supplies the sector inequality via the new geometry lemma,
which gives the named bridge under this explicit indexed-product data.

What remains is to construct that data for the actual folded Xi function:
the genus-zero canonical product identity with correct normalization,
inverse-zero summability, and a conjugation involution on an index set carrying
the required multiplicities and correspondence with critical-strip zeros.
The real approximants no longer need to be supplied separately. Assuming the
product identity is substantial; the conditional assembly does not prove it.

There are no simple-zero or strict-modulus-gap hypotheses in these modules.
Target A's separately proved split-pair theorem remains standalone. No
unconditional `finitePF43`, unbounded-rank PF, RH, or Green-form budget is
claimed. Height 14.1 and published versions are unchanged.

## Verification

The eighteen public theorems have a separate semantic audit against the
standard axioms `propext`, `Classical.choice`, and `Quot.sound`. Verification
includes fresh elaboration of each source file, the explicit
`Reinmann.XiGenusZeroSector` target, the default build, and the unchanged
1619-declaration root guard. These new modules remain outside the root import;
the separate audit is not part of that root count.

Evidence is stored in `verification_2026_10_20_real_approximants/`. Its verifier
replays the immutable polynomial-sector checkpoint and all its parent bindings,
then validates the new source, audit, command receipts, and checksums. Existing
manifests are not rewritten. Large build logs are losslessly compressed with
both compressed-file and uncompressed-output checksums retained.

Rebuild with `lake build Reinmann.XiGenusZeroSector`. Replay saved evidence with
`python3 experiments/prime_spectral/verify_real_genus_zero_approximants.py`.
Receipt replay alone is not a fresh Lean build or hosted-CI result.

At preparation, the default job of proof-source CI run 39425081613 had passed,
while its rectangle job was still running. The Target B table closeout remains
conditional on both jobs succeeding. These new modules are not covered by that
older proof-source run.
