# RH Theorem Targets from the Current Knowledge Base

**Status:** theorem-target map, not a proof of RH.

The current program now has three explicit levels.  This keeps the work honest:
we can push hard toward RH without confusing partial positivity with the full
Pólya-frequency statement that would actually close the problem.

## Level 1: Order-3 frontier

Lean target:

- `Order3FrontierTheorem`
- `xiToeplitzOrder3Positive_of_order3Frontier`
- `xiToeplitzOrder3Positive_of_order3CrossField`

Mathematical meaning:

Prove the first Toeplitz determinant beyond the known Turán/order-2 rung.  The
candidate sources are combinatorial Hodge theory, Lorentzian polynomial
coefficients, lattice-path total positivity, Weil/Hodge positivity models,
Euclidean convexity inequalities, or hyperbolic spectral trace formulas.

This would be genuine progress, but it would not solve RH by itself.

## Level 2: Contiguous all-order kernel positivity

Lean target:

- `KernelContigTotalPositive`
- `XiContigToeplitzTotalPositive`
- `xiContigToeplitzTotalPositive_iff_kernelContig`
- `xiContigToeplitzTotalPositive_of_kernelContigWitness`

Mathematical meaning:

Prove every contiguous factorial-weighted moment Toeplitz determinant coming
from Polya's xi-kernel.  This is much stronger than order 3 and would give a
coherent analytic/combinatorial ladder.

This is still not the full Edrei-ASW Pólya-frequency condition, because RH needs
arbitrary Toeplitz minors, not only contiguous blocks.

## Level 2.5: Contiguous-to-full PF upgrade

Lean target:

- `XiContigToFullPFBridge`
- `XiArbitraryMinorReductionToContig`
- `XiMinorContigCertificate`
- `XiAllMinorContigCertificates`
- `xiToeplitzEntry_nonneg_of_contig`
- `XiMomentCoeffNonnegativeFromContig`
- `xiMomentCoeffNonnegative_of_contig`
- `XiMomentCoeffPositive`
- `xiMomentCoeffPositive_of_kernelRep`
- `xiMinorZeroContigCertificate`
- `exists_xiMinorZeroContigCertificate`
- `xiContiguousMinorSelfCertificate`
- `exists_contiguousMinorSelfCertificate`
- `xiMinorOneContigCertificate`
- `exists_xiMinorOneContigCertificate`
- `xiZeroSupportMinorCertificate`
- `exists_xiZeroSupportMinorCertificate`
- `xiZeroRowMinorCertificate`
- `exists_xiZeroRowMinorCertificate`
- `xiZeroColumnMinorCertificate`
- `exists_xiZeroColumnMinorCertificate`
- `xiMinorTwoUpperRightZeroCertificate`
- `exists_xiMinorTwoUpperRightZeroCertificate`
- `XiMinorTwoFullSupportFromContig`
- `XiMinorTwoGapInequalityFromContig`
- `XiMomentRatioMongeFromContig`
- `XiMomentAdjacentRatioMongeFromContig`
- `XiMomentUnitRatioMongeFromContig`
- `xiMomentUnitRatioMonge_of_contig`
- `two_step_ratio_cancel`
- `XiMomentAdjacentRatioGap`
- `xiMomentAdjacentRatioGap_one_of_contig`
- `XiMomentAdjacentRatioGapSuccBridge`
- `xiMomentAdjacentRatioGapSuccBridge_of_strictPositivity`
- `xiMomentAdjacentRatioMonge_of_gapSuccBridge`
- `XiUnitRatioToAdjacentRatioBridge`
- `XiUnitRatioToAdjacentRatioWithPositivityBridge`
- `xiUnitRatioToAdjacentRatioBridge_of_withPositivity`
- `XiUnitRatioToAdjacentRatioWithStrictPositivityBridge`
- `xiUnitRatioToAdjacentRatioWithStrictPositivityBridge_of_gapInduction`
- `xiUnitRatioToAdjacentRatioBridge_of_strictPositivity`
- `xiUnitRatioToAdjacentRatioBridge_of_kernelRep`
- `xiMomentAdjacentRatioMonge_of_unitBridge`
- `xiMomentAdjacentRatioMonge_of_kernelRep`
- `XiUnitRatioRoute`
- `xiMomentAdjacentRatioMonge_of_unitRoute`
- `two_step_ratio_cancel_general`
- `XiAdjacentRatioToGlobalRatioBridge`
- `XiMomentRatioDistanceFromAdjacent`
- `xiMomentRatioDistance_zero`
- `xiMomentRatioDistance_succ_of_adjacent_strictPositivity`
- `xiMomentRatioMonge_of_adjacentRatio_strictPositivity`
- `XiAdjacentRatioToGlobalRatioWithStrictPositivityBridge`
- `xiAdjacentRatioToGlobalRatioWithStrictPositivityBridge_of_distanceInduction`
- `xiAdjacentRatioToGlobalRatioBridge_of_kernelRep`
- `xiMomentRatioMonge_of_adjacentRatioBridge`
- `xiMomentRatioMonge_of_kernelRep`
- `XiAdjacentRatioRoute`
- `xiMomentRatioMonge_of_adjacentRatioRoute`
- `xiMinorTwoGapInequalityFromContig_of_ratioMonge`
- `xiMinorTwoGapInequalityFromContig_of_kernelRep`
- `xiMinorTwoFullSupportFromContig_of_gapInequality`
- `xiMinorTwoFullSupportFromContig_of_kernelRep`
- `xiMinorTwoFullSupportCertificate`
- `exists_xiMinorTwoFullSupportCertificate`
- `exists_xiMinorTwoContigCertificate_of_kernelRep`
- `XiAllMinorGeThreeContigCertificates`
- `XiMinorThreeContigCertificates`
- `XiAllMinorGeFourContigCertificates`
- `xiAllMinorGeThree_of_three_and_geFour`
- `xiAllMinorContigCertificates_of_kernelRep_and_geThree`
- `arbitraryMinorReduction_of_allMinorContigCertificates`
- `xiContigToFullPFBridge_of_allMinorContigCertificates`
- `xiContigToFullPFBridge_of_kernelRep_and_geThree`
- `xiContigToFullPFBridge_of_kernelRep_three_and_geFour`
- `xiContigToFullPFBridge_iff_arbitraryMinorReduction`
- `KernelContigToPFTheorem`
- `KernelContigToPFGeThreeTheorem`
- `KernelContigToPFThreeAndGeFourTheorem`
- `kernelContigToPF_of_geThree`
- `kernelContigToPFGeThree_of_three_and_geFour`
- `xiToeplitzTotalPositive_of_kernelContigToPF`
- `xiToeplitzTotalPositive_of_kernelContigToPFGeThree`
- `xiToeplitzTotalPositive_of_kernelContigToPFThreeAndGeFour`
- `riemannHypothesis_of_kernelContigToPF`
- `riemannHypothesis_of_kernelContigToPFGeThree`
- `riemannHypothesis_of_kernelContigToPFThreeAndGeFour`

Mathematical meaning:

This is the next named wall.  If we prove all contiguous kernel determinants,
we still need a theorem upgrading that structured positivity to arbitrary
Toeplitz minors:

```text
XiContigToeplitzTotalPositive -> XiToeplitzTotalPositive
```

For arbitrary sequences this should not be assumed.  The only honest version is
an xi-specific theorem, probably using additional structure from Polya's kernel,
factorial weighting, a planar network model, or a variation-diminishing operator.

The bridge now has a local equivalent:

```text
XiArbitraryMinorReductionToContig
```

This says that every arbitrary Toeplitz minor has a proof of nonnegativity from
the contiguous-minor ladder.  It is the right loop target because it can be
attacked one row/column pattern at a time.  A future proof could come from:

- a Cauchy-Binet factorization into contiguous blocks;
- a planar-network path matrix whose Lindstrom-Gessel-Viennot determinant is the
  target minor;
- a variation-diminishing operator that upgrades interval minors to arbitrary
  minors for this specific xi coefficient sequence.

The bridge now also has a certificate layer:

```text
XiAllMinorContigCertificates -> XiArbitraryMinorReductionToContig
```

Each `XiMinorContigCertificate k rows cols hRows hCols` is a local proof object
for one arbitrary minor.  This is the next practical loop: build certificates
for concrete row/column patterns, detect the common algebraic shape, and then
generalize to all strictly monotone patterns.

The certificate program now has a verified base case:

```text
xiContiguousMinorSelfCertificate
```

For row pattern `rows i = m + i` and column pattern `cols j = j`, the certificate
is immediate from `XiContigToeplitzTotalPositive`.  This does not solve the
arbitrary-minor upgrade.  It marks the boundary: contiguous interval patterns
are solved by definition, and the next certificates must handle non-contiguous
row or column gaps.

The program now also has a verified arbitrary `1 x 1` certificate:

```text
xiMinorOneContigCertificate
```

For any single row and single column, either the Toeplitz entry is zero because
the column lies above the lower-triangular support, or it is the contiguous
`1 x 1` minor at offset `row - col`.  This closes the full arbitrary-minor
certificate problem in size `1`.  The next real certificate family is size `2`
with non-contiguous row or column gaps.

The program also has an arbitrary-size zero-support certificate:

```text
xiZeroSupportMinorCertificate
```

If every selected column lies strictly above every selected row, then every
entry in the lower-triangular Toeplitz submatrix is zero, so the determinant is
zero.  This closes the completely unsupported arbitrary-minor family.  The next
frontier is therefore the mixed-support case: non-contiguous `2 x 2` minors
where at least one entry is nonzero but the pattern is not a contiguous block.

This has been strengthened to a zero-row certificate:

```text
xiZeroRowMinorCertificate
```

If even one selected row lies strictly below every selected column, that row is
zero and the determinant is zero.  This closes a larger arbitrary-size family
than the all-zero-support case.  The next frontier is mixed-support minors with
no zero row, starting at non-contiguous `2 x 2` patterns.

The symmetric zero-column family is also verified:

```text
xiZeroColumnMinorCertificate
```

If one selected column lies strictly above every selected row, that column is
zero and the determinant is zero.  The remaining certificate frontier is now
mixed-support minors with no zero row and no zero column, starting at
non-contiguous `2 x 2` patterns.

The first mixed-support `2 x 2` family is now verified:

```text
xiMinorTwoUpperRightZeroCertificate
```

The auxiliary lemma `xiToeplitzEntry_nonneg_of_contig` proves every individual
Toeplitz entry is nonnegative from the contiguous `1 x 1` ladder.  Therefore,
if the upper-right entry of a `2 x 2` minor is zero, the determinant reduces to
the product of the two diagonal entries and is nonnegative.

The remaining `2 x 2` frontier is the genuinely full-support case where all
four selected Toeplitz entries are nonzero and the pattern is not a contiguous
block.  That is where a real variation-diminishing, planar-network, or
Cauchy-Binet certificate must enter.

That frontier is now named:

```text
XiMinorTwoFullSupportFromContig
```

It states that for every full-support `2 x 2` arbitrary Toeplitz minor,
contiguous positivity implies determinant nonnegativity.  Lean verifies that
this condition supplies local certificates via:

```text
xiMinorTwoFullSupportCertificate
```

So the loop has reduced the remaining `2 x 2` frontier to one exact theorem
target.  The next push is to prove or further decompose
`XiMinorTwoFullSupportFromContig`.

The determinant target is now decomposed into an explicit four-index inequality:

```text
XiMinorTwoGapInequalityFromContig
```

For rows `r0 < r1` and columns `c0 < c1` with full lower-triangular support
`c1 <= r0`, it asks for:

```text
XiMomentCoeff (r0 - c1) * XiMomentCoeff (r1 - c0)
  <= XiMomentCoeff (r0 - c0) * XiMomentCoeff (r1 - c1)
```

Lean verifies:

```text
XiMinorTwoGapInequalityFromContig -> XiMinorTwoFullSupportFromContig
```

This is now the sharp algebraic `2 x 2` condition to prove or decompose next.

The four-index inequality is now reduced to a sequence-level ratio-Monge target:

```text
XiMomentRatioMongeFromContig
```

For every `a <= b` and positive gap `d`, it asks:

```text
XiMomentCoeff a * XiMomentCoeff (b + d)
  <= XiMomentCoeff (a + d) * XiMomentCoeff b
```

This is the no-division version of saying the ratio
`XiMomentCoeff (n + d) / XiMomentCoeff n` decreases with `n`.  Lean verifies:

```text
XiMomentRatioMongeFromContig -> XiMinorTwoGapInequalityFromContig
```

The next proof attempt should attack this ratio-Monge property directly, or
decompose it into adjacent ratio monotonicity plus positivity.

That adjacent decomposition is now named:

```text
XiMomentAdjacentRatioMongeFromContig
XiAdjacentRatioToGlobalRatioBridge
```

The adjacent condition asks only for:

```text
XiMomentCoeff n * XiMomentCoeff (n + 1 + d)
  <= XiMomentCoeff (n + d) * XiMomentCoeff (n + 1)
```

for every `n` and positive gap `d`.  The propagation bridge is separated because
turning adjacent cross-multiplied inequalities into the global ratio-Monge
statement needs positivity/control of intermediate coefficients.  Lean verifies:

```text
XiAdjacentRatioRoute -> XiMomentRatioMongeFromContig
```

The next proof attempt should either prove the adjacent inequality from the
contiguous ladder or prove the propagation bridge from entry positivity plus
adjacent inequality.

The unit-gap adjacent inequality is now solved:

```text
xiMomentUnitRatioMonge_of_contig
```

It is exactly the contiguous `2 x 2` Toeplitz/Turan rung:

```text
XiMomentCoeff n * XiMomentCoeff (n + 2)
  <= XiMomentCoeff (n + 1) * XiMomentCoeff (n + 1)
```

The next bridge is now named:

```text
XiUnitRatioToAdjacentRatioBridge
```

It asks for the propagation from the proved unit-gap inequality to arbitrary
positive gap `d` in the adjacent condition.  Lean verifies:

```text
XiUnitRatioRoute -> XiMomentAdjacentRatioMongeFromContig
```

So the sequence-theoretic frontier has moved from proving the base Turan
inequality to proving that unit-gap ratio monotonicity propagates across longer
gaps.

The propagation bridge is now refined to include the positivity actually needed
for chaining:

```text
XiMomentCoeffNonnegativeFromContig
XiUnitRatioToAdjacentRatioWithPositivityBridge
```

Lean proves `XiMomentCoeffNonnegativeFromContig` from contiguous `1 x 1`
minors via:

```text
xiMomentCoeffNonnegative_of_contig
```

and verifies:

```text
XiUnitRatioToAdjacentRatioWithPositivityBridge
  -> XiUnitRatioToAdjacentRatioBridge
```

So the next target is now sharper: prove that nonnegative coefficients plus the
unit-gap Turan/log-concavity inequality propagate to arbitrary positive gaps in
the adjacent-ratio inequality.

There is also a stricter kernel-backed route:

```text
XiMomentCoeffPositive
xiMomentCoeffPositive_of_kernelRep
XiUnitRatioToAdjacentRatioWithStrictPositivityBridge
```

Pólya's positive-kernel representation supplies strict positivity of all signed
moment coefficients.  Lean verifies:

```text
XiMomentKernelRep
  -> XiUnitRatioToAdjacentRatioWithStrictPositivityBridge
  -> XiUnitRatioToAdjacentRatioBridge
```

This strict-positivity route is now solved at the sequence-algebra level.

The propagation target has now been decomposed one more level into fixed-gap
induction:

```text
XiMomentAdjacentRatioGap d
XiMomentAdjacentRatioGapSuccBridge
```

Lean verifies the base case:

```text
xiMomentAdjacentRatioGap_one_of_contig : XiMomentAdjacentRatioGap 1
```

and also verifies the algebraic cancellation step:

```text
two_step_ratio_cancel
```

This lemma says that from

```text
A * B <= C * D
C * E <= B * B
0 <= A, 0 <= B, 0 < C
```

one may conclude:

```text
A * E <= B * D
```

That cancellation closes the gap-successor theorem under strict positivity:

```text
xiMomentAdjacentRatioGapSuccBridge_of_strictPositivity
```

Consequently Lean now verifies:

```text
XiMomentKernelRep -> XiMomentAdjacentRatioMongeFromContig
```

via:

```text
xiMomentAdjacentRatioMonge_of_kernelRep
```

The next bridge was:

```text
XiAdjacentRatioToGlobalRatioBridge
```

That bridge is now also solved under strict positivity.  The proof introduces a
distance-indexed form:

```text
XiMomentRatioDistanceFromAdjacent k
```

and proves:

```text
xiMomentRatioDistance_zero
xiMomentRatioDistance_succ_of_adjacent_strictPositivity
xiMomentRatioMonge_of_adjacentRatio_strictPositivity
```

The algebraic engine is the more general no-division cancellation lemma:

```text
two_step_ratio_cancel_general
```

Consequently Lean now verifies:

```text
XiMomentKernelRep -> XiMomentRatioMongeFromContig
```

via:

```text
xiMomentRatioMonge_of_kernelRep
```

and therefore also verifies the explicit four-index full-support `2 x 2`
inequality:

```text
XiMomentKernelRep -> XiMinorTwoGapInequalityFromContig
```

via:

```text
xiMinorTwoGapInequalityFromContig_of_kernelRep
```

The determinant-form full-support `2 x 2` target is then immediate:

```text
XiMomentKernelRep -> XiMinorTwoFullSupportFromContig
```

via:

```text
xiMinorTwoFullSupportFromContig_of_kernelRep
```

The `2 x 2` full-support certificate frontier is no longer the main obstacle
once `XiMomentKernelRep` is available.  The next honest frontier is the general
arbitrary-minor upgrade for sizes `k >= 3`: find a certificate family or
structure theorem that turns contiguous positivity plus the xi kernel
representation into all arbitrary Toeplitz minors.

That frontier is now named directly:

```text
XiAllMinorGeThreeContigCertificates
```

Lean verifies the low-size closure:

```text
exists_xiMinorZeroContigCertificate
exists_xiMinorOneContigCertificate
exists_xiMinorTwoContigCertificate_of_kernelRep
```

and therefore verifies:

```text
XiMomentKernelRep
  -> XiAllMinorGeThreeContigCertificates
  -> XiAllMinorContigCertificates
```

via:

```text
xiAllMinorContigCertificates_of_kernelRep_and_geThree
```

This plugs into the full PF bridge:

```text
XiMomentKernelRep
  -> XiAllMinorGeThreeContigCertificates
  -> XiContigToFullPFBridge
```

via:

```text
xiContigToFullPFBridge_of_kernelRep_and_geThree
```

The sharper RH-closing bundled target is now:

```text
KernelContigToPFGeThreeTheorem
```

It asks for:

1. Pólya kernel representation with positive kernel moments;
2. all contiguous kernel Toeplitz determinants;
3. arbitrary-minor certificates only for sizes `k >= 3`.

Lean verifies:

```text
KernelContigToPFGeThreeTheorem -> XiToeplitzTotalPositive
KernelContigToPFGeThreeTheorem -> RiemannHypothesis
```

via:

```text
xiToeplitzTotalPositive_of_kernelContigToPFGeThree
riemannHypothesis_of_kernelContigToPFGeThree
```

The `k >= 3` frontier has now been split into the first concrete unsolved rung
and the remaining tail:

```text
XiMinorThreeContigCertificates
XiAllMinorGeFourContigCertificates
```

Lean verifies:

```text
XiMinorThreeContigCertificates
  -> XiAllMinorGeFourContigCertificates
  -> XiAllMinorGeThreeContigCertificates
```

via:

```text
xiAllMinorGeThree_of_three_and_geFour
```

and therefore verifies the sharper bridge:

```text
XiMomentKernelRep
  -> XiMinorThreeContigCertificates
  -> XiAllMinorGeFourContigCertificates
  -> XiContigToFullPFBridge
```

via:

```text
xiContigToFullPFBridge_of_kernelRep_three_and_geFour
```

The newest RH-closing bundle is:

```text
KernelContigToPFThreeAndGeFourTheorem
```

Lean verifies:

```text
KernelContigToPFThreeAndGeFourTheorem -> XiToeplitzTotalPositive
KernelContigToPFThreeAndGeFourTheorem -> RiemannHypothesis
```

via:

```text
xiToeplitzTotalPositive_of_kernelContigToPFThreeAndGeFour
riemannHypothesis_of_kernelContigToPFThreeAndGeFour
```

The active loop target is now `XiMinorThreeContigCertificates`: prove every
`3 x 3` arbitrary Toeplitz minor has a local certificate from the contiguous
ladder and xi-kernel structure.  The tail condition `XiAllMinorGeFour...` keeps
the full RH route honest while the first remaining rung is attacked.

With classical scaffolding, Lean now verifies:

```text
KernelContigToPFTheorem -> RiemannHypothesis
```

So this is a complete RH route if the two mathematical payloads are proved:

1. every contiguous kernel Toeplitz determinant is nonnegative;
2. contiguous positivity upgrades to full arbitrary-minor PF for this xi
   sequence.

## Level 3: Full arbitrary-minor PF positivity

Lean target:

- `CrossFieldPFWitness`
- `xiToeplitzTotalPositive_of_crossFieldPFWitness`
- `riemannHypothesis_of_crossFieldPFWitness`

Mathematical meaning:

Any successful route must prove the full arbitrary-minor Pólya-frequency
condition for the signed xi coefficients:

```text
XiToeplitzTotalPositive
```

Given the classical scaffolding already isolated in `ClassicalToeplitzScaffolding`
(Edrei-ASW, Laguerre-Polya closure, Polya-Jensen, and the classical RH-to-PF
converse), Lean verifies:

```text
CrossFieldPFWitness -> RiemannHypothesis
```

This is the current honest success condition for fully solving RH inside this
program.

## Best next mathematical push

The most promising route is still combinatorics:

1. Try to realize the factorial-weighted moment sequence
   `M n / (2n)!` as a coefficient sequence of a Lorentzian or strongly
   log-concave object.
2. Upgrade the order-3 determinant to all contiguous determinants using a
   lattice-path or planar network model.
3. Prove `XiArbitraryMinorReductionToContig`, equivalently
   `XiContigToFullPFBridge`, the xi-specific theorem that upgrades contiguous
   minors to arbitrary Toeplitz minors.

The third step is the likely RH-hard wall.  It is now named precisely rather
than hidden inside broad language like "use combinatorics" or "use geometry."
