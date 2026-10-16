# Formal targets after the controls-paper release

The user explicitly placed these projects **after publication**. They are scoped here, not claimed implemented. The paper remains unpublished pending a human read. No new axiom, placeholder certificate hypothesis or `sorry` discharges either target.

## A. Finite-product split-pair theorem

Start with B(z)=product_j(1-lambda_j*z), nonzero distinct inverse zeros, a conjugation-invariant real polynomial, and positive inner product P. Prove the reciprocal coefficient identity h_n=sum_j c_j lambda_j^n, then the size-s complementary determinant expansion by Cauchy–Binet. The two dominant subsets contain all s-1 strictly larger inverse-zero moduli and one of a nonreal conjugate pair. Every Vandermonde/residue factor is nonzero.

Prove the normalized error bound by a finite sum of ratios with norm below 1. This avoids the entire-function Cauchy remainder in the first Lean target. The existing `ToeplitzQuadraticChebyshev.lean` and `WeilSchurInertia.lean` are neighboring finite-algebra precedents, not proofs of this new theorem.

A useful formal route avoids an irrational-rotation/density theorem altogether. Let u have modulus 1 with u neither1 nor -1, and let w have modulus 1. For x_n=Re(w*u^n), on any block of N terms,

- |sum x_n| <= 2/|1-u|;
- sum x_n² >= N/2 - 1/|1-u²|.

These follow from two finite geometric sums. If every x_n>=-c, then x_n²<=(1-c)x_n+c for -c<=x_n<=1. At c=1/4, this contradicts the two bounds whenever

    N > 4/|1-u²| + 6/|1-u|.

The corresponding inequality on [-1,c] also forces a term above+c. Thus every sufficiently long block contains phases of both signs bounded away from0, without splitting rational and irrational angles. Once the normalized determinant remainder is below half the leading margin, both determinant signs occur infinitely often. This is an elementary classical strategy, not a novelty claim; its hypotheses and constants require a Lean proof.

Acceptance: actual finite-product coefficient/determinant identity, explicit modulus ordering and nonvanishing, asymptotic decay and both sign conclusions; direct compilation, appropriate integration build and standard-axiom audit. A conditional theorem that merely assumes the desired two-term asymptotic is an intermediate lemma, not completion.

## B. Priority C: remove the low-zero named input

Current target in `Reinmann/QuasiRHInputs.lean:170`:

    ZetaNoLowStripZero (141/10)
    = forall s, IsCriticalStripZero s -> 14.1 <= |Im s|.

This supplies a classical input to both finite-PF theorems. It does not discharge `KatkovaSectorBridge` or RH.

1. Use the correct entire xi target, with a proved bridge from critical-strip zeta zeros. Mathlib's entire pole-subtracted completed-zeta function has a different zero set and cannot silently replace xi.
2. Reduce by conjugation/reflection if the existing formal bridges justify it; otherwise cover the whole closed rectangle 0<=Re(s)<=1, |Im(s)|<=14.1. Handle endpoints and pole-removal analytically.
3. Choose an evaluator with a **Lean-proved** remainder bound, for example the theta/Mellin representation with a finite rational enclosure and uniform tail. Arb pilots can select tile sizes, but their external receipts alone do not prove a Lean theorem.
4. Prove finite rectangle coverage and tile-wise zero exclusion, including cells near0,1 and the top edge. A sampled grid or a winding count without a proved zero-excluding boundary is insufficient.
5. Compose the zero-exclusion theorem with the target bridge and instantiate the two finite-PF theorems. Audit the resulting proof bodies; do not replace `ZetaNoLowStripZero` by another unproved certificate proposition.

Existing `XiMellinRemainder` work is branch-specific and has previously been recorded as unverified. Rerun its named direct compiler/build/axiom checks before relying on it. No low-rectangle certificate or new Lean theorem was produced in the controls calibration round.
