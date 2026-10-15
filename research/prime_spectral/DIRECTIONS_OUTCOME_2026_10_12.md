# D1–D6: results, counterexamples and remaining theorems

The remaining directions have now been pursued with new full-operator certificates, a quantitative written theorem, and an actual Davenport–Heilbronn falsification. **They are not all solved.** In particular no all-support counting asymptotic, universal ordinate-only zero-free region, first negative Toeplitz minor, or effective-block induction is claimed.

All work is in the separate codex/xi-eigenvector-reduction worktree. The original checkout is unchanged by this continuation. The new evidence is under [verification_2026_10_12_remaining](verification_2026_10_12_remaining/manifest.json); earlier certificates retain their historical manifests.

| Direction | New outcome | Exact status |
|---|---|---|
| D1: whole-cluster certificate | Degree-32 C=3 trial, all action modes through 256 and a rigorous infinite tail; rank four with two modes in each parity; projector distance <0.425 | Improved fixed-support full certificate; growing-support uniformity and internal ground-state selection remain open |
| D2: count from the prime side | Unconditional full-operator identity \(N_3(0.1)=4\), while the proposed staircase gives 5 | Exact staircase refuted for this explicit near-zero threshold; \(2C+O(1)\) at an independently specified threshold remains unproved |
| D3: window/zero exchange | [Packet-dependent theorem](WINDOW_PACKET_THEOREM_2026_10_12.md), explicit support budget and infinite zeta-zero tail, interval calculator | Written theorem proved; cancellation constants have not been replaced by a function of one ordinate |
| D4: DH falsification | [Actual DH completion and form](DH_FALSIFICATION_2026_10_12.md): certified off-line zero, 6,400 positive solid minors, passing finite ground gates at C=13, negative full-form trial at C=31 | Negative witness and first degree in the fixed C=31 even family completed; first failing Toeplitz minor and smallest full negative support not found |
| D5: robustness note | [Existing C=3.2 note](ROBUSTNESS_OBSTRUCTION_C3P2_2026_10_12.md), radius upper bound \(8.112\,10^{-9}\) | Completed for all bounded self-adjoint norm perturbations; no impossibility theorem about exact or structured proofs |
| D6: exact one-direction induction | [Infinite positive/negative index of an active prime translation and exact Schur inertia identity](INERTIA_INDUCTION_OBSTRUCTION_2026_10_12.md) | Raw rank-one update ruled out; an arithmetic effective-block induction remains open |

## D1/D2: an improved full block and a threshold counterexample

[refine_cluster.py](../../experiments/prime_spectral/refine_cluster.py) integrates the actual C=3 Ritz matrices at degree 32 and 512 bits. It reuses the already validated containing-support comparison and the 256-mode sequence, checking their provenance. Interval inertia on the actual trial matrices and the full comparison gives
\[
 \lambda_3(A_3)<0.1<0.629<\lambda_4(A_3),
\]
with zero-based indices. Therefore precisely four full eigenvalues, two in each parity, are below 0.1. The upper and lower arguments include the full operator rather than only a finite compression.

The two lowest selected columns in each degree-32 parity block have second Ritz values approximately 0.00148665 (even) and 0.0921392 (odd). Exact decimal columns, Gram bounds, actual action through mode 256 and the analytic infinite residual tail give
\[
 \|P_3-\Pi_{32}\|<0.425.
\]
Here \(P_3\) is the full rank-four spectral projection and \(\Pi_{32}\) the normalized trial projection. The saved outward bound is about 0.42452548. The previous degree-16 bound was <0.531. Both use the outer gap, with no division by an internal near-zero gap.

The [new certificate](verification_2026_10_12_remaining/C3_N32_full_cluster.json) includes exact columns, full residual allowances, all inertia pivots and input/source hashes. Tests replay the full result and compare degree-32 diagonal/off-diagonal entries with independent geometric integrals.

Since \(\lfloor2(3)-7/4\rfloor+1=5\), the proposed exact formula cannot count this explicitly defined near-zero cluster. This does not disprove a leading \(2C\) asymptotic with a bounded error, nor a formula for some other precisely defined quantity. A moving threshold selected from the spectrum would need its own mathematical definition before an asymptotic claim becomes testable.

## What the negative control changes strategically

The DH completion has strictly positive ordinary coefficients at all orders, passes all tested solid minors through rank/shift 80, and has the finite simple/even/boundary gates needed for the generic real-zero construction. Nevertheless an independently certified off-line zero exists and the actual Weil form is negative on an explicit trial. The [falsification report](DH_FALSIFICATION_2026_10_12.md) distinguishes each tested hypothesis family and each unperformed port.

Thus the main arithmetic target is the growing-support **effective Schur block**, including its signed complementary resolvent correction. Finite spectral separation supplies a stable subspace but not the internal signs. Generic symmetry, coefficient positivity, prolate concentration and finite real-zero constructions do not identify the required Xi limit.

The most concrete next theorem for D3 is to control or replace the packet interpolation constant in the new bound, while retaining the explicit infinite tail. The most concrete next target for D6 is a relation between effective Schur blocks on two supports; support inclusion and prime activation themselves supply no finite-rank identity. Neither task is discharged by fitting a staircase to numerical eigenvalues.

## Reproduction

From this worktree, use Python 3.12 with python-flint==0.8.0, mpmath, and numpy:

~~~sh
uv run --with python-flint==0.8.0 --with mpmath --with numpy --python 3.12 python experiments/prime_spectral/refine_cluster.py
uv run --with python-flint==0.8.0 --with mpmath --with numpy --python 3.12 python experiments/prime_spectral/dh_weil_certificate.py --cutoff 31 --modes 60
uv run --with python-flint==0.8.0 --with mpmath --with numpy --python 3.12 python experiments/prime_spectral/dh_zero_and_gates.py
uv run --with python-flint==0.8.0 --with mpmath --with numpy --python 3.12 python experiments/prime_spectral/dh_toeplitz_scan.py
~~~

The bounded Toeplitz scan takes substantially longer than the local tests. The full lower comparison is a dependency of the cluster result, with its earlier replay retained; this batch does not claim a new complete independent regeneration of that comparison.

Fifteen new tests passed: eight DH controls, two refined-cluster checks, and five packet/tail checks. These are Python/Arb checks plus written analytic arguments. No new Lean theorem, all-support proof, novelty claim or RH proof is asserted.
