# Two explicit Xi evaluators and reflection majorants, 18 October 2026

`7376a2336c3fe9cceaa137b247962dde3ecfc6a3` is pushed and its
[CI run passes](https://github.com/sciencenerd-des/reinmann/actions/runs/39113141784).
The standalone formalization preprint is now published, explicitly unreviewed:
[10.5281/zenodo.23449490](https://doi.org/10.5281/zenodo.23449490).

The Arb comparison favors Euler–Maclaurin with shifted Stirling for the finite
arithmetic. Its complete external hard tile takes about 0.66 ms. **A complete
Lean hard tile remains unproved and untimed.** Neither the new Gamma component
nor the Arb measurements discharge `ZetaNoLowStripZero (141/10)`.

## Matched evaluator comparison

Both implementations evaluate Xi at 1/2+14i, with ordinary s-Taylor coefficients
through degree 16, using 192-bit Arb arithmetic. Accuracy includes the Euclidean
radius of each complex coefficient box, not just its real-component radius.
Each timing below is the median of seven runs. All 17 coefficients overlap an
independent builtin Gamma/zeta-series reference. The explicit evaluators do not
call those special functions to calculate their point jets.

| Evaluator | Parameters | Median | Largest complex coefficient radius |
| --- | --- | ---: | ---: |
| Mellin Taylor models | 20 panels, degree 8, 3 theta terms | 4.07 ms | 1.52e-6; fails target |
| Mellin Taylor models | 20 panels, degree 12, 3 theta terms | 6.03 ms | 2.66e-10 |
| Mellin Taylor models | 20 panels, degree 16, 3 theta terms | 7.99 ms | 5.41e-14 |
| Euler–Maclaurin / shifted Stirling | 10 terms, 4 zeta corrections | 0.57 ms | 6.71e-7; fails target |
| Euler–Maclaurin / shifted Stirling | 10 terms, 6 zeta corrections | 0.58 ms | 1.92e-9 |
| Euler–Maclaurin / shifted Stirling | 10 terms, 8 zeta corrections | 0.64 ms | 1.12e-11 |

The matched target is absolute complex coefficient error below 1e-8. These are
normalized Taylor coefficients, not unnormalized derivatives. The raw seven-run
timings and exact interval outputs are retained in `comparison.json`.

### Taylor-model Mellin implementation

On each real integration panel [c-h,c+h], expand each of the 17 weighted
integrands in t through degree k. Integrate every polynomial monomial exactly;
odd monomials vanish. A Cauchy bound on the complex t-disk of radius c/2 controls
the remainder. With q=h/(c/2), its integral error is at most

    2h M_j q^(k+1) / ((k+2)(1-q)).

Here M_j bounds the whole complex disk, including the imaginary phase of the
power t^(-3/4±7i) and the log(t)^j weight. It is not a point-sampling error
estimate. Panels have h/c at most 1/16. The integral ends at 12; a uniform
analytic tail bound on the unit s-disk controls every remaining jet coefficient.
The three-term theta truncation has its own uniform bound. Multiplication by
s(s-1)/2 and addition of 1/2 produce the actual Xi jet.

This replaces the earlier range-quadrature pilot's millions-of-panels projection
with 20 panels. A Lean proof of this Taylor-model integrator and its jet bridge
has not been supplied by the external experiment.

### Euler–Maclaurin / Gamma implementation

Use the finite sum n=1,...,10, the integral and endpoint corrections at N=11,
and Bernoulli corrections. A periodic-Bernoulli remainder bound is uniform on
the unit s-disk; Cauchy's estimate bounds all 17 normalized coefficient errors.
For Gamma(s/2), shift by 12 and evaluate log-Gamma's Stirling expansion with
seven retained Bernoulli terms. The first omitted term times the complex-sector
secant factor bounds the log error. A finite rectangle bound on the approximant
then controls the Gamma error before multiplying the series.

The primary algorithmic reference is Johansson's
[rigorous Hurwitz-zeta and derivative computation](https://arxiv.org/abs/1309.2877).
The complex log-Gamma remainder is described in
[DLMF 5.11(ii)](https://dlmf.nist.gov/5.11#ii). These are classical numerical
methods; no algorithmic novelty is claimed.

The point jet uses 14 series exp/log model calls, compared with 120 in the
20-panel Mellin implementation. Scalar logarithms, finite powers, rational
Bernoulli arithmetic, convolutions and remainder checks still have costs.
This count is a proxy for elementary-model demand, **not a measured number of
Lean-certified operations**. The timing ratio does not establish a Lean runtime.

The selected complete external tile uses the eight-correction zeta variant,
radius 1/16, and the already proved coarse unit-circle majorant 1000. Its
derivative bound is about 0.001721113 and its positive nonvanishing margin is
about 9.37e-5. The median total external tile time is 0.66 ms, including the jet,
explicit remainder checks, derivative-tail bound and margin check. A tighter
majorant is not needed for this external degree-16 tile.

## Correct reflection argument

Reflection gives a product identity. An upper bound on its second factor cannot
be divided out to obtain an upper bound on its first factor. The additional
one-sided ingredient is a Beta-integral comparison to a real-part anchor.

`Reinmann/GammaReflectionMajorant.lean` proves eight public theorems, including:

- the real Beta-integral norm comparison and Gamma quotient bound;
- the resulting one-sided shifted-anchor Gamma bound;
- the genuine reflection norm-product identity;
- |Gamma(1/2+iy)|² = pi/cosh(pi y);
- |Gamma(1+iy)|² = pi |y|/|sinh(pi y)| for y != 0;
- the explicit half-line exponential bound
  |Gamma(1/2+iy)|² <= 2 pi exp(-pi |y|).

The Beta comparison is adapted with attribution from OpenAI math's
`GammaBetaComparison.lean`, blob `9d30e92d96e42bc7b996799d87acab1bf3ead172`,
under its verified Apache-2.0 license. It supplies the missing one-sided control;
the product identity alone does not.

An external interval-arc calculation folds the unit circle about 1/2+14i into
Re(s)>=1/2 using the Xi symmetries. It combines the Beta comparison, exact anchor
norms and a finite EM zeta enclosure. On 1,024 arcs it gives

    reflection/Beta Xi majorant: 0.012492650361
    shift-product Xi majorant:   0.016654434071
    finite EM zeta norm bound:   0.809996200438

The Gamma identity/comparison theorems are proved in Lean. The numerical real
Gamma enclosures and EM zeta remainder used for this small Xi majorant are
external. A uniform numerical Lean strip majorant remains open.

## Library audit and remaining formal work

The Mathlib v4.30.0 `Stirling.lean` file concerns real factorial asymptotics and
real bounds. The source searches did not identify an explicit zeta
Euler–Maclaurin or complex log-Gamma remainder matching this evaluator.
OpenAI code searches for `EulerMaclaurin`, `Maclaurin` and `periodicBernoulli`
returned no matches at audit time. Relevant files referring to vertical Stirling
growth were inspected: `HeckeCompletedOrder`, `HeckeDualContour` and
`AngularDualContour` package those growth statements as conditional inputs;
they do not discharge the numerical remainder. The audit is scoped, not an
assertion that every file in either library has been read.

The arithmetic preference is EM/Stirling. Its remaining critical path is:

1. Prove the zeta EM identity and explicit analytic remainder, including its
   extension to the unit disk around the hard center.
2. Prove a complex Gamma evaluation remainder, not merely a Gamma norm bound.
3. Connect the finite exp/log/power/Bernoulli calculation and normalized jets to
   the actual functions; replay the numerical arithmetic in the kernel.
4. Assemble and time a complete Lean hard tile. Only then estimate 35 tiles.

No placeholder remainder axiom or conditional numerical result has been called
a completed tile. The alternate Mellin route is retained as a measured fallback.

## Publication and verification

The five-page formalization preprint adds ASW (1952), Horn–Johnson and a primary
Jacobi-identity reference; its appendix pins the 364-theorem source snapshot and
successful CI run. It cites the published DH controls as motivation and explicitly
requires a future Lean-certified atlas for a formal DH application. All five
pages were rendered and visually inspected. The paper and source supplement were
downloaded and checksum-verified before publication. The four public files were
then independently downloaded and verified. It is a Zenodo release, not an arXiv
submission or a peer-reviewed publication.

The current new Gamma module has local verification: full build (3,599 jobs),
372-declaration standard-axiom audit, and no unfinished proofs or project axioms.
CI run 39113141784 covers the pinned 364-theorem source snapshot, not the later
Gamma module. The old published DH scientific files and historical manifests
remain unchanged. The Liu note is unposted, and no stopped research track was
resumed.

Reproduce the Arb comparison and majorant:

```sh
uv run --offline --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/xi_evaluator_comparison.py --output tmp/xi-evaluator-replay/comparison.json
uv run --offline --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/xi_reflection_majorant.py --output tmp/xi-evaluator-replay/majorant.json
lake build
bash scripts/verify_axiom_clean.sh
python3 experiments/prime_spectral/verify_evaluator_comparison_round.py
```
