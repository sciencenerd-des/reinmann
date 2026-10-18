# Analytic split-pair assembly and hard-tile decision, 18 October 2026

The standalone entire-function split-pair theorem and its actual Taylor-series
Toeplitz--Jacobi bridge compile. The height-14 evaluator has a certified integral
panel, but no certified complete hard tile or measured full-tile runtime. The
current range-quadrature implementation is not a practical scaling method.
Neither result proves RH or the low zero-free rectangle.

## Completed formal assembly

`Reinmann/AnalyticSplitPair.lean` combines the constructed simple-pole remainder,
actual reciprocal coefficient identity, repeated-pole cancellation and mixed-row
estimate with finite dominant-pair oscillation. Its boundary theorem derives all
subset-product gaps from a top-modulus set with one isolated conjugate tie.
The perturbation and nonzero leading coefficient are proved consequences, not
new hypotheses. The geometric-sum argument gives both signs at arbitrarily large
indices, with no irrational-rotation assumption.

`Reinmann/AnalyticToeplitzJacobi.lean` proves ordinary Taylor convolution from
Leibniz's rule, derives the reciprocal series identity from analytic functions,
and applies the complementary determinant identity. For F(0)=1 and coefficients
mu of F(-z), the size-s reciprocal determinant at index n equals the original
size-(n+s-1), shift-s minor (s is positive in the oscillation theorem).
`entire_original_both_signs` transfers both signs to these actual original minors.

The hypotheses include an entire real-type function, distinct simple selected
zeros, coverage of all zeros in a closed disk, a split pair strictly inside its
radius, a nonreal dominant product and a unique cross-boundary modulus tie.
General multiplicities and cross-boundary ties are not handled. The theorem is
standalone, and the PF-to-RH bridges and their dependencies are unchanged.
Genus-zero functions are applications; no general canonical-product factorization
is claimed to have been formalized.

`Reinmann/GammaHeightMajorant.lean` proves a finite-shift Gamma bound retaining
the full denominator product, a height-only specialization, and a bound for the
actual Xi product. The Xi bound explicitly retains the actual zeta norm. A proved
uniform small numerical strip majorant still needs the zeta and real Gamma factors
enclosed. The external 0.004543 bound below does not fill that Lean obligation.

The integral comparison is adapted from OpenAI math's
`GammaElementaryGrowth.lean`, Git blob
`362a26a92faefda3dcc04466bb6bb2e99c71d7a5`. The two related Gamma growth files
inspected in this round supply qualitative estimates with existential constants,
not the desired directly usable height-14 numerical bound. Source references are
saved in the round's `gamma_sources.jsonl`; this is not a claim about all files in
that library.

## Hard-center evidence and decision

At center 1/2+14i, an external 192-bit Arb degree-16 jet and a cover of the entire
unit circle by 1,024 interval arcs give an upper majorant 0.004542519505776.
The proposed radius 1/16 tile has positive external margin about 9.27e-5 with a
center error budget 1e-6. This is an Arb computation, not a Lean jet or tile proof.

`research/prime_spectral/hard_tile_2026_10_18/PanelBenchmark.lean` proves actual
integral bounds on [1,1025/1024] for all 17 first-theta-term weighted integrands,
in both real and imaginary components. The interval exp/log/trig rules cover
every point in the panel. The numerical box-width assertion is reduced in Lean's
kernel. The three audited panel declarations have only the standard foundational
axioms. The fixture uses an isolated pinned LeanCert thin API, without changing
the project's dependency files.

| Quantity | Measured result / status |
| --- | --- |
| Panel elaboration, all 17 weights and both components | 18.9317 s |
| Import-only baseline in a separate process | 15.6213 s |
| Full Lean Xi jet at 1/2+14i | Not certified |
| Full hard tile time | Not measured |
| 35-tile Lean runtime | Not measured; no extrapolation asserted |

An external range-quadrature pilot, even for only the first theta term and
central real component on [1,4], has enclosure width 1.24056e-5 after 32,768
panels. The target integral width is 1e-8, chosen for the center error budget.
The observed inverse-panel-count trend projects about 40.65 million panels for
this one component. That projection is descriptive, not a lower bound on other
rules and not a Lean runtime measurement.

**Decision:** do not scale the present range quadrature to the rectangle.
A proved higher-order integration rule, complete theta/Mellin jet assembly and
fresh hard-tile timing are needed before a whole-rectangle runtime estimate.
The original first tile at center 1/2, radius 1/100 remains certified. No result
here discharges `ZetaNoLowStripZero (141/10)`.

## Paper and verification

The five-page working draft is `paper/formal_split_pair/main.tex` and `main.pdf`,
titled *Finite and analytic split-pair oscillation and the Toeplitz--Jacobi bridge*.
It attributes the classical mechanism to Edrei and related Toeplitz literature,
states the exact hypotheses, and excludes the unproved rectangle from its title
and claims. It has not been submitted or published. All five pages were rendered
and visually inspected after layout repair.

The previous commit `855c2c5039ed894b92bdba570947c320832118b3` was pushed.
Its [GitHub Actions run](https://github.com/sciencenerd-des/reinmann/actions/runs/39101056242)
completed successfully. This is CI evidence for that commit; the new assembly has
local build and audit evidence and is not covered by that older CI run.

The new full `lake build` passes (3,598 jobs). The source scan and axiom audit
pass for 364 declarations, including all 16 new public theorems. The audit finds
no unfinished proofs or project-declared axioms; audited dependencies are
`propext`, `Classical.choice`, and `Quot.sound`.

Run the checks:

```sh
lake build
bash scripts/verify_axiom_clean.sh
python3 experiments/prime_spectral/verify_analytic_assembly_round.py
```

Reproduce the external pilots and isolated Lean panel:

```sh
uv run --offline --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/xi_hard_tile_pilot.py --output tmp/hard-tile-replay/arb.json
uv run --offline --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/xi_hard_panel_cost.py --output tmp/hard-tile-replay/range.json
python3 experiments/prime_spectral/check_leancert_v430.py
python3 experiments/prime_spectral/check_hard_panel.py
```

The new immutable manifest preserves the preceding 1,096-artifact closure.
Only the two root library integration files change among those bindings; their
exact prior versions are saved in `historical_855c2c5/`. All other old artifacts,
including the published DH scientific files, remain byte-identical. Old manifests
are not rewritten. The Liu note remains unposted.
