# Theorem-status ledger for the synthesized RH paper

This ledger accompanies `paper/rh_two_routes_paper.tex`.  The complete audit
list is in `Reinmann/AxiomAudit.lean`; this file records the principal
interfaces cited in the manuscript.

## Proved in Lean

| Theorem / definition | File | Role |
|---|---|---|
| `Xi_eq_zero_iff_riemannZeta` | `JensenProgram.lean` | Correct ξ zero correspondence |
| `maxMinor_syzygy` | `GrassmannSyzygy.lean` | Generic Grassmann identity |
| `grassmann_three_term` | `GrassmannSyzygy.lean` | Three-term gap identity |
| `xiInitialMinor_pos_of_strictLadder` | `FeketeAllOrders.lean` | All-order row-gap induction |
| `xiInitialColumnMinorTotalPositive_of_strictLadder` | `FeketeAllOrders.lean` | Initial-column positivity |
| `xiToeplitzTotalPositive_of_strictLadder` | `ToeplitzFullPF.lean` | Full PF closure |
| `riemannHypothesis_of_strictLadder` | `ToeplitzFullPF.lean` | Conditional RH capstone |
| `polynomialHyperbolic_of_tendsto` | `HyperbolicLimit.lean` | Bounded-degree hyperbolic limit |
| `turan23_not_imp_toeplitz3` | `TuranRouteKill.lean` | Local Turán route-kill |
| `order3RatioGapExpr_nonneg_of_effective_bounds` | `Order3Certificate.lean` | Exact interval receptor |
| `riemannHypothesis_of_effectiveCertificates` | `EffectiveAssembly.lean` | Route A assembly |
| `jensenPoly_hyperbolic_of_hpss` | `EffectiveAssembly.lean` | Jensen/HPSS receptor |
| `riemannHypothesis_of_hpss_route` | `EffectiveAssembly.lean` | Route B assembly |
| `certGapRatio_lt_two` | `CertificateBarrier.lean` | 3–4–1 limitation |
| `fiber_centroid_eq_half` | `FiberCentroid.lean` | Same-height symmetry reduction |
| `riemannHypothesis_of_liCriterion` | `LiCriterion.lean` | Conditional Li package |
| `riemannHypothesis_of_twoBranchArchitecture` | `TwoBranchArchitecture.lean` | Conditional operator package |

## Named external inputs / open targets

| Proposition | Status |
|---|---|
| `ClassicalToeplitzScaffolding` | External ASW/Edrei, Laguerre–Pólya, Pólya–Jensen bridges; not formalized here |
| `XiMomentKernelRep` | Pólya kernel representation; named input |
| `XiMomentStrictTuran` | Classical strict Turán input; named input |
| `KernelEffectiveCertificates` | Open effective prefix-plus-tail theorem for every order |
| `HermitePoulainSchurSzegoTheorem` | Open general same-sign composition theorem in the Lean interface |
| `XiJensenCoeffHyperbolic` | Open all-degree/all-shift Xi window certificate |
| `HeatFlowRigidity` | Proposed third-route target asserting the missing \(\Lambda\le0\) rigidity |

## Audit contract

- `bash scripts/verify_axiom_clean.sh` must report 87 audited theorems and only
  `[propext, Classical.choice, Quot.sound]`.
- `bash scripts/safe-verify.sh` must pass without `sorry`, `admit`, or project
  axioms.
- Numerical scan outputs are diagnostics, not theorem inputs.
- No open target appears as a Lean axiom or an unvalidated instance.
