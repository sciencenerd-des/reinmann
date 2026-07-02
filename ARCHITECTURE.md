# Reinmann — Architecture & Verification Map

**Canonical, current overview of the repository.** This file supersedes the
~19 historical status/summary files now archived under [`docs/archive/`](docs/archive/).
For narrative and dated progress logs, see that archive and [`research/`](research/).

> **Last verified:** `lake build` — 3496 jobs, exit 0. `scripts/verify_axiom_clean.sh`
> — 0 `sorry`, 0 custom axioms; all audited reduction theorems depend only on
> `[propext, Classical.choice, Quot.sound]`.

---

## What is and is not proven

This project **does not prove the Riemann Hypothesis**, and cannot by engineering
alone. What it *does* provide is a large, fully machine-checked body of
**conditional reductions**: theorems of the form *"IF ⟨named analytic input⟩ THEN
RH"*, together with the equivalences that pin down exactly which inputs remain open.

The honesty discipline is enforced structurally (see
[`Reinmann/RHReductionCapstone.lean`](Reinmann/RHReductionCapstone.lean)): every
open, RH-equivalent input is carried as a **named `Prop` hypothesis**, never as an
`axiom`. Declaring `axiom xiToeplitzTotalPositive` would be mathematically
identical to `axiom rh` — assuming the conclusion — so it is deliberately avoided.
`Reinmann/AxiomAudit.lean` + `scripts/verify_axiom_clean.sh` make this checkable in
one command.

| Claim | Status |
| --- | --- |
| Reduction chain `HilbertPólyaWitness ⟹ RH` (spectral branch) | ✅ proven, axiom-clean |
| Reduction `same-height uniqueness + conjugate symmetry ⟹ RH` | ✅ proven, axiom-clean |
| `RH ↔ full Ξ Pólya-frequency (Toeplitz) total positivity` | ✅ equivalence proven |
| The Pólya-frequency positivity input itself | ❌ **open** (RH-equivalent) |
| The Riemann Hypothesis | ❌ **open** |

---

## The reduction chain

```
        HilbertPolyaWitness
                │  riemannHypothesis_of_twoBranchArchitecture   (TwoBranchArchitecture.lean)
                ▼
   ZeroImUniqueness + ConjugateSymmetry
                │  uniqueness_implies_rh                          (ZeroSymmetry.lean)
                ▼
        RiemannHypothesis

   RH  ◄──────────────────────────►  XiToeplitzTotalPositive
       xiToeplitzTotalPositive_iff_riemannHypothesis   (RHReductionCapstone.lean)
```

Both branches, their architecture-level packagings
(`main_spectral_reduction`, `main_uniqueness_reduction` in
[`Reinmann/ProofArchitecture.lean`](Reinmann/ProofArchitecture.lean)), and the
capstone equivalence are audited in
[`Reinmann/AxiomAudit.lean`](Reinmann/AxiomAudit.lean).

---

## The open frontier — three-level ladder

Defined in [`Reinmann/RHTheoremTargets.lean`](Reinmann/RHTheoremTargets.lean).
Progress toward RH means climbing this ladder analytically; it is **not** reachable
by refactoring.

| Level | Target | Meaning | Status |
| --- | --- | --- | --- |
| 1 | `Order3FrontierTheorem` | First open Toeplitz/PF rung beyond Turán | open; finite/rational fragment certified in `Order3Certificate.lean` |
| 2 | `KernelContigTotalPositive` | All contiguous factorial-weighted kernel minors | open |
| 3 | `XiToeplitzTotalPositive` | Full arbitrary-minor PF positivity — RH-equivalent | open |

---

## Module inventory

Grouped by role. All 48 modules imported by [`Reinmann.lean`](Reinmann.lean) build
axiom-clean.

### Spine & core reductions
| Module | Role |
| --- | --- |
| `RiemannSpine.lean` | Foundational RH equivalences (half-strip / off-line / involution) |
| `ProofArchitecture.lean` | Complete reduction chain, both branches packaged |
| `RiemannHypothesisReduction.lean` | Unconditional reduction of RH to zero-height uniqueness |
| `RHReductionCapstone.lean` | The honest conditional capstone + tightness equivalence |
| `TwoBranchArchitecture.lean` | Spectral (Hilbert–Pólya) branch to RH |
| `ZeroSymmetry.lean` | Uniqueness framework; `uniqueness_implies_rh` |

### Symmetry & the completed zeta
| Module | Role |
| --- | --- |
| `ConjugateHalfPlane.lean`, `ConjugateSymmetryComplete.lean` | Conjugate symmetry of ζ |
| `InvolutionSymmetry.lean` | The `s ↦ 1−s̄` involution on strip zeros |
| `ZetaPrimeSymmetry.lean`, `CompletedZetaPrime.lean`, `CompletedZetaConj.lean` | Symmetry of ζ′ and Λ₀′ |
| `HadamardZetaTransfer.lean` | Completed-zeta Hadamard transfer contract |

### Fiber / same-height geometry
| Module | Role |
| --- | --- |
| `ZeroFiberFiniteness.lean` | Finiteness of zeros at a fixed height |
| `FiberCentroid.lean` | Each height-fiber centroid is exactly 1/2 (unconditional) |
| `FiberEnergyGap.lean`, `MirrorHeightEnergy.lean`, `SpectralEnergyCriterion.lean` | Energy/order-parameter criteria |
| `HorizontalRepulsion.lean`, `HorizontalCritical.lean`, `HorizontalDerivative.lean` | Same-height repulsion & ζ′ route |

### Jensen / Pólya-frequency frontier
| Module | Role |
| --- | --- |
| `JensenProgram.lean`, `JensenTuranBridge.lean` | Laguerre–Pólya / Jensen `d=2` ⟹ Turán rung |
| `XiTotalPositivity.lean`, `XiToeplitzPositivity.lean` | Total-positivity targets (Toeplitz, not Hankel) |
| `XiMomentKernel.lean`, `XiPlanePrincipalValue.lean` | Moment-kernel mechanism; Ξ-plane principal values |
| `CrossFieldBridges.lean`, `RHTheoremTargets.lean` | Order-3 frontier bridges; the theorem-target ladder |
| `FiniteGaussLucas.lean` | Finite Gauss–Lucas / log-derivative surrogate |

### Critical-line detection & counting
| Module | Role |
| --- | --- |
| `CriticalLineRealSlice.lean`, `CriticalLineCounting.lean` | On-line zero detection & sign-change counting |

### Zero-free region program (de la Vallée Poussin)
| Module | Role |
| --- | --- |
| `VdpConditional.lean`, `VdpCertificates.lean`, `CertificateBarrier.lean` | Verified deductive core, certificate theory, method ceiling |
| `ZeroFreeEngine.lean`, `BoundaryGrowthBuildingBlocks.lean` | Positivity engine & analytic building blocks |
| `ZetaStripBounds.lean`, `ZetaLeftEdge.lean` | ζ growth bounds on vertical lines / left edge |
| `EulerFactorPositivity.lean`, `Zeta341GlobalBridge.lean` | Euler-factor 3-4-1 positivity, global product bridge |
| `KnownZeroFreeRegions.lean` | Known zero-free regions |

### Hilbert–Pólya / operator-theoretic route
| Module | Role |
| --- | --- |
| `HilbertPolyaExperiment.lean`, `HilbertPolyaConstruction.lean` | Honest reduction; symmetric operators with prescribed spectrum |
| `HilbertPolyaConverse.lean`, `InfiniteHilbertPolya.lean` | Finite converse; infinite-dimensional witness |
| `PseudoHermitian.lean` | Pseudo-Hermitian / PT reduction |
| `RHAttackBridges.lean` | Unified bridges across the routes |

---

## Verifying locally

```sh
lake exe cache get          # fetch cached mathlib
lake build                  # build all 48 modules
bash scripts/verify_axiom_clean.sh   # prove 0 sorry / 0 custom axioms
./scripts/safe-verify.sh    # exhaustive per-file typecheck (heavier)
```

CI (`.github/workflows/ci.yml`) runs `lake build` + the axiom guard on every push.
