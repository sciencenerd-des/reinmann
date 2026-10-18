# Xi evaluator route: go/no-go memo (18 October 2026)

**Decision: GO on the Euler–Maclaurin/Stirling (EM) route. Keep the Mellin
Taylor-model route as the fallback.** The deciding fact is new today:
`fb2bf81` proves the actual ζ Euler–Maclaurin identity on the whole hard disk.
The EM route's remaining analytic work is now a single theorem, the complex Γ
evaluation. The Mellin route still needs two analytic theorems and about eight
times more certified arithmetic per tile.

This memo is about proof cost. External Arb timings (EM 0.6 ms, Mellin 6–8 ms
per jet) are not Lean runtimes and are used only as a proxy for arithmetic
volume.

## Already proved (shared or route-specific)

| Item | Status | Module |
|---|---|---|
| ξ = Mellin integral; truncation tail on the low rectangle | proved | `XiMellinRemainder`, `XiMellinRectangle` |
| finite-theta tail | proved | `XiFiniteTheta` |
| ζ = order-12 EM model + R₁₂ on Re s > −11, Im s > 0 (covers the hard disk) | proved | `EulerMaclaurinZeta`, `EulerMaclaurinAnalytic` |
| symbolic bound on R₁₂ (B₁₂ Bernstein constant 6112/15015) | proved | `EulerMaclaurinTail`, `BernoulliBernsteinBounds` |
| Bernoulli quadrature / cell machinery | proved | `BernoulliQuadrature`, `EulerMaclaurinCell`, `EulerMaclaurinFinite` |
| per-tile cover rule, quarter reduction, unit-circle majorant 1000 | proved | `XiAdaptiveTiles`, `XiLocalCauchy` |
| Γ norm bounds (shift product, reflection + Beta comparison) | proved, norms only | `GammaHeightMajorant`, `GammaReflectionMajorant` |
| complex exp Taylor bound | Mathlib `Complex.exp_bound` | — |

## Remaining obligations

### EM route

| # | Obligation | Effort | Notes |
|---|---|---|---|
| E1 | Complex Γ(w) value with explicit remainder for Re w ≥ −1/4, Im w ≈ 7 | **High** (the one hard theorem) | Shift w → w+K (K≈12), then Stirling with Bernoulli terms. Proof path: Mathlib `Complex.GammaSeq_tendsto_Gamma` (Gauss limit) + EM on Σ log(w+k) (reuse the Bernoulli quadrature and the B₁₂-type bound) + the Stirling constant from `Stirling.tendsto_stirlingSeq_sqrt_pi`. Work with exp of sums to avoid branch issues in a log of the product. The Isabelle AFP proof is the architecture reference. |
| E2 | Numeric enclosure of the ζ model and Stirling terms at the tile centre | Low–medium | About 14 elementary calls per centre: n^(−s) = exp(−s log n), finite Bernoulli rationals, (s)_j. Complex exp from `Complex.exp_bound` with argument reduction; log of small integers from Mathlib series bounds. |
| E3 | Jets (degree 16) | Low | The model's s-derivatives are closed forms. Remainder jets follow from the proved symbolic bound on the unit disk plus Cauchy's estimate. |
| E4 | Tile assembly and timing | Low | Rules exist (`adaptive_cover_nonzero`, the majorant-1000 Cauchy tail). |

### Mellin route

| # | Obligation | Effort | Notes |
|---|---|---|---|
| M1 | Taylor-model panel integrator with a Cauchy remainder in a complex t-disk | Medium | Needs analyticity of θ_N(t)·t^(s−1)·log(t)^j on each disk and a **numeric majorant on every complex panel disk** (20 panels per centre). |
| M2 | s-jets: swap the s-Taylor series with the t-integral (17 orders) | Medium | Fubini/dominated convergence for log(t)^j weights. |
| M3 | Numerics | Medium–high | About 120 exp/log model calls per centre, plus the panel majorants. A certified panel took about 3 s beyond imports. |
| M4 | Tile assembly | Low | Shared rules. |

## Comparison

- **Analytic theorems left:** EM has one (E1); Mellin has two (M1, M2).
- **Arithmetic per tile:** EM ≈ 14 calls; Mellin ≈ 120 calls plus disk majorants.
- **Reuse:** E1 reuses today's EM machinery directly (Bernoulli quadrature,
  Bernstein bounds), with log(w+t) in place of (N+t)^(−s). M1 needs new
  complex-disk majorant arithmetic.
- **Risk:** E1 is a substantial formalization, but every ingredient (Gauss
  limit, Stirling constant, EM quadrature) is already in Mathlib or this repo.
  If E1 stalls, M1+M2 remain available, and the function identities they need
  are already proved.

## Go/no-go gates

1. **E1 time-box.** Stop and switch to Mellin if the complex Stirling theorem
   (value plus remainder on the shifted disk) is not proved within about two
   working rounds, or if its remainder constant is too weak for 10⁻⁸ jet
   accuracy at K ≤ 16.
2. **Hard-tile gate (unchanged).** Prove one complete tile at 1/2+14i with a
   degree-16 jet, radius 1/16, and the proved majorant 1000, then time it in
   Lean. Scale to the 35-tile cover only if one tile takes minutes, not hours.
3. **Majorant.** Deprioritized. The degree-16 jet tile works with the proved
   1000 majorant, and the numerical strip majorant (about 0.0125 externally)
   is not needed.

## Housekeeping done with this memo

- The in-progress EM identity round was rebuilt (3,635 jobs) and audited
  (425 theorems, standard axioms only). Its verification record was completed
  from real runs and committed as `fb2bf81`, then pushed for CI.
- No published file is changed. No PF ⇒ RH bridge is touched. Nothing here
  discharges `ZetaNoLowStripZero (141/10)`.
