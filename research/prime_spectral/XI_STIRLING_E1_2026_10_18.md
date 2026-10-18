# E1: complex Stirling formula with explicit remainder (18 October 2026)

Status: **proved in Lean, axiom-clean**. This closes obligation E1 of
`XI_EVALUATOR_ROUTE_DECISION_2026_10_18.md` inside its time-box.

## What is proved

Modules: `Reinmann/StirlingCell.lean`, `Reinmann/StirlingSum.lean`,
`Reinmann/StirlingGamma.lean` (30 audited theorems; 455 in total).

- `StirlingGamma.Gamma_eq`: for `0 < Re w`,

      Γ(w) = exp((w − 1/2) Log w − w + log(2π)/2 − corr w 0 + tail w).

- `StirlingSum.tail_norm_le`: `‖tail w‖ ≤ (6112/15015)/12 · 1/(11 (Re w)^11)`.
- `StirlingGamma.corr_zero_eq`: the correction is the classical Stirling series,
  `−corr w 0 = Σ_{k<11} B_{k+2} / ((k+1)(k+2)) · w^{−(k+1)}`.
- `StirlingGamma.Gamma_eq_shift`: for `0 < Re(w+K)` and `w + j ≠ 0` (j < K),
  `Γ(w) = exp(mainTerm(w+K) + tail(w+K)) / Π_{j<K} (w+j)`.

Proof path: Euler's limit `Complex.GammaSeq_tendsto_Gamma`, with GammaSeq written
as the exponential of a sum of principal logarithms (no branch issue). It then
uses order-12 Bernoulli summation of `Σ Log(w+j)`, reusing the existing
`BernoulliQuadrature` and `periodicTwelve` bound, and Mathlib's Stirling constant
`Stirling.tendsto_stirlingSeq_sqrt_pi`. Nothing about Γ is assumed.

## Gate check (accuracy)

On the hard disk, `s ∈ D(1/2+14i, 1/16)`, so `w = s/2` has `Re w ≥ 1/4 − 1/32`.
With the shift `K = 12`, `Re(w+K) ≥ 12.21875`, and the proved remainder bound is
about **3.4·10⁻¹⁵**. That is far below the 10⁻⁸ jet-accuracy gate.

## Cost

A full `lake build` takes 3,640 jobs. `StirlingGamma.lean` elaborates in about
25–30 s on this machine, and each of the other two modules takes seconds.

## Still open for the hard tile (unchanged scope)

- **E2:** numeric enclosures of `mainTerm(w+12)` and the shift product at the
  tile centre. This needs certified complex exp/log and the 11 Bernoulli
  rationals.
- **E3:** degree-16 jets. Cauchy estimates on the remainder need `tail`
  holomorphic on `Re w > 0` (differentiation under the integral, with the same
  `1/(Re w + t)^12` dominator), or the equivalent for log Γ − mainTerm.
- **E4:** tile assembly with `adaptive_cover_nonzero` and the proved majorant
  1000, then a Lean timing.

No complete hard tile is certified yet. Nothing here discharges
`ZetaNoLowStripZero (141/10)` or touches any PF ⇒ RH bridge. This is not a
proof of RH.

Logs: `verification_2026_10_18_stirling/full_build.log`, `axiom_audit.log`.

Replay note: `verify_em_identity_round.py` hashes the then-current
`Reinmann.lean` and `AxiomAudit.lean` (425 audit lines). Those two files at
`8e187b5` are preserved under `verification_2026_10_18_stirling/historical_8e187b5/`.
Replay that round at its own commit.
