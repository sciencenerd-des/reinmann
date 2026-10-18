# Kernel-checked Euler–Maclaurin components, 18 October 2026

The next evaluator obligation is now split into proved finite components and
unproved function identities. This round adds 22 public Lean theorems. It does
**not** certify the centre at `1/2 + 14i`, a hard tile, a zero-free rectangle, or RH.
The published papers and their source archives are unchanged.

## What is proved

- `BernoulliQuadrature`: the derivative and endpoint values of the actual
  factorial-normalized Bernoulli polynomials, one integration-by-parts step,
  and an exact all-orders quadrature formula on `[0,1]` for a derivative chain.
- `EulerMaclaurinCell`: proves the derivative chain for the actual function
  `(N+t)^(-s)` at every positive `N+t`, then applies that quadrature formula.
  The cell theorem accepts no assumed derivative identities.
- `BernoulliBernsteinBounds`: a general whole-interval bound from Bernstein
  coefficients and a degree-12 rational certificate giving
  `|B12(x)| ≤ 6112/15015` for **every** `x ∈ [0,1]`. Consequently the same bound
  holds for `B12(fract t)` for every real `t`.
- `EulerMaclaurinTail`: measurability and integrability of the actual periodic
  Bernoulli integrand, plus its explicit improper-integral norm bound.

More precisely, with `C12 = 6112/15015`, `σ = Re s > -11`, and `N > 0`, Lean proves

```text
R12(s,N) = -(s)_12/12! * ∫_(N,∞) B12(fract t) t^(-s-12) dt
‖R12(s,N)‖ ≤ ‖(s)_12‖/12! * C12 * N^(-σ-11)/(σ+11).
```

Here `R12` is a definition by the displayed integral. We have **not** proved that
it equals zeta minus the finite Euler–Maclaurin expression. Naming the integral
“remainder” does not discharge that identity.

The Bernstein certificate uses nonnegative basis polynomials whose sum is one.
Its coefficient maximum is the rational `6112/15015`; its polynomial identity and
all coefficient inequalities are checked with kernel-replayed rational algebra.
There is no sample-grid extrapolation, Fourier-series assumption, native evaluator
axiom, or additional project axiom. Cached Bernoulli values are individually
proved from Mathlib's finite recurrence.

## Numerical relevance

The separate Arb validation substitutes **this** Bernoulli constant into the
existing external EM/Stirling evaluator, without changing that frozen driver.
At `1/2 + 14i`, with degree-16 ordinary coefficients and 192-bit arithmetic:

| Zeta terms | Corrections | Maximum complex coefficient radius | Median runtime, seven runs |
|---:|---:|---:|---:|
| 10 | 6 | 2.83e-9 | approximately 0.70 ms |
| 12 | 6 | 4.89e-10 | approximately 0.68 ms |
| 16 | 6 | 2.92e-11 | approximately 0.68 ms |

All 17 coefficients overlap the independent builtin Gamma/zeta reference; all
meet the `1e-8` target. Exact measured timings and radii are in the bound receipt.
These are external Arb timings, **not Lean panel or tile timings**. The zeta
identity and complex Stirling identity/error remain externally justified in this
experiment. The numeric log/exp arithmetic is not yet a Lean enclosure.

## Verification and evidence

`570a5cfb45e4f74c35b0167d87f45059ba5ca13f` was pushed and its
[CI run 39114361022](https://github.com/sciencenerd-des/reinmann/actions/runs/39114361022)
completed successfully. That CI predates these 22 new theorems. Their local full
build and axiom audit are stored in `verification_2026_10_18_em_foundations` and
checked by `verify_em_foundations_round.py`. Historical root import/audit files
preserve the previous manifest's bindings; the prior manifest is not rewritten.
All 394 audited public theorems use only Lean's standard foundational axioms.
The modules retain the invariant that no component imports the umbrella root.

Replay from this checkout:

```sh
lake build
bash scripts/verify_axiom_clean.sh
uv run --offline --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/xi_em_bernstein_validation.py --output tmp/em-bernstein-replay.json
python3 experiments/prime_spectral/verify_em_foundations_round.py
```

The manifest checks file hashes and recorded outcomes. The build, semantic axiom
audit, and Arb driver are separate replays, not consequences of a hash match.

## Remaining work before a complete hard tile

1. Sum the exact cell formulas and take the infinite limit in `Re s > 1`,
   identifying the integral with the **actual** zeta tail there.
2. Prove holomorphy of the integral and continue the identity to `Re s > -11`
   away from `s = 1`. The unit disk about the target has `Re s ≥ -1/2`.
3. Prove a usable complex Gamma evaluation identity and explicit remainder,
   or replace that evaluation by another already-identified Gamma formula.
   Reflection bounds alone do not give the complex Gamma value.
4. Supply proved finite exp/log and jet enclosures, apply the local derivative
   theorem, and measure one **complete** hard tile. Only then is multiplying
   Lean time by 35 meaningful. That time remains unknown.

## Prior art and proof route

The finite Euler–Maclaurin and Bernstein arguments are classical. This round
makes no mathematical novelty claim. The explicit evaluator comparison remains
motivated by [Johansson's Hurwitz-zeta computation paper](https://arxiv.org/abs/1309.2877).
For Gamma, [Johansson's 2023 survey](https://doi.org/10.5206/mt.v3i1.14591)
provides algorithms and error analyses.

The [Isabelle AFP Stirling formalization](https://www.isa-afp.org/browser_info/current/AFP/Stirling_Formula/document.pdf)
already proves a complex log-Gamma Stirling identity with a periodic Bernoulli
integral and an explicit asymptotic remainder. This supplies a proof architecture,
not a Mathlib theorem or a ready Lean proof. Its identity includes the appropriate
endpoint Bernoulli correction: shifting the truncation order without keeping
that correction would give the wrong remainder. No AFP code is copied here.
