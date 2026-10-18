# Proved ordinary Gamma/zeta jet remainders, 18 October 2026

The analytic remainder estimates needed for the hard jet are now Lean theorems.
At `c = 1/2+14i`, for **every** order `n`, including `0..16`:

```text
| Gamma(s/2) coefficient_n - finite_Stirling_coefficient_n | <= 4e-14,
| zeta(s) coefficient_n - finite_EM_coefficient_n | <= 1e-7.
```

All coefficients here are **ordinary Taylor coefficients**, `f^(n)(c)/n!`.
The Gamma approximant shifts by 12 and retains the corrections `B2` through
`B12`. The zeta model uses `N=21`, i.e. twenty Dirichlet terms, and corrections
`B2` through `B12`. The eleven-term formal sums include zero odd Bernoulli terms.

The actual remainder functions are constructed and proved holomorphic; no
analyticity, numerical circle majorant, remainder identity or jet-error bound
is assumed. These theorems discharge the analytic remainder part of E3. They
**do not** supply kernel-checked finite exp/log evaluations or finite-model jet
coefficient enclosures (E2), nor a complete hard tile (E4).

## Gamma proof

`StirlingAnalytic` builds on the actual complex Stirling identity at `6dd599e`.
The remainder integrand is normalized to

```text
-B12(fract t)/12 * (w+t)^(-12),
```

and its actual complex derivative is `B12(fract t)*(w+t)^(-13)`. On a ball of
radius `Re(w)/2`, the derivative is dominated by

```text
(6112/15015)/a * 1/(a+t)^12,    a = Re(w)/2 > 0.
```

That majorant is integrable by the already-proved order-12 integral. Mathlib's
dominated parameter-integral theorem gives complex differentiability of the
actual remainder. On the **full unit disk** about `c`, `Re(s/2+12) >= 47/4`, so
its norm is at most `1e-14`, checked by rational arithmetic in Lean. This is the
unit disk used for Cauchy estimates, not just the tile of radius `1/16`.

To bound the **absolute** Gamma approximation error, no sharp numerical bound
is needed. The Gamma shift-product estimate and `Im(s/2) >= 13/2` give

```text
|Gamma(s/2)| <= Gamma(Re(s/2)+12)/(13/2)^12
             <= 12!/(13/2)^12 <= 1.
```

The middle inequality uses Mathlib's proved monotonicity of real Gamma on
`[2,infinity)` and `Re(s/2)+12 <= 13`. The actual Stirling identity then gives
`|GammaApprox(s)| <= 2`; the exponential remainder bound gives an absolute
error `<= 4e-14` on every point of the closed unit disk. Both functions are
proved holomorphic there. Cauchy's estimate yields the same bound on every
ordinary error coefficient. `gamma_coefficient_error_le` explicitly compares
the separately normalized derivatives of actual Gamma and its approximant.

## Zeta proof

`ZetaJetRemainder` uses the actual EM identity already proved on the upper
half-strip. On the closed hard unit disk, Lean proves `|s| <= 16` and
`Re(s) >= -1/2`. Thus

```text
|(s)_12| <= product_(j=0)^11 (16+j),
21^(-Re(s)-11) <= 21^(-10),    Re(s)+11 >= 21/2.
```

Substituting these into the proved B12 integral bound gives the rational
upper bound `363248384/8990455847250339 < 1e-7`. All powers and inequalities
in this last step are kernel-checked rational arithmetic. The extra Dirichlet
terms avoid needing a numerical square-root bound. Holomorphy and Cauchy's
estimate again give the ordinary coefficient bound, explicitly comparing
actual zeta and its finite model in `zeta_coefficient_error_le`.

## External hard-tile probe

An Arb replay uses exactly these two **proved analytic coefficient-error
constants**, rather than the previous external EM/Stirling error bounds.
It encloses the finite models' seventeen coefficients and propagates their
errors through the Xi prefactor and product. Builtin Gamma/zeta are used only
as an independent overlap reference.

At 192 bits, all 17 coefficients overlap that reference. The maximum complex
radius is about `7.47e-10`, below the `1e-8` target. Using radius `1/16` and the
already-proved Xi unit-circle majorant `1000`, the external tile margin is
about `9.37246e-5 > 0`. Seven-run median time is about `0.8 ms` on this run.
Exact measurements and source hashes are in `probe.json`.

**This is still an external Arb calculation.** Its finite exp/log and series
arithmetic are not Lean certificates. The complete Lean hard-tile runtime and
any 35-tile runtime estimate remain unknown. The test shows that the weaker,
fully proved remainder constants are sufficient for this evaluator design.

## Verification and historical evidence

This round adds 35 public theorems: 25 in `StirlingAnalytic`, ten in
`ZetaJetRemainder`. The full local build and semantic audit cover **490**
declarations, with only Lean's standard foundational axioms, no project axioms
and no `sorry`. The baseline `6dd599e94a6dd8099b8636833a23ecd37f5a5888` has
[successful CI](https://github.com/sciencenerd-des/reinmann/actions/runs/39118187321).
That CI predates this round. Its current local receipts are checked by
`verify_proved_jet_remainders_round.py`.

The prior EM manifest's root import/audit bindings are preserved using the
existing `historical_8e187b5` copies. The newer 455-declaration root files are
preserved under this round's `historical_6dd599e`. The Stirling E1 files and
receipts are additionally bound to their exact Git source pin. Earlier
manifests and publication artifacts are unchanged; no PF implies RH bridge is
modified. Nothing here certifies a low zero-free rectangle or proves RH.

Replay:

```sh
lake build
bash scripts/verify_axiom_clean.sh
uv run --offline --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/xi_proved_remainders_probe.py --output tmp/proved-jet-remainders-replay.json
python3 experiments/prime_spectral/verify_proved_jet_remainders_round.py
```

The next implementation task is E2: prove the finite complex exp/log and
ordinary-jet arithmetic enclosures, then assemble and time the complete hard
tile. The Gamma Euler-integral fallback is unnecessary now that the actual
Stirling identity and its coefficient error bounds are proved.
