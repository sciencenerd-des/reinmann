# Degree-eight arithmetic and the first actual composition, 18 October 2026

The hard-tile target is now **degree 8**, with nine ordinary coefficients and
an eventual Xi coefficient-disk budget of **1e-7**. This checkpoint proves the
rational arithmetic layer and instantiates its reciprocal/Log machinery on
`Log(s/2+12)` at `c=1/2+14i`. It does **not** yet certify the complete finite
Gamma/zeta/Xi jet or a nonzero hard tile. The complete-tile time and any estimate
for 35 tiles remain unknown. No zero-free rectangle or RH proof is claimed.

## Numerical precheck, before the new Lean layer

`xi_degree8_probe.py` ran at 64, 80 and 96 bits. It used exactly the previously
proved analytic errors, Gamma **4e-14** and zeta **1e-7** per ordinary coefficient,
with the shifted Stirling model (shift 12, six nonzero corrections) and the EM
model (N=21, twenty Dirichlet terms, six nonzero corrections).

All nine coefficient intervals overlap the independent builtin Gamma/zeta
reference. Their largest complex radius before rounding is about **7.47e-10**.
All coefficients can be rounded to centres with denominator at most 2^28 and
individual disk error **1e-7**. At tile radius 1/16, the existing unit-circle Xi
majorant 1000 gives an external positive margin about **9.34787e-5** even after
rounding and the degree-eight derivative tail. The low-precision Arb evaluation
is roughly 0.15--0.16 ms on this run; exact timings are in `arb_probe.json`.

These are external numerical results, not Lean-certified Xi coefficients.
The derivative-tail calculation in this probe has not yet been connected to
`adaptive_cover_nonzero` in a complete hard-tile module.

## Certified arithmetic

`CertifiedTaylorModel` stores a rational complex centre and a nonnegative
rational disk radius for each coefficient. `Jet8` has type `Fin 9 -> Disk`.
Soundness refers to **ordinary** coefficients `iteratedDeriv k f c / k!` at an
arbitrary complex centre. Add, multiplication and rational complex scaling are
proved sound; the product proof derives the convolution from Leibniz's rule
and the factorial identity. These are not Jensen coefficients.

Multiplication uses the rational L1 bound for the centre's complex norm.
Outward rounding is a separately checked inequality: old radius plus the L1
centre displacement is at most the new radius. This avoids importing rounded
machine calculations as facts. An inflation/perturbation rule attaches a
separately proved analytic coefficient error to a finite approximant. Norm
majorants and the zeroth-coefficient/function-value bridge are also proved.

`CertifiedTaylorComposition` proves the actual analytic coefficient recurrences
for exp, reciprocal and principal Log. Its soundness theorems accept a finite
sequence of rational outward-rounding inequalities and a proved constant-value
enclosure. Log retains the explicit slit-plane condition. Differentiability,
local derivative identities and the coefficient normalization are derived;
these are not assumed formal-series identities.

`CertifiedHorner` proves a rounded Horner certificate and its equality to the
ordinary exponential and Mathlib logarithm polynomials. Rounding is permitted
at every Horner step. `CertifiedComplexInputs` supplies Mathlib-based series
error bounds: twenty exponential terms on the unit disk give error <=1e-18;
Mathlib's `logTaylor 48` on the half-unit disk gives error <=1e-15. The exact
2*pi phase-reduction identity and the closed formula for the coefficients of
`exp(a*s)` are proved. **Numerical phase enclosures for the Dirichlet terms are
still to be instantiated.**

## Actual scalar inputs and the first composition

`HardTileLogInputs` certifies logs of **every integer 2..21**, including every
prime through 19, and **log pi**, with errors <=6e-15 (log 2 uses 1e-15).
The proofs use Mathlib's atanh-series bound with twenty terms after scaling by
a power of 2; log pi uses Mathlib's 20-decimal pi bounds and monotonicity.
Each displayed centre is a rational proposal checked by Lean.

At the actual shifted centre `w=49/4+7i`, Lean proves

```
Log(w) = log(16) + Log(1+delta),
delta = -15/64 + (7/16)i,    |delta| <= 1/2.
```

`HardTileGammaLog` checks a 48-term Horner table with outward rounding on a
50-bit dyadic grid. It certifies the principal value with radius **2^-45**,
approximately **2.84217e-14**. This is a numerical **Log-value** error, distinct
from the already proved analytic **Gamma-factor** remainder of 4e-14.

`HardTileGammaLogJet` then proves the affine input jet, the nine reciprocal
coefficients and all nine coefficients of **actual `Log(s/2+12)`** using the
recurrences. Every coefficient radius is proved <=1e-12; the nonconstant
coefficients use much smaller radii. This is a complete instance of one genuine
composition, not the complete Gamma factor or Xi product.

The three `generate_hard_tile_*.py` scripts reproduce the scalar rational
proposals and tables. Their host arithmetic is not trusted: the generated Lean
files prove every required inequality with kernel-checked rational arithmetic.
No `native_decide`, custom axiom or placeholder proof is used.

## Remaining hard-tile obligations

1. Instantiate the reduced phase/exponential enclosures for the Dirichlet terms
   and the pi exponential, then assemble the finite EM jet.
2. Assemble the Stirling main-term jet, certify its constant exponential, and
   compose exp and the shift-product reciprocal into the finite Gamma jet.
3. Attach the already proved analytic Gamma/zeta coefficient remainders and
   assemble the actual Xi product.
4. Prove the local derivative bound from these nine enclosures and the Cauchy
   tail, apply `adaptive_cover_nonzero`, and time that **complete module**.

Only step 4 provides the requested complete-tile go/no-go measurement. Component
replay timings are recorded separately and must not be multiplied by 35 as a
substitute. The published DH/formalization artifacts and PF-to-RH bridges are
unchanged.

## Verification

This checkpoint adds **78** public theorems; the integrated audit covers **568**
declarations. Fresh full-build, semantic-audit, component-replay and Arb receipts
are stored under `verification_2026_10_18_degree8`. The manifest extends the
previous 1,195-file evidence closure, preserving its old 490-declaration roots
as exact historical copies of commit `7a04cef`.

Replays:

```
uv run --offline --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/xi_degree8_probe.py --output tmp/degree8-arb-replay.json
lake build
bash scripts/verify_axiom_clean.sh
python3 experiments/prime_spectral/time_degree8_components.py --output tmp/degree8-component-replay
python3 experiments/prime_spectral/verify_degree8_round.py
```

The immutable manifest records local outcomes. Remote CI for the new commit is
checked separately after pushing; it is not inferred from the previous commit.
