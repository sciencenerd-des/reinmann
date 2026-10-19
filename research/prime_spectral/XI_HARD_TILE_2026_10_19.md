# A complete degree-eight Xi hard tile, 19 October 2026

`Reinmann.HardTileXi.hard_tile_nonzero` proves, in Lean, that the actual
`Reinmann.xiCompleted` has no zero in the closed disk

\[
  |s-(1/2+14i)|\le 1/16.
\]

`hard_tile_zeta_nonzero` gives the corresponding statement for Mathlib's
`riemannZeta`. These theorems have no numerical-enclosure or zero-free-region
hypotheses beyond membership in this disk. This completes the **single-tile**
go/no-go experiment. It does not discharge `ZetaNoLowStripZero (141/10)`;
the closed rectangle, its coverage, and all other centres remain uncertified.
We do not prove RH.

This note supersedes the incomplete-hard-tile status in the frozen
18 October degree-eight arithmetic checkpoint. That checkpoint's 1,223
evidence bindings are preserved; its two root files and original axiom guard are retained as exact
`1269738` snapshots in this round's evidence directory.

## Certified numerical inputs

The target remains degree eight: nine **ordinary** Taylor coefficients
`iteratedDeriv k f c / k!`, not Jensen coefficients. Each coefficient has a
rational complex centre and a rational disk radius. Every arithmetic operation
rounds outward, with the rational rounding inequality proved by `norm_num`.
There is no `native_decide` or trusted external numerical oracle.

The earlier 64-, 80-, and 96-bit Arb precheck fixed the degree and the
`1e-7` coefficient budget before this assembly. The new exact-rational
generators propose tables; Lean independently checks their inequalities.
An additional 192-bit Arb comparison checks all nine coefficients of each
finite approximant against the earlier independent evaluator. Neither Arb
calculation is a premise of the Lean theorem.

`CertifiedScalarExp` implements exact reduction by an integer multiple of
`2*pi*i`, division by 64, twenty exponential terms, and six outward-rounded
squarings. Its input disk and finite checks imply an enclosure of the actual
complex exponential. The pi interval comes from Mathlib. This handles the
values `n^(-s)` without assuming externally computed sine/cosine values.
`HardTilePowerInputs` separately certifies the twenty scalar inputs for
`n=2,...,21`.

`HardTileFiniteJets` supplies sound jets and analytic-at-centre proofs for
each operation in these two models:

* Gamma: shift 12, six nonzero Stirling corrections, exponentiation of the
  main term, and the twelve inverse shift factors.
* Zeta: the twenty Dirichlet terms `n=1,...,20`, the endpoint at 21, and
  six Euler–Maclaurin corrections.

`HardTileFiniteIdentities` proves that the generated formulas equal the
existing Stirling and Euler–Maclaurin approximants, including all correction
constants. In particular, the finite zeta model is the model with endpoint
**21**, not an unproved truncation of the defining series in the critical strip.

The previously proved **analytic** coefficient errors, `4e-14` for Gamma
and `1e-7` for zeta, are attached by the perturbation rule. The Xi jet then
multiplies the actual Gamma and zeta jets with `s(s-1)/2` and
`exp(-(s/2)*log pi)`. A local identity identifies this product with
`xiCompleted`. The pole-subtracted completed zeta is not used as the zero target.

## The closed-disk certificate

The actual centre enclosure is

\[
\left|\xi(1/2+14i)-\frac{56659349003}{281474976710656}\right|
\le\frac{255423}{1125899906842624}<2.27\cdot10^{-10}.
\]

All nine Xi coefficient disks satisfy the requested `1e-7` error budget
(`xiCompleted_coefficient_error_budget`). The largest proposed radius is
about `5.29e-10`.

`TaylorDerivativeTail.derivative_bound` proves the derivative estimate from
the first eight nonconstant coefficients and a bound `M` on every ordinary
coefficient. The residual is bounded by

\[
 M r^8\left(\frac{r}{(1-r)^2}+\frac9{1-r}\right).
\]

The existing, proved unit-circle Xi majorant supplies `M=1000`. At
`r=1/16`, the kernel-checked rational estimate gives

\[
  |\xi'(s)|\le 9/5000=0.0018
\]

throughout the disk. The centre modulus exceeds the enclosure error plus
`(9/5000)/16` by approximately **`8.87942e-5`**. The final proof instantiates
`XiAdaptiveTiles.adaptive_cover_nonzero` with one closed-ball tile. It does
not merely assume a finite cover or use a finite-section numerical result.

## Timing and decision

Timing replay is recorded in `verification_2026_10_19_hard_tile/replay`.
The measurement re-elaborates seventeen sources serially, including the
actual numerical tables, both analytic remainder modules, and the final
tile. Mathlib and the other analytic foundations are already built. This
is a fresh proof-elaboration measurement, not a clean Mathlib build, an Arb
runtime, or a replay of only the cached last theorem.

On the Apple M4 Pro, fresh elaboration took **597.35 seconds (9 min 57 s)**:

| Scope | Seconds |
| --- | ---: |
| Reusable rules and analytic foundations | 263.11 |
| Centre-specific remainder/input/jet/tile work | 334.24 |
| Complete single-tile replay | 597.35 |

The finite coefficient module took 157.50 seconds; the final Xi module took
22.49 seconds. Reporting only the last number would omit most of the numerical
proof work. Desktop background activity was not controlled; compiled
dependencies and OS caches were retained.

The serial conditional projection is `263.11 + 35 * 334.24`, or **11,961.50
seconds (about 3 h 19 min)**. **Decision: go for implementing further tiles.**
This meets the minutes-per-tile feasibility test, without establishing that
other centres have comparable proof costs or that 35 tiles suffice. Reusing
the numerical remainder budgets at other centres also requires proving
their local domain and size conditions.

The receipt separates reusable rules from centre-specific work. Its
35-centre projection assumes that every other centre costs as much as this
one. That assumption and a 35-tile formal cover have not been tested.

## Reproduction and scope

The independent 192-bit generator crosscheck requires `uv`, Python 3.12,
and `python-flint==0.8.0`. On a fresh machine, populate its cache once:

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/degree8_model_generator.py --both --check
```

The closure verifier then runs that pinned crosscheck offline.

```sh
lake build
bash scripts/verify_axiom_clean.sh
lake env lean research/prime_spectral/verification_2026_10_19_hard_tile/AllNewAxioms.lean
python3 experiments/prime_spectral/verify_hard_tile.py
python3 experiments/prime_spectral/time_hard_tile.py --output tmp/new-hard-tile-replay
```

The toolchain is Lean/Mathlib `v4.30.0`. The full project build passes
**3,657 jobs**. The separate audit covers every one of this round's **635**
new public declarations. All are also included in the expanded project guard,
which now audits **1,203** declarations using only `propext`, `Classical.choice`
and `Quot.sound`.
The expanded guard now correctly permits subsets of the three standard axioms;
its previous exact-list test incorrectly rejected `disk_ext` for not using
`Classical.choice`. Synthetic parser regressions check that forbidden axioms
and malformed dependency output still fail. The original guard is preserved
in the historical snapshot.

The manifest binds source, generator checks, audit logs and timing receipts.
Checksum verification checks that closure; it does not replace Lean replay.

The next mathematical obligation is a finite certified cover of the whole
closed quarter-rectangle and corresponding centre/derivative certificates.
The existing symmetry reduction can then recover the full rectangle. No
such coverage result follows from this single disk, and no claim about a
formal DH zero atlas is made here.
