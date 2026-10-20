# Actual-Xi low rectangle: numerical proof replay

Status: **verified locally**. All 44 numerical tiles and the closed-rectangle
assembly compile. The default build and its 1,619-declaration audit pass; the
separate audit matches all 1,700 new public declarations and uses only
`propext`, `Classical.choice` and `Quot.sound`. The checksum closure is recorded
by the fail-closed verifier described below. A new hosted CI result is separate
from these local checks.

This work concerns the finite region

\[
0\leq\Re s\leq1,\qquad |\Im s|\leq141/10.
\]

It does not prove RH. It does not supply a Lean-certified DH zero atlas, an
all-order PF theorem, or the remaining classical sector bridges.

## Proof construction

The optional library `XiRectangle` contains numerical certificates for 44
closed balls covering the closed quarter-rectangle
`[1/2,1] × [0,141/10]`. Each ball has a degree-12 ordinary Taylor jet for the
actual `Reinmann.xiCompleted`; these coefficients are
`iteratedDeriv k xiCompleted c / k!`. The other three parts of the rectangle
follow from the already proved conjugation and functional-equation symmetries.

The low-height evaluator uses the pole-free factorization

\[
\xi(s)=\pi^{-s/2}\Gamma(1+s/2)\,Z(s),\qquad
Z(s)=(s-1)\zeta(s),\quad Z(1)=1.
\]

`RegularizedEulerMaclaurin.lean` proves that `Z` is entire, extends the
Euler–Maclaurin identity through `s=1`, and proves the factorization including
that point. This avoids using a Taylor disk across a pole of either unregularized
factor.

`UniformXiRemainders.lean` supplies reusable bounds for every centre in the
quarter-rectangle:

- A shifted Stirling model for `Gamma(1+s/2)`, shift 12 and six corrections,
  has ordinary coefficient error at most `4e-14`, for every coefficient order.
- The regularized Euler–Maclaurin model with endpoint 27 (26 Dirichlet terms
  and six corrections) has coefficient error at most `6e-8`, for every order.
- The regular gamma factor has norm at most 2 on `-1/2 ≤ Re s ≤ 2`, at every
  height, and at most 1 on that strip when `Im s ≥ 5`.

The coefficient bounds follow from holomorphic remainder bounds on the entire
unit circle around a centre, not just a numerical value at the centre. The
regular gamma factor is holomorphic on `Re s > -2`.

The finite evaluator uses rational complex disks, proved log/exp enclosures,
and sound rules for ordinary Taylor coefficients. Proposed values are generated
externally; their acceptance is proved in Lean using rational arithmetic and
`norm_num`. There is no imported Arb verdict, `native_decide`, placeholder, or
new axiom in a production certificate.

## Tile and covering rules

The global coefficient majorant remains the proved value `M=1000`; there is
no assumed small high-height gamma estimate in the tail rule. For radius `r<1`
and degree `d=12`, the derivative bound uses the first twelve derivative terms
and the exact remaining geometric-series bound

\[
1000r^{12}\left(\frac{r}{(1-r)^2}+\frac{13}{1-r}\right).
\]

If `a0` is the rational centre-value proposal with radius `eps`, `L` is a
proved lower bound for its norm, and `K` is the derivative bound throughout
the closed ball, the final rational test is `eps + K*r < L`.

`cover_plan.tsv` records every centre, radius, degree and proposed margin.
`cover_plan.json` additionally retains exact rational margins, derivative bounds
and all coefficient centres and error radii. The radii range from approximately 0.06333 to 0.33323; four
balls meet the top edge. Proposed margins range from approximately `3.09e-5`
to `0.4784`. All corresponding tile modules now compile and prove their margins. The planner
JSON retains its external-proposal status; certification comes from Lean and the
separate certificate manifest, not from a flag set by the planner.

`RationalBallCover.lean` proves the four-corner squared-distance rule for a
closed rational rectangle. `XiRectangle.Cover` uses a finite binary subdivision
and proves coverage of every cell, including shared edges and all four outer
boundaries. There is no sampling assumption in this argument.

The final assembly proves `rectangle_nonzero` for actual Xi and
`zetaNoLowStripZero : ZetaNoLowStripZero (141/10)`. The optional wrappers
`finitePF43` and `finitePF58` use this theorem to discharge just the low-height
zero-free input. Their sector bridges, and the quasi-RH input for PF58, remain
explicit arguments.

## Build cost and reproduction

The frozen degree-eight hard-tile checkpoint is commit
`736e1dc4a78cb570f75ba902f8fa2e832fcfe3b8`. Its measured centre computation took
334.24 seconds, including 68.47 seconds for the two remainder modules and
157.51 seconds for the finite coefficient tables. Replaying the new generic
regularization and uniform-remainder modules with warm dependencies took 3.15
and 4.13 seconds, respectively. This is a measurement of those modules, not a
whole-tile speed comparison.

A complete monolithic degree-12 top-edge tile was checked in 233.87 active
seconds after its foundation build. It produced a roughly 410 MB proof object
and had a high memory peak. Production tiles therefore split the gamma factor,
four Dirichlet-term batches, the regularized zeta assembly and the final Xi
assembly into separate modules. The corrected partitioned pilot passed, but
its warm replay time is not a fresh whole-tile benchmark.

The full run uses at most four tile components concurrently, with three Lean
threads per module. Timings use Python's monotonic clock; they should not be
confused with elapsed time that includes host sleep. The complete bounded run took 6,562.03 monotonic seconds (109.37 minutes),
with all 79 batches successful. Shared dependencies and the partitioned tile-42
pilot were warm, so this is not a clean-machine benchmark. The final assembly
batch took 10.82 seconds; a cached import replay took 1.30 seconds and the full
public-theorem axiom command took 3.79 seconds. These are measured timings, not
an under-one-hour performance claim. The proof objects require substantial local
disk space and are ignored build products, not part of the release supplement.
Two recorded macOS cache-only compression passes preserved the SHA-256 and
modification time of 922 completed generated files and saved 13,729,406,976
allocated bytes. This changes physical storage only, not Lean source, proof
bytes or accepted arithmetic. The dedicated CI job instead reserves runner
disk space.

With dependencies and the pinned Mathlib v4.30.0 available:

```sh
lake build
bash scripts/verify_axiom_clean.sh
python3 experiments/prime_spectral/generate_rectangle_certificates.py --shared --tiles all --check
python3 experiments/prime_spectral/build_xi_rectangle.py --jobs 4 --output tmp/xi-rectangle-replay
python3 experiments/prime_spectral/verify_xi_rectangle.py --live-audit
```

Use fewer concurrent jobs on a memory-constrained machine. The numerical library
is separate from the default `Reinmann` target. A separate CI job builds it
serially and audits the resulting theorem dependencies. Configuring that job
does not establish a successful CI run.

The evidence directory is
`research/prime_spectral/verification_2026_10_19_rectangle/`.
Historical failed or interrupted pilots are retained as diagnostics, separately
from the completed pilots and the production `parallel/` receipts. The final
closure verifier must preserve all 1,279 bindings from the prior hard-tile
manifest, bind the current sources and successful logs, and audit every new
public theorem. The root sources/configuration refreshed this round have
checksum-bound historical snapshots rather than silently changing the old
checkpoint.

## Verified boundary and CI

`Reinmann.XiRectangle.rectangle_nonzero` has only the stated closed-rectangle
membership hypotheses. `Reinmann.XiRectangle.zetaNoLowStripZero` has no supplied
zero-free hypothesis. The PF43 wrapper still requires its sector bridge; PF58
still requires its sector bridge and quasi-RH input. No PF-to-RH bridge was
rewired, and no RH theorem is asserted.

The audit selector was corrected to include the same-line `[simp]` theorem
`regularZeta_one`; the final counts above include it. Earlier 1,618/1,699 counts
in retained diagnostics predate that correction. Both corrected audits passed.

The default build, bounded numerical build, generator comparison, source scan,
public-theorem dependency audit and checksum closure are local verification.
The separate hosted certificate job is configured in CI. This note does not
assert that a new hosted CI run has completed.
