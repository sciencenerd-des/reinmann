# Height-32 finite-width PF97 candidate

**Completed update, 22 October 2026:** the complete 34-job CI gate passed at
`b4ec4a3`. The [certified closeout](PF97_CERTIFIED_2026_10_22.md) supersedes
the pending status in the historical development snapshot below.

---

The rank-97 core remains the existing proved conditional theorem
`FiniteHeightPFCalibration.finitePF97_of_low_height_width`:
the first-zero bound 14.1 and `LowHeightWidth (9/40) 32` imply
`FinitePF XiMomentCoeff 97`. The new numerical obligation is the right-hand
box `[29/40,1] × [14.1,32]`; the existing full rectangle handles the lower
part. This does not assert that the full critical strip is zero-free below 32.
Zeros on the critical line remain allowed.

The shared height-32 evaluator inputs were compiled and audited in the PF58
round. No constant is extrapolated: the unit-circle Xi bound is 1000, the
Gamma coefficient error is at most 4e-14, the regularized endpoint-27 zeta
coefficient error is at most 1/5000, and the scaled principal-log enclosure uses
160 terms on a radius-4/5 disk. The exact finite expression and ordinary-jet
soundness rules are unchanged between the two boxes.

The Arb plan, already retained with the PF58 inputs, has 67 degree-16 balls.
All 473 proposed source files reproduce exactly from that plan. The complete
rational covering theorem compiles. One complete high tile, `Tile066`, at
`69/80 + (81741/2560)i`, has passed the Lean kernel check. Its Gamma module took
182 seconds and its full eight-batch pilot took 432 seconds. The actual
nonvanishing theorem has only `propext`, `Classical.choice` and `Quot.sound`.
The checksum-bound pilot receipt is in `verification_2026_10_21_pf97_pilot/`.

**This snapshot does not certify the full PF97 box or unconditional PF97.**
Only one of the 67 numerical tiles has been checked locally. The remaining
tiles and final assembly must pass the split CI and semantic audits. The
planned extension has seventeen PF97 shards, with at most four tiles each and
Gamma modules built serially per runner. The last shard contains exactly
tiles 64, 65 and 66. That extension is now activated after all seventeen PF58 jobs passed at `1d97a06`
(run 39730502820). The combined workflow requires thirty-four successful jobs.

This is finite strengthening of classical zero-location information, not an
RH discriminator. The earlier DH register, stopped research directions,
external seven-eighths reproduction, and published paper versions are unchanged.
