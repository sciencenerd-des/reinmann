# Control calibration and certified-symbol comparison — 13 October 2026

The q = 17 forecast passes the specified empirical test. An exact rational witness proves a negative full-form value at C = 133.751953125, inside the recorded [126,154] forecast band. The requested symbol-tail refinement is implemented and certified, but the hoped-for comparison dimensions do not follow: late dips force large cutoffs. A separate controls manuscript is drafted.

These results are calibration and certificate engineering. They do not prove RH, a universal window-to-zero implication, or a new full-window positivity record.

## 1. Complete atlases before window fitting

All counts below are upper-half-plane multiplicity counts in a zero-excluding full rectangle. “Off pairs” counts right-hand disks; reflection supplies the left-hand zeros. Counts are exhausted by disjoint simple disks and line sign brackets. Absolute Dirichlet tails bound the horizontal strip. The Epstein target is the entire function (s−1)E(s,Q)/2, with its completion regularized at both 0 and 1.

| Control | Height | Total | Line | Off pairs | Lowest right-hand off-line zero, rounded |
|---|---:|---:|---:|---:|---|
| Classical DH | 340 | 249 | 235 | 7 | 0.8085171825 + 85.69934849i |
| q=7, Conrey label 3 | 160 | 107 | 93 | 7 | 1.0356987161 + 31.58036054i |
| q=11, label 2 | 160 | 118 | 118 | 0 | None below 160; excluded from fitting |
| q=13, label 2 | 160 | 123 | 113 | 5 | 0.5836215560 + 31.43420501i |
| q=13, label 6 | 160 | 122 | 104 | 9 | 0.8621740581 + 25.60874641i |
| q=17, label 3 | 160 | 130 | 128 | 1 | 0.6633061848 + 105.15528688i |
| Epstein x²+5y² | 120 | 133 | 101 | 16 | 0.9329696975 + 15.66824953i |
| Epstein x²+6y² | 120 | 136 | 104 | 16 | 0.8037491286 + 15.11757853i |

The classical DH atlas and global steepest-angle proof are retained from the preceding round. The seven new atlases have a separate higher-precision replay: 320-bit contour images and line signs, 640-bit Rouché gates, containment, disjointness and exact exhaustion. This uses the same FLINT backend, rather than an independent analytic implementation.

The q=17 zero at 105.1553 is therefore the lowest off-line zero, not merely the first one discovered by Newton iteration. No new global-steepest claim is made for these other controls. The q=7 zero lies outside the usual zeta critical strip, an explicit limitation of extrapolation.

## 2. Seven common-degree negative-window upper bounds

All final calibration trials use N=192 in both real parity sectors and 2,048-bit interval arithmetic. C=e^(2L), with support [−L,L]. Exact rational vectors and normalized geometric-form quotient enclosures are retained.

| Control | Positive finite section C | Certified negative C | r |
|---|---:|---:|---:|
| DH5 | 4014571/131072 | 1003691/32768 = 30.630218505859375 | 0.449141 |
| q13(2) | 138241/4096 | 17281/512 = 33.751953125 | 0.518959 |
| Epstein5 | 81205/4096 | 20303/1024 = 19.8271484375 | 0.399277 |
| q17(3) | 34237/256 | 68481/512 = 133.751953125 | 0.470111 |
| q7(3) | 852533/65536 | 426333/32768 = 13.010650634765625 | 0.369797 |
| q13(6) | 691375/32768 | 1382897/65536 = 21.101333618164062 | 0.398252 |
| Epstein6 | 520653/16384 | 1041423/32768 = 31.781707763671875 | 0.478278 |

Here T*=2πC/q for degree-one character completions and T*=π√(C/d) for the degree-two Epstein forms; r=T*/γ for the lowest off-line zero. This leading-density normalization is a model coordinate, not a theorem about detection.

The negative endpoints are full-form certificates. The positive endpoints concern only the tested finite sections. Dilated Fourier trial spaces are not nested, and no monotonicity theorem is used. These searches do not bracket a minimum negative full support.

### q=17 prediction and resolution

The forecast C=140 with ±10% band was saved before its new window trials. The observed N=192 negative endpoint is 4.4629% below 140. Reconstructing linear interpolation from only the original bracketing controls gives C≈141.14; that specific reconstruction was calculated after the test and is not a preregistered algorithm.

Degree 80 remains positive at all tested points through 200. Degree 128 detects a negative trial near 134.09, and degree 192 at 133.752. At degree 256 the tested section is positive at 133.5 and an exact witness is negative at 133.73828125. This checks finite-family resolution without turning any positive section into a full positivity claim.

### Descriptive fits and attribution

The seven-point fit is r≈0.541313−0.322085b, with r-RMSE≈0.01826. Adding a degree term gives r≈0.540344−0.340917b+0.024014(degree−1), with RMSE≈0.01494. Largest absolute leave-one-out C errors are approximately 16.3% and 19.6%, respectively. The degree effect has only two Epstein observations and is not established.

Every atlas disk used for attribution is refined to radius 10^−120 and checked against its parent. The largest negative quartet in each of the seven finite sums is the lowest off-line pair. The q=7 witness is odd; the other selected witnesses are even.

This is mechanism evidence. In every case the finite total has magnitude more than 100 times the tiny certified geometric quotient, so omitted contributions are material. No independently negligible infinite-tail bound is claimed. The physical Fourier basis contains a coordinate phase (−1)^n; the final transform includes it and agrees with independent direct integration, including removable poles.

The data do not imply that zeta positivity at C rules out every off-line zero below 12C. A universal conclusion additionally requires uniform offset, multiplicity, local cancellation and tail estimates, including the untested b→0 regime.

## 3. Certified actual-comb tails: improvement exists, success criterion fails

The comparison symbol is

Ψ_C(t)=Re ψ(1/4+it/2)−log π−Σ_(p^k<C) 2log(p)/√(p^k) cos(t log(p^k)).

The [existing Binet proof](WINDOW_POSITIVITY_PROOF_2026_10_07.md) gives Re ψ−logπ≥log(t/(2π))−1/t for t≥4. The new code interval-subdivides this lower envelope with the **actual oscillatory comb**, then uses the increasing triangle envelope beyond T_global. Sampling selects candidates only; every accepted panel is enclosed and the infinite continuation is analytic.

| C | Tail floor β | Certified T₀ | T_global | Accepted panels | Full polynomial count | Per parity |
|---|---:|---:|---:|---:|---:|---:|
| e² | 0.31 | 2449 | 2984 | 211 | 6690 | 3345 |
| e² | 0.50 | 3101 | 3608 | 197 | 8464 | 4232 |
| 9.5 | 0.31 | 7099 | 10129 | 1263 | 21758 | 10879 |
| 9.5 | 0.50 | 8477 | 12248 | 1592 | 25974 | 12987 |

The actual digamma symbol is negative near t=1549.91 for e² (about −0.317), and near t=1549.925 for 9.5 (about −1.516). Certified later dips are below 0.5 near 3099.895 and 8475.8, respectively. Thus the large cutoff is not merely an artifact of discarding comb oscillation.

The reported dimensions are the smallest even counts for the existing analytic polynomial coupling-plus-tail budget <10^−10, at those certified cutoffs. They are not optimal lower bounds over all comparison methods. No comparison matrices at those dimensions were assembled and no outer-gap, projector-distance or compressed-block positivity certificate was produced.

The e² count improves over 11168, but stays above the requested 2000, even per parity. The 9.5 comparison is still costly. This round therefore does **not** independently check Liu's window.

This limitation also appears in [Zhu v2, §7](https://arxiv.org/html/2608.24827v2): actual-symbol refinement leaves late dips and a large polynomial comparison cost. The same active prime powers through 9 explain the comparable late-frequency obstruction. This is acknowledged prior art, not a novelty claim.

## 4. Controls paper and the allowed Toeplitz theory follow-up

Draft: [How sensitive are finite RH criteria? Certified Davenport–Heilbronn controls](../../paper/dh_controls_paper.pdf), with [editable source](../../paper/dh_controls_paper.tex).

The paper retains PF435 as a **sufficient guarantee** and the passing 18,291 solid-minor grid as a finite result. It makes no PF520 assertion and does not locate the globally first failing minor. No new Toeplitz scan was run.

An elementary masking example gives a precise theory follow-up. For 0<c<1, G(w)=(1+4w)(1+2cw+w²) has nonreal zeros, but

D_(r,1)(G)=Σ_(j=0)^r 4^(r−j) U_j(c) ≥ (2/9)4^r >0

for every r. The bound follows from |U_j(c)|≤j+1. Multiplication can therefore conceal the quadratic's negative minors forever along one fixed-shift ladder. This does not prove the full DH grid and is not presented as a novel general positivity theorem.

For DH itself, the complete atlas also gives a direct asymptotic result. Its first two critical-line ordinates lie in (81/16,41/8) and (143/16,9); the first off-line zero is above 85. Consequently F has a unique simple zero −a in |w|≤64, where a=γ₁²<64. If B(w)=F(−w), then A=−1/(aB′(a))>0, and subtracting A/(1−w/a) from 1/B leaves a function analytic on a neighborhood of that disk. Cauchy's estimate yields D_(r,1)(F)=A a^(−r)+O(64^(−r)), so the DH shift-one ladder is eventually strictly positive. This dominant-pole argument is included without a novelty claim; it gives neither an explicit last exceptional rank nor positivity at all shifts.

Credit is explicit: all seven classical off-line centers were already reported by Spira and Balanzario–Sánchez-Ortiz; Bombieri–Ghosh provide character-combination background; the [teal-sea/zeta-lab report](https://github.com/teal-sea/zeta-lab/issues/57) already found DH negativity near C=31. The added evidence is complete interval accounting, angular comparison, the specified grid and multi-control calibration. Public archival release and external review remain pending.

## 5. Retired work and the remaining mathematical obligation

Per the user's directions, retire further Toeplitz scans, the tested D6 induction, arithmetic ablations, and the D2 exact-count search. Modified arithmetic forms have no corresponding supplied zero side; their signs are not interpreted as zero attribution. The approximate slope-two prolate count is prior art.

D3 remains background mathematics. The [localized packet note](LOCALIZED_TURAN_PACKET_2026_10_12.md) still needs joint complex partial-sum, filter and infinite-tail control. Neither the empirical fit nor local O(log γ) zero counting supplies the missing universal Φ.

The defensible outputs of this round are the controls paper, a successful q=17 forecast test with stated resolution limits, and measured feasibility of certified-symbol comparison. A new comparison architecture is needed before practical larger-window positivity certification can be claimed.

A concrete engineering candidate is to bound concentration of support-limited Fourier transforms in the late negative-symbol pockets, instead of demanding a pointwise positive floor at every frequency. Such a bound would use the widths and depths of the pockets together with a certified time–frequency concentration operator and its coupling to retained modes. This is an untested next candidate, not a result of this round. The actual negative symbol values do not by themselves disprove positivity on the support-limited test space.

## 6. Verification and reproduction

The new nine-test suite checks independent integral entries and transforms, genus coefficients against representation counts, removable-point images, fresh higher-precision assembly of all seven final negative witnesses, every symbol panel and counterexample, finite-attribution phase and dominance, and unchanged mathematical functions across matrix-storage compaction.

The new atlas replay is separate from those nine tests. All classical DH and Toeplitz evidence remains linked to the preceding round's replay and targeted Lean audit; this continuation adds no new Lean claim and runs no new root build.

From the worktree root:

~~~sh
uv run --with python-flint==0.8.0 --with mpmath --with numpy --python 3.12 python -m unittest discover -s experiments/prime_spectral -p test_control_calibration.py -v
uv run --with python-flint==0.8.0 --with mpmath --with numpy --python 3.12 python experiments/prime_spectral/replay_control_atlases.py
python3 experiments/prime_spectral/verify_calibration_round.py
~~~

The compact supplement retains exact witnesses, pivot/quotient balls, source snapshots and hashes. Removed full matrix arrays are regenerable. Source equivalence for the mathematical entry and quotient functions is tested; compaction preserves a canonical mathematical-core digest.

No commit, merge, publication, full-window record or RH proof is claimed.
