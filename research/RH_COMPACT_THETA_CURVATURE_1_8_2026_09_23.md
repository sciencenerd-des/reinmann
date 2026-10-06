# True-theta curvature on the compact interval [1,8]

Let `I(x)` be the theta moment integral in
[`RH_CONTINUOUS_THETA_2026_09_14.md`](RH_CONTINUOUS_THETA_2026_09_14.md),
`q(x)=x(2x-1)I(x-1)I(x+1)/((x+1)(2x+1)I(x)^2)`, and
`epsilon(x)=(x+1)(1-q(x))`. The coupled midpoint and derivative covers
certify, for **every real** `x` in `[1,8]`,

```
0 < q(x) < 1,
(log epsilon)''(x) <= -97765/274877906944 < 0.
```

The new `[3,8]` cover has 1,812 positive cells and no unresolved cells.
It joins the existing `[1,2]` and `[2,3]` covers at exact rational
endpoints. The three covers have 2,830 cells in total, and their four
numerical source hashes agree with each other and with the current files.
The rational union verifier checks each cell's mean-value witness, strict
sign, provenance settings, and exact adjacency. Its common curvature
margin is the minimum of the 2,830 certified upper endpoints.

For each integer `n=2,...,7`, integrating the curvature bound against
the unit-mass tent kernel on `[n-1,n+1]` gives the quantitative finite
inequality

```
epsilon(n)^2 >= exp(97765/274877906944)
                * epsilon(n-1) * epsilon(n+1).
```

This is a finite compact-domain result for the **true theta integral**.
It does not extend the frozen degree-16 reference to all anchors: that
reference has [certified positive curvature at anchors 1 and 6](RH_LOW_ANCHOR_REFERENCE_COUNTEREXAMPLE_2026_09_23.md),
so its proposed all-anchor negative sign is false. The true-theta interval
`(8,10^6)` remains outside this cover and the existing uniform tail theorem.
More decisively for RH, rank-two theta curvature supplies no uniform
interior rank-and-shift budget. The negative `C_r(4)` values and the
repeated-root control rule out simply assuming nonnegative corrections or
a strictly positive limiting rank slope.

Replay from the repository root:

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/coupled_cover.py --lo 3 --hi 8 --max-depth 16 --max-cells 20000 --output research/certified_xi/coupled_cover_3_8.json
python3 experiments/certified_xi/verify_cover.py research/certified_xi/coupled_cover_1_2.json research/certified_xi/coupled_cover_2_3.json research/certified_xi/coupled_cover_3_8.json --output research/certified_xi/coupled_cover_1_8_summary.json
uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/certified_xi -p test_continuous_theta.py -v
```

The numerical trust boundary is the written theta identity, explicit tail
bounds, monotone split quadrature, FLINT/Arb ball arithmetic, and the
mean-value theorem. The union verifier checks serialized rational evidence;
it does not independently prove the numerical integration. This theorem is
not formalized in Lean, and it does not prove RH.
