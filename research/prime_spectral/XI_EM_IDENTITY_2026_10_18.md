# Actual zeta Euler–Maclaurin identity, 18 October 2026

Lean now identifies the actual Riemann zeta function with the order-12 finite
Euler–Maclaurin model plus the previously bounded periodic Bernoulli integral.
The continuation theorem holds for `Re s > -11` and `Im s > 0`. In particular,
it covers the **entire closed unit disk** about `1/2 + 14i` used by the external
ordinary-jet evaluator. This removes the zeta-identity obligation for that disk.

The complex Gamma evaluation identity/error, kernel-checked numerical exp/log
and jet arithmetic, and the complete hard tile remain unfinished. There is no
new zero-free rectangle, RH proof, numerical Lean tile runtime, or forecast.

## Exact statement

For a positive integer `N`, set

```text
M12(s,N) = sum_(n=1)^(N-1) n^(-s) + N^(1-s)/(s-1) + N^(-s)/2
         + sum_(j=1)^11 B_(j+1)/(j+1)! * (s)_j * N^(-s-j),
R12(s,N) = -(s)_12/12! * integral_(N,infinity) B12(fract t) t^(-s-12) dt.
```

The new theorem proves `riemannZeta s = M12(s,N) + R12(s,N)` on the stated
upper half-strip, with no assumed EM identity, zero condition, RH input, or
coefficient asymptotic. Combining it with the existing proved remainder bound:

```text
|riemannZeta(s) - M12(s,N)|
  <= |(s)_12|/12! * (6112/15015) * N^(-Re(s)-11)/(Re(s)+11).
```

`EulerMaclaurinAnalytic.hard_disk_identity` and `hard_disk_error_le` specialize
these actual-function statements to `|s-(1/2+14i)| <= 1`. The bound there is an
explicit **symbolic** bound. This round does not evaluate it uniformly to a
rational numerical constant inside Lean or enclose the 17 jet coefficients.

## Proof chain

1. `EulerMaclaurinFinite.normalized_cell` removes the alternating signs from
   the actual spatial derivative chain. The order-12 endpoint corrections are
   then collected explicitly in `one_cell`.
2. `kernel_fract` handles the closed-cell endpoint at 1 using equality of the
   Bernoulli endpoint values. `cellTail_eq` turns the local kernel integral into
   the actual periodic integral on `[N,N+1]`.
3. `finite_sum` inducts over adjacent integer cells. Both ordinary integrals and
   periodic remainders merge using proved integrability; all endpoint terms
   telescope exactly.
4. `EulerMaclaurinZeta` proves the vanishing endpoint limits and identifies the
   actual convergent Dirichlet series with zeta for `Re s > 1`. Passing to the
   improper-integral limit proves the actual-function identity there.
5. `EulerMaclaurinAnalytic.cutoff` is the fixed integrable kernel
   `1_(t>N) B12(fract t) t^(-12)`. It vanishes near zero and is `O(t^(-12))` at
   infinity. Mathlib's Mellin-transform differentiability theorem proves that
   the remainder integral is holomorphic for `Re s > -11`.
6. The analytic identity principle continues the identity along the convex
   open upper half-strip, starting in a neighborhood of `2+i`. The pole at
   `s=1` is outside this domain. We do not assert continuation on the entire
   punctured half-plane as a consequence of this particular theorem.

These are classical Euler–Maclaurin/Mellin arguments formalized with the existing
[Mathlib v4.30.0 Mellin-transform library](https://github.com/leanprover-community/mathlib4/blob/v4.30.0/Mathlib/Analysis/MellinTransform.lean).
No mathematical novelty is claimed.

## Numerical compatibility and verification

The finite model includes all eleven Bernoulli endpoint terms from `B2` through
`B12`; its six nonzero terms agree numerically with the archived Arb evaluator.
A separate Arb check compares all 17 ordinary coefficients at five centres and
three cutoffs (`N=11,13,17`), including the target centre and the lower/upper
imaginary edges of its unit disk. Every coefficient overlaps the archived model,
and each tested centre error against builtin zeta lies inside the explicit
pointwise bound. This is a consistency check, not a formal numerical enclosure
or a claim that finitely many sampled points cover the disk.

This round adds **31 public Lean theorems** across three modules. The complete
local build and semantic audit cover **425** declarations, using only Lean's
standard foundational axioms, with no project axioms or `sorry`. The baseline
`d14bb18f8109ad7723919ccb94b714eefc519491` has
[successful CI](https://github.com/sciencenerd-des/reinmann/actions/runs/39115158614).
That CI predates this round. Local build/audit results and the prior evidence
closure are recorded in `verification_2026_10_18_em_identity`.

The earlier manifests, published PDFs and released source archive remain unchanged.
Their earlier “identity not proved” flags describe their frozen historical state;
the present manifest records the stronger current theorem. The new code is not
retroactively included in the published source snapshot.

Replay:

```sh
lake build
bash scripts/verify_axiom_clean.sh
uv run --offline --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/xi_em_identity_validation.py --output tmp/em-identity-replay.json
python3 experiments/prime_spectral/verify_em_identity_round.py
```

The manifest verifier checks recorded outcomes and hashes. Rebuilding Lean and
rerunning the audit are the proof replay; rerunning Arb is the numerical replay.

## Next actual evaluator obligation

Prove a complex Gamma evaluation identity with a computable remainder, then
connect proved finite arithmetic to the zeta/Gamma jet evaluation. The existing
reflection/Beta majorants bound norms but do not determine Gamma's complex value.
The complete Lean hard-tile timing, and consequently a 35-tile timing estimate,
remain unavailable until that evaluator and the local tile are proved end to end.
