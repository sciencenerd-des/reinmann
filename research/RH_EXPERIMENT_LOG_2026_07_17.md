# RH Open-Input Experiment Log

**Status:** numerical/algebraic evidence only; no experiment is an RH proof.

## Formal targets audited before experiments

The active Lean surface contains explicit proposition targets and conditional
capstones for:

- `HermitePoulainSchurSzegoTheorem` and its checked degree-1/degree-2/cubic
  coefficient fragments;
- `XiOrder3PositiveScaledLimit` and
  `xiToeplitzMinor3_eventually_nonneg_of_scaled_limit`;
- `PolyaJensenBridge` and
  `riemannHypothesis_of_xiLaguerrePolyaScaledFinite`;
- `riemannHypothesis_of_pf_and_classical_inputs` as the total-positivity
  conditional capstone.

`AxiomAudit.lean` checks these reductions with no project-declared axioms.

## Experiment 1: arbitrary-row initial-column minors

Command:

```text
python3 scripts/arbitrary_row_minor_scan.py --max-row 30 \
  --output-json /tmp/rh_minor_scan30.json \
  --output-md /tmp/rh_minor_scan30.md
```

The stored-decimal interval enclosures gave:

| order | certified positive | certified negative | inconclusive |
|---:|---:|---:|---:|
| 3 | 4,495 | 0 | 0 |
| 4 | 31,465 | 0 | 0 |

This strengthens the finite falsification check but does not prove the
coefficient cache, the Pólya representation, or an infinite-order theorem.
The tightest margins are extremely small, so a proof will need normalized
determinants and explicit error control rather than raw determinant estimates.

## Experiment 2: normalized ratio diagnostics

Using exact `Fraction` arithmetic on the stored decimal strings (with the
repository's stated enclosure caveat):

- 121 signed coefficient values were available;
- the normalized order-2 Turán slack stayed positive, with the smallest
  observed value about `0.01291825947` at offset `118`;
- the normalized order-3 ratio gap was positive at every tested offset;
- `(n+1)^3 * ratioGap` increased from about `0.0782` at offset `0` to about
  `6.7441` at offset `116`.

The last observation is evidence for a positive scaled tail, but it does not
identify a limit or provide an effective analytic remainder bound. The next
mathematical target is therefore an explicit Xi asymptotic with a certified
positive lower margin in the exact `momentToeplitzOrder3RatioExpr` convention.

## High-precision rerun

`mpmath` 1.3.0 is available in the active Python 3.14 environment.  The
repository defaults (`80` digits and the larger Taylor request) were too slow
because repeated complex zeta evaluations did not finish within the bounded
run window, so a controlled `60`-digit, `N = 8` run was used:

- `mu₀, …, mu₈` matched the stored coefficient cache to the displayed digits;
- order-2 Turán slacks for offsets `0..6` were
  `1.149687885`, `0.594115499`, `0.405737775`, `0.310063099`,
  `0.251855007`, `0.212569287`, and `0.184199180`;
- contiguous moment minors remained positive through `k = 4` in the tested
  window (for example, the first `k = 3` values were approximately
  `1.4705e-13`, `2.2300e-20`, `1.4114e-27`, `4.3714e-35`);
- Jensen root checks returned zero imaginary parts for degrees `2`, `3`, and
  `4` over the converged offsets; the degree-4 solver failed to converge at a
  later offset, which is a numerical limitation rather than a sign result.

These computations strengthen the diagnostic evidence but still do not provide
the explicit Xi remainder estimates or all-degree theorem required by Lean.

## New mathematics indicated by the experiments

1. **Order 3:** derive the Xi moment asymptotic through at least the first
   error term, then turn it into an explicit tail bound for the normalized
   ratio gap.
2. **All orders:** replace finite positivity evidence by a theorem that
   propagates contiguous kernel positivity to every order, with zero-pivot and
   strictness cases handled explicitly.
3. **Jensen bridge:** formalize the locally-uniform entire-function theorem and
   the exact Pólya coefficient convention; fixed-degree asymptotics are not a
   substitute for all-degree/all-shift hyperbolicity.
4. **Composition:** formalize the same-sign Schur–Szegő root-location argument
   in the binomial basis; the unrestricted statement is false and is guarded
   by a checked counterexample in `HermitePoulainComposition.lean`.
