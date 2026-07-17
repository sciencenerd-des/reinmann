# RH Jensen/Schur–Szegő Literature Review

**Review date:** 2026-07-17  
**Scope:** the three blockers in the Lean RH route: the general
Hermite–Poulain/Schur–Szegő composition theorem, the Xi-specific scaled
`k = 3` asymptotic, and the Pólya/Jensen bridge.

## Primary and reference sources

1. **Griffin–Ono–Rolen–Zagier (2019),**
   [Jensen polynomials for the Riemann zeta function and other sequences](https://arxiv.org/abs/1902.07321).
   The paper states the Pólya equivalence and proves an all-orders asymptotic
   expansion for central derivatives.  It obtains hyperbolicity for a density-one
   subset of each degree and all degrees `d ≤ 8`; this is not a proof for every
   shift and degree.

2. **Griffin–Ono–Rolen–Thorner–Tripp–Wagner (2022),**
   [Jensen Polynomials for the Riemann Xi Function](https://arxiv.org/abs/1910.01227).
   This is the effective Xi result.  It makes eventual hyperbolicity effective
   for each fixed degree and relates the exceptional range to low-lying zeros of
   derivatives of `xi`.  The abstract does not provide the Lean-level moment
   representation or a uniform all-degree certificate.

3. **Craven–Csordas (1982),**
   [On the number of real roots of polynomials](https://msp.org/pjm/1982/102-1/pjm-v102-n1-p03-s.pdf).
   This paper records the historical Hermite–Poulain, Schur, and Pólya
   composition results and explains the same-sign-root hypothesis.  It supports
   keeping the unrestricted Hadamard statement out of the Lean target.

4. **Craven–Csordas–Smith (survey),**
   [Composition theorems, multiplier sequences](https://math.hawaii.edu/~tom/mathfiles/czdssurvey.pdf),
   Theorem 2.4(4).  In the binomial coefficient convention, if both input
   polynomials are real-rooted and one input has all roots of the same sign,
   then the Schur–Szegő composite is real-rooted.  This is the exact classical
   shape mirrored by `PolynomialRootsSameSign` and
   `HermitePoulainSchurSzegoTheorem` in the repository.

5. **Griffin et al.,** [Journal version](https://doi.org/10.1016/j.aim.2022.108186).
   This confirms the publication status and the effective nature of the Xi
   Jensen result; it does not change the logical scope of the arXiv theorem.

## Translation into the Lean proof surface

| Mathematical result | Lean status | Remaining work |
|---|---|---|
| Same-sign Schur–Szegő preservation | Degree 1 and coefficient-level degree 2 are proved; the general target is named | Formalize the full finite-degree root-location argument, including the exact binomial convention and zero-root cases |
| Effective Xi Jensen asymptotics | Generic `XiOrder3PositiveScaledLimit` and tail extraction are proved | Translate explicit Xi estimates into the exact `momentToeplitzOrder3RatioExpr` convention and prove positivity of the limiting constant |
| Pólya/Jensen equivalence | `PolyaJensenBridge` is an explicit proposition target | Formalize the analytic approximation, coefficient convergence, and converse/forward hyperbolicity implications |
| RH conclusion | Only conditional reduction theorems exist | Supply all three missing mathematical inputs; no current file proves `RiemannHypothesis` unconditionally |

## Research conclusion

The literature validates the architecture and the corrected same-sign
composition hypothesis.  It does **not** supply a ready-made proof of the
repository’s exact Lean statements: the published Xi work is effective for
fixed degree, whereas the Pólya criterion is an all-degree/all-shift statement,
and the analytic estimates still need a convention-preserving formalization.
The next sound implementation step is therefore a full finite-degree
Schur–Szegő formalization or a direct Lean translation of the Xi asymptotic
constants—not an axiom or an unconditional RH theorem declaration.
