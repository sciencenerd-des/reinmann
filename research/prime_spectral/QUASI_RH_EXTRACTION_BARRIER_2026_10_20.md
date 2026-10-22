# The alternate 11/12 argument and what its extraction bound can deliver

This reconstructs the reduction in the [alternate October 5 manuscript](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Quasi-Riemann-Hypothesis-October-5-2026/build/paper2.tex),
sections 2–3, conditional on its central mean-square proposition. It is not an
independent proof of that proposition or a review of every theta calculation.
The 7/8 paper and the independent verifier's row-density model are separate.

## Arithmetic input and notation

Write mu_K for the ideal Mobius function on K=Q(sqrt(-3)), to avoid confusion
with our ordinary Xi Taylor coefficients mu_n. With a fixed finite-order Hecke
character nu and a smooth compactly supported W, define

    M_nu(D) = sum_n mu_K(n) nu(n) W(N(n)/D).

Embed this in the sextic-twist family M_{nu,u}(D). The load-bearing input is
an averaged estimate of size D^(1+epsilon) H for the squares of these sums,
in the range H=D^(1+theta), theta>0. The source proves it through Poisson,
cubic Gauss sums, theta reflection, a quadratic large sieve, cube inversion
and transfer estimates. These steps are not replaced by a density heuristic.

## Reconstruction in our notation

For a prime ideal p with norm about Y=H^(1/6), the sixth-power row satisfies

    M_{nu,p^6}(D) = M_nu(D) + O(D/Y).

There are about Y/log(Y) such rows. Taking their contribution out of the
nonnegative family mean square gives, suppressing D^epsilon losses,

    |M_nu(D)|^2 <= D H^(5/6) + D^2 H^(-1/3).

With H=D^(1+theta), the square-root exponents are

    11/12 + 5 theta/12,     5/6 - theta/6.

Letting the requested exponent loss absorb theta gives the 11/12 bound.
A Mellin transform identifies the generating transform with W-hat/L_K^S;
choosing W-hat nonzero at a putative zero gives the zero-free half-plane.
The family estimate and extraction are arithmetic input; the Mellin step is
an analytic conversion of that bound, not additional cancellation.

## A rigorous barrier for this particular bound, not for arithmetic generally

Keep exactly the two extraction terms but hypothetically let H=D^h. The bound
then has exponent

    sigma_bound(h) = max(1/2 + 5h/12, 1 - h/6).

Elementary algebra gives sigma_bound(h)>=6/7 for every h, with equality at
h=6/7. Indeed, a weighted average of its two arguments, with weights 2/7 and
5/7, is exactly 6/7. In the actually proved range h>1, its infimum is 11/12.
Thus even extending the same mean-square bound to shorter rows would not,
with this unchanged extraction and error term, reach exponent 1/2.

This is an optimization of an **upper bound**, not a lower bound on actual
Mobius sums or a theorem prohibiting stronger arithmetic estimates. The 1/6
in this alternate proof comes directly from the sparsity of sixth-power rows.
It should not be conflated with the zeta_K(6z) pole in the other paper's
Mellin normalization. Nor is it a density barrier in this alternate argument.
The quadratic large sieve is crucial upstream to proving the mean square;
the final 11/12 exponent is the extraction cost after that estimate is granted.

The [independent 7/8 barrier report](https://github.com/tomoto0/quasi-riemann-hypothesis-7-8-verification/blob/b83a73c6cb626a391e551baafdb7d0cceafaa55a/reports/barrier_analysis.md)
analyses a different parameterized row-count model, and labels extrapolations
outside the proved lemma ranges as optimistic. Its approximate 0.8745 fixed
point is not a theorem about every metaplectic method. We stop retuning this
extraction as a proposed route to RH; the algebra above already excludes that
use of the unchanged bound. No new forecast or density optimization is begun.

## DH discriminator

The reciprocal coefficients for a multiplicative Hecke Euler product are
mu_K(n) nu(n). Their arithmetic identities let sextic Gauss sums absorb the
Mobius factor into cubic theta coefficients, and multiplicativity supports
cube inversion. Actual DH reciprocal coefficients are not of that form.
Defining a formally similar DH family does not supply its theta reflection
or mean-square estimate. This is the precise missing step in a DH transfer.
Functional symmetry and positive ordinary Taylor coefficients do not supply it.

## Can the estimate be fed to positivity instead?

It supplies a norm bound on a specified arithmetic family. It does not assert
the sign of a Weil form or a rectangular Schur function. A valid transfer would
first express the actual retained-to-complement coupling in that family, with
its exact coefficient dependence, and derive an inequality such as

    B* D^(-1) B <= epsilon(C) Q_low,   epsilon(C)<1,

on the same form domain. The identity, constants and full complement control
are absent. Positive power sums alone also fail to give Schur positivity; see
`CornerPowerSumCounterexample.lean`. Consequently this transfer is an
uninstantiated proposal, not an active RH strategy or a new theorem.

For finite calibration, a half-plane sigma combined with reflection bounds
|beta-1/2| by sigma-1/2; the existing low-height and sector machinery converts
that into one fixed PF rank. That is exactly the finite use already made of
7/8, not a path to unbounded rank.

## General row-density audit (22 October 2026)

The [new source audit](ROW_DENSITY_AND_CUBIC_OBSTRUCTION_2026_10_22.md) proves
the conditional k/(k+1) optimization and separates it from the actual h>1
range. It also identifies why replacing sextic rows by cubic rows does not
preserve the Mobius-to-theta identity or quadratic large-sieve step. In
particular k=3 gives 5/6 in the old range, while 3/4 needs an additional short-
family theorem; k=1 has all h>=1/2 as minimizers. No stopped extraction search
is restarted by that algebra.
