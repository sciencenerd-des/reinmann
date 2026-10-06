# Increasing-support audit and independent Xi moment comparison

Update (2026-09-23): the [matrix perturbation certificate](PERTURBATION_KERNEL_2026_09_23.md)
now resolves cutoff 31, mode 16. The unresolved classification below
describes the original direct interval eigenpair method at the time of
this audit; it is not the current finite result. The three saved
variance comparisons remain unchanged.

## Findings

At mode count 16, the isolated-eigenpair and whole-support positive-kernel
gates pass at prime-power cutoffs 17 and 23 as well as the previous cutoff
13. At cutoff 31, the even-block eigenpair isolation is unresolved; the
odd block isolates with a positive first eigenvalue near 4.02776e-41.
This is not a negative-spectrum or negative-kernel finding at cutoff 31.

The independently certified Xi theta-measure variance is

    V_Xi=2*mu_1/mu_0=0.046209986230837941577867620860678...,

where mu_n=[z^(2n)]xi(1/2+z) are the existing ordinary coefficients.
They are used only for this post-construction target audit. They do not
enter the prime matrices, eigenvectors, gates, or kernel definitions.

| Cutoff | Modes | Certified kernel variance (approximately) | Variance excess over Xi | W2 distance lower bound |
|---|---:|---:|---:|---:|
| 13 | 16 | 0.04897499407765188 | 0.00276500784681394 | >0.00633786 |
| 17 | 16 | 0.05328233626932298 | 0.00707235003848504 | >0.01586458 |
| 23 | 16 | 0.05857329755526394 | 0.01236331132442600 | >0.02705412 |

Exact enclosures and conservative rational distance bounds are saved in
`support_variance_audit_13_17_23.json`. The variances increase across these
three support cutoffs at fixed mode count. That differs from the decreasing
variances seen when increasing modes at cutoff 13. No monotonicity theorem
in either parameter is inferred from these finite comparisons.

## 1. A rigorous distributional mismatch, not just a plot

Let nu be one of the certified even prime probability measures, and let
nu_Xi be the normalized even measure from Xi's theta representation.
Both have finite second moments. For any coupling (X,Y) of the measures,
the triangle inequality for the L2 norm gives

    sqrt(E[(X-Y)^2]) >= |sqrt(E[X^2])-sqrt(E[Y^2])|.

Taking the infimum over couplings proves

    W2(nu,nu_Xi) >= |sqrt(V_nu)-sqrt(V_Xi)|.           (1)

Thus the last column is a rigorous lower bound for each finite measure's
quadratic Wasserstein distance to the intended target. No optimal transport
algorithm or RH assumption is needed. The target variance follows directly
by differentiating the normalized theta Fourier representation at zero.

These nonzero finite distances do not rule out convergence on another
sequence, or after increasing the modes at a given support. Nor do they
prove that the actual W2 distances increase: increasing lower bounds alone
cannot establish that. They exclude only unjustified claims that the shown
kernels already equal the Xi measure or that their variance trend is
independent of how the two cutoffs change.

## 2. Implication for an admissible convergence path

The prior grid-tail theorem requires N/(log cutoff)^2 to tend to infinity
for the unmodified Fourier profiles to converge to Xi. Keeping N=16 while
letting the support grow cannot meet that requirement. The present finite
experiment is a gate and conditioning test, not a proposed infinite path.

The variance identity also gives an explicit necessary inequality. Since
the quotient inverse-square sum S is positive,

    V/2=S+(L^2/(4pi^2))*sum_(k>N)k^(-2)
       >=L^2/[4pi^2*(N+1)].

Consequently any sequence with V<=M must satisfy

    N+1 >= L^2/(2pi^2*M).                            (2)

This is only a necessary finite constraint; the stronger asymptotic
condition for the Xi target still applies. The lower bound cannot replace
an upper variance estimate or prove weak convergence.

At cutoff 31, unresolved isolation is an additional numerical limit of
the current procedure, not evidence that the admissibility condition or
RH fails. Resolving it needs better eigenpair or matrix error control;
silently accepting approximate eigenpairs would not be a valid continuation.

## 3. What was saved and checked

New prime-only certificates:

* `isolated_kernel_17_16.json`
* `isolated_kernel_23_16.json`

Each records the complete isolated block spectra, boundary normalization,
Bernstein coefficients and variance, under the unchanged source hashes.
The independent audit additionally records the target coefficient file
hash, prime certificate hashes, variance differences and exact lower bounds
from (1). It contains no fitted parameters.

Reproduce the new prime certificates with:

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/isolated_kernel.py --cutoff 17 --modes 16 --output research/prime_spectral/isolated_kernel_17_16.json
uv run --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/isolated_kernel.py --cutoff 23 --modes 16 --output research/prime_spectral/isolated_kernel_23_16.json
```

To reconstruct the audit, load each certificate's variance interval and the
first two coefficient intervals of `research/certified_xi/coefficients_120.json`,
compute V_Xi=2*mu_1/mu_0 with outward ball arithmetic, and use the lower
endpoint of sqrt(V)-sqrt(V_Xi). All three differences are strictly positive.
The coefficient generator hash and every prime source hash were verified.

No code was changed in the gate for this audit. The new finite inputs were
actually run through its certified checks. Uniform gates, a suitable
increasing-support/mode path, variance control and weak identification with
the Xi measure remain unproved. This work does not prove RH.
