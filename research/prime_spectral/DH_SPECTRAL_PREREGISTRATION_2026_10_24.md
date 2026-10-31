# DH spectral diagnostic: preregistration, 24 October 2026

This records the experiment before implementation or inspection of its output.
It instantiates a missing negative control, not a proposed RH-separating lemma.

Conventions: `C = lambda^2`, support in log coordinates `[-log(C)/2,
log(C)/2]`, centered periodic Fourier modes through `N` in each direction.
The orthonormal even basis is `1/sqrt(L)`,
`sqrt(2/L) cos(2 pi n (t+L/2)/L)`; both parity blocks must be tested.
The DH matrix is the existing conductor-5, odd-gamma, pole-free geometric
form with **all** coefficients of `-H'/H`, including non-prime-powers.
The DH Dirichlet coefficients are `a_n=(1,kappa,-kappa,-1,0)` periodically.

The zeta comparison uses the existing `E(h_C)` candidate (even prolate modes
0 and 4 with zero integral). For DH, define
`k_C(t)=exp(t/2) sum_{1<=n<=C} a_n h_C(n exp(t))`, where `h_C` is the first
odd prolate mode on `[-sqrt(C),sqrt(C)]`, with angular parameter `2 pi C/5`,
extended by zero. Its Gaussian limit is proportional to
`x exp(-pi x^2/5)`. This gives the odd gamma factor, rather than zeta's
even gamma factor. Indeed the full Mellin transform is
`H(s) int_0^infty h(x) x^(s-1) dx`, with `s=1/2-iz`; for this Gaussian
the integral is `(1/2)(5/pi)^((s+1)/2) Gamma((s+1)/2)`.
No theorem identifying this DH prolate trial with a ground state is assumed.
Measure reflection defect before projecting onto the even basis.

Initial finite diagnostic: `C=10,13,14,20,31,35`, `N=32,64`, with higher
precision replays at selected windows. Track simple-even ordering, the
global parity gap, nonzero boundary value, real transform roots to height
100, and offsets from retained DH line-zero disks. The suggested boundary
`85.7/(2 pi) ~ 13.6` is a heuristic prediction from the handoff, **not** a
theorem or a conductor-adjusted resolution threshold. Failure may occur
earlier, later, or through rank instability. We do not assert these are all
complex zeros, nor that the first observed discrepancy is globally first.

For each unit projected candidate record its Rayleigh value `mu`, residual
`r=||(A-mu)k||`, overlap with the finite even ground vector, `r/gap`, and
`lambda_2-mu`. Only positive latter clearance permits the usual residual
ground-distance argument. A small `r/gap` alone does not locate the ground
state. These are finite **projected** residuals, not full-operator residuals.
Candidate quadrature and prolate coefficients initially use double precision;
their errors must not be interpreted as exact residuals below that floor.

Checks: direct matrix entries against the parity recurrence; Fourier
evaluation against analytic basis integrals, including removable poles;
precision replay of the eigensystem; rank replay of root positions and
candidate metrics; prolate/quadrature refinement. Stop interpreting a
diagnostic as soon as those checks fail. If a decisive stable finite window
emerges, use Arb eigenpair isolation there. No larger Weil positivity scan,
Toeplitz/Jensen scan, forecasting, release, or existing manifest mutation.

Until a named, proved arithmetic inequality controls zeta and fails for DH,
the route remains a reformulation with an unproved convergence comparison.
