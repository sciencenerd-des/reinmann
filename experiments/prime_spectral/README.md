# One independent prime-defined program

This program implements the finite Weil quadratic-form matrix from
[Connes–Consani–Moscovici, *Zeta Spectral Triples*](https://arxiv.org/html/2511.22755v1),
equations 2.9–2.10 and 3.14–3.18. Inputs are an integer prime-power support cutoff,
a Fourier-mode cutoff and a quadrature budget. No zeta zeros are used as input,
fit targets, weights or basis data.

For `L=log(cutoff)` and `U_n(x)=L^(-1/2)exp(2 pi i n x/L)` on `[0,L]`, the code
computes the even correlations q exactly as elementary sine/cosine expressions.
The matrix is the pole term minus the archimedean and prime-power terms.
Every prime power up to `exp(L)` is included with its von Mangoldt weight.
The archimedean tail past L is included analytically as
`q(0)/2 log(tanh(L/2))`; dropping it changes the matrix.
The removable singularity at zero uses its analytic limit
`q(0)/4-1/L`, including off-diagonal entries.

```sh
python3 experiments/prime_spectral/weil_matrix.py --cutoff 13 --modes 8 --panels 1024 --output research/prime_spectral/weil_13_8.json
uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/prime_spectral -v
```

`research/prime_spectral/weil_sweep.json` records cutoffs 3, 5 and 13, each at
modes 2, 4 and 8, using 1024/2048 panels. Results are floating diagnostics.
The refinement difference is not an error bound. The output flags a smallest
eigenvalue below the observed refinement/residual scale as unresolved; even
values above that scale are not certified positive.

## Concrete next mathematical and numerical gates

1. Extend the interval eigenvalue/subspace bounds beyond the two configurations
   certified below, and establish omitted-mode error control. Finite
   configurations alone do not provide a uniform spectral separation.
2. Establish uniform simplicity, reflection parity and nonzero boundary
   normalization beyond the finite certificates, as needed to construct the paper's perturbed scaling operator.
3. Extend the finite quotient construction below to a controlled family and
   regularized determinant limit. The Weil form and its perturbed quotient
   operator are distinct; neither spectrum is identified here with zeta ordinates.
4. Make the fixed-support omitted-mode error effective and uniform along an
   increasing-support path. The [form-core audit](../../research/prime_spectral/FIXED_SUPPORT_FORM_CORE_2026_09_23.md)
   derives qualitative Ritz convergence from the established fixed-support
   core theorem, but no rate;
   it also proves that the boundary-evaluation norm grows at least as
   `sqrt(N/log N)` at fixed support in the logarithmic form norm.
   Boundary-zero Fourier vectors are consequently form dense, so their
   finite Rayleigh separation from the even ground Ritz value collapses
   as modes grow. Boundary evaluation is also unbounded in the Weil
   operator graph norm, ruling out a generic L2-to-boundary resolvent
   estimate. The [finite susceptibility audit](../../research/prime_spectral/BOUNDARY_SUSCEPTIBILITY_2026_09_23.md)
   certifies how the mode-4 and mode-8 boundary values relate to their
   boundary-constrained eigenvalue margins.
   Different support lengths need a common comparison target.
5. Prove local uniform convergence of the correctly normalized entire
   determinants to Xi, with a nonzero limiting normalization. Self-adjointness
   of finite matrices or agreement of a few eigenvalues cannot replace this.

This is a single independent arithmetic route, separate from the Xi coefficient
laboratory. The convergence theorem is open here. The source itself identifies
missing steps; we make no claim to have reproduced its spectral construction.

Replay the full recorded sweep from the repository root:

```sh
python3 - <<'PYTHON'
import json, sys
from pathlib import Path
sys.path.insert(0, 'experiments/prime_spectral')
from weil_matrix import run
out = Path('research/prime_spectral/weil_sweep.json')
out.parent.mkdir(parents=True, exist_ok=True)
rows = [run(c, n, 1024) for c in (3, 5, 13) for n in (2, 4, 8)]
out.write_text(json.dumps(rows, indent=2) + '\n')
PYTHON
```

## Certified finite gates

`certified_weil.py` now supplies interval integration, interval LDL inertia,
eigenvalue brackets and a boundary-kernel positivity test. The
[certificate note](../../research/prime_spectral/CERTIFIED_WEIL_GATES_2026_09_19.md)
proves the inference from these checks to finite positivity, simple even
lowest eigenvector and nonzero boundary evaluation. All three gates pass
at cutoff 13 for N=4 and N=8. The finite Weil eigenvalues remain distinct
from zeta ordinates. No omitted-mode or support-limit convergence is proved.

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/certified_weil.py --cutoff 13 --modes 8 --output research/prime_spectral/certified_weil_13_8.json
uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/prime_spectral -p 'test_*.py'
```

The original floating script still needs only the standard library; running
the entire test directory now also requires python-flint, as shown above.

## Certified comparison at fixed support

`certified_mode_comparison.py` encloses boundary-normalized eigenvectors
using a positive projected linear system. It compares nested mode spaces
only at the same support and bounds the difference of their origin-normalized
entire Fourier profiles on complex disks. The
[comparison note](../../research/prime_spectral/CERTIFIED_MODE_COMPARISON_2026_09_19.md)
records a unit-vector distance about 0.1376 for modes 4 versus 8 at cutoff 13.
This is a finite comparison, not a convergence estimate for omitted modes.

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/certified_mode_comparison.py --first research/prime_spectral/certified_weil_13_4.json --second research/prime_spectral/certified_weil_13_8.json --output research/prime_spectral/mode_comparison_13_4_8.json
```

The [strip residual transfer](../../research/prime_spectral/STRIP_RESIDUAL_TRANSFER_2026_09_23.md)
uses the finite Weil spectral gap and a candidate's Rayleigh residual to
bound its distance from the least eigenvector, then controls the
origin-normalized Fourier profiles on `|Im z|<=sigma`. The Fourier norm
is `sqrt(sinh(sigma*L)/(sigma*L))`, independent of the real part of `z`.
It now also records a form-level alternative using Rayleigh excess over
the lowest eigenvalue divided by the spectral gap, with no operator
residual. Both variants require a relative all-support estimate.
Local uniform convergence on the critical strip would suffice for RH;
an entire-plane variance bound is stronger than this route requires.
The saved cutoff-13 mode-4/mode-8 strip bound is finite only. The
prolate-candidate audit below encloses two finite residuals, but no
uniform residual-over-gap estimate has been established.

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/strip_transfer.py --comparison research/prime_spectral/mode_comparison_13_4_8.json --height 2/5 --output research/prime_spectral/strip_transfer_13_4_8.json
```

The [prolate candidate audit](../../research/prime_spectral/PROLATE_CANDIDATE_GATE_2026_09_23.md)
projects the paper's `k_lambda` into these same finite even Fourier spaces.
At cutoff 13, modes 4 and 8, the rounded numerical candidate has a
Rayleigh quotient certified above the second even eigenvalue by factors
greater than 50,093 and 85,199,037 respectively. The exact rational
calculation also encloses their squared residual norms. An infinite-Jacobi
tail certificate, closed-form Arb projection, and eigenfunction-error
transfer now place the **exact** prolate projection within the exclusion
radii at these two configurations. Its Rayleigh quotient also exceeds
the certified second even eigenvalue. These are finite exclusions;
their ordinary L2 projection error is small, but the finite residual
gate is far more demanding. A spectral
inverse filter suppresses high-energy leakage in these two finite
matrices: using their already certified ground vectors, the filtered
candidate is within `4.182e-6` and `1.398e-6` respectively. A uniform
Fourier-profile difference from the rounded prolate candidate is nevertheless
certified above `0.22829` and `0.10058` at real frequency 4. Thus the filter
does not preserve that profile in these finite examples. A uniform
ground-state overlap, gap ratio, and filtered-profile Xi limit remain
unproved.
`robust_prolate_gate.py` gives exact-rational exclusion radii around
the two normalized rounded vectors: approximately `3.79916e-5` at
mode 4 and `9.51734e-11` at mode 8. The
[exact-prolate certificates](../../research/prime_spectral/exact_prolate_gate_13_4.json)
bound the corresponding unit-vector distances by `5.35800e-16` and
`3.74586e-15`, respectively. They certify finite failure of the
Rayleigh-below-second-even gate; they do not rule out a different
mode/support path.
The [two-frequency profile constraint](../../research/prime_spectral/PROLATE_PROFILE_CONSTRAINT_2026_09_23.md)
shows more: at these same finite cutoffs, any even vector matching the
exact prolate profile sufficiently closely at real frequencies 4 and 8
also lies above the second even eigenvalue. The certified sample
tolerances are `1e-9` for modes 4 and `1e-22` for modes 8.
The [higher-mode exact-prolate check](../../research/prime_spectral/PROLATE_CANDIDATE_GATE_2026_09_23.md)
replays the isolated prime spectra at cutoff 13, modes 12 and 16, and
also certifies Rayleigh excess above their second even eigenvalues.
It uses closed-form prolate projection and the infinite-Jacobi
eigenfunction error, not a rounded candidate. This is still fixed-support
evidence, not a uniform spectral comparison.
The [direct residual-and-gap audit](../../research/prime_spectral/PROLATE_RESIDUAL_GAP_AUDIT_2026_09_26.md)
replays exact-prolate projection certificates and encloses the Weil
operator residual at cutoffs 17 and 19. Its three tested finite spaces
have Rayleigh values above the second even eigenvalue, so the strip
residual transfer has no positive clearance there.
The [physical cross-support overlap audit](../../research/prime_spectral/CROSS_SUPPORT_PHYSICAL_OVERLAP_2026_09_26.md)
embeds finite Fourier ground functions into one `L2(R)` space before
comparing cutoffs 17 and 19. It certifies their physical overlap and
a support-aware strip bound. Matching their Fourier origins before
bounding the difference more than halves that bound in all three
audited ranks. High coefficient overlap alone does not control the
change of Fourier interval.
The [moving-support boundary identity](../../research/prime_spectral/MOVING_SUPPORT_BOUNDARY_FLUX_2026_09_26.md)
shows that the physical `L2` path has square-root increments whenever
the endpoint value is nonzero. Its cross-Gram derivative has a
rank-one symmetric part driven by the same boundary vector as the
prime-power Weil eigenvalue kink. This rules out integrating a plain
physical `L2` derivative as the continuous support budget.

```sh
python3 experiments/prime_spectral/robust_prolate_gate.py --certificate research/prime_spectral/certified_weil_13_4.json --candidate research/prime_spectral/prolate_candidate_13_4.json --output research/prime_spectral/robust_prolate_gate_13_4.json
python3 experiments/prime_spectral/robust_prolate_gate.py --certificate research/prime_spectral/certified_weil_13_8.json --candidate research/prime_spectral/prolate_candidate_13_8.json --output research/prime_spectral/robust_prolate_gate_13_8.json
uv run --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/exact_prolate_finite_gate.py --certificate research/prime_spectral/certified_weil_13_4.json --candidate research/prime_spectral/prolate_candidate_13_4.json --jacobi research/prime_spectral/prolate_jacobi_13_80.json --vectors research/prime_spectral/prolate_vectors_13_80.json --output research/prime_spectral/exact_prolate_gate_13_4.json
uv run --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/exact_prolate_finite_gate.py --certificate research/prime_spectral/certified_weil_13_8.json --candidate research/prime_spectral/prolate_candidate_13_8.json --jacobi research/prime_spectral/prolate_jacobi_13_80.json --vectors research/prime_spectral/prolate_vectors_13_80.json --output research/prime_spectral/exact_prolate_gate_13_8.json
```
The [finite-Fourier diagonal theorem](../../research/prime_spectral/PROLATE_FOURIER_DIAGONAL_2026_09_23.md)
gives an explicit bounded-variation tail for the even projection and
shows that a sufficiently fast growing mode cutoff preserves the
prolate candidate's Xi profile limit. It does not transfer that limit
to the Weil ground state.
The [two-constraint audit](../../research/prime_spectral/PROLATE_TWO_CONSTRAINT_DEFECT_2026_09_23.md)
separates the candidate's zero-integral normalization from exact
vanishing at the origin, which the earlier near-radical argument also
requires. Their mismatch is an exact compressed-Fourier eigenvalue
defect. An established nonasymptotic PSWF estimate gives explicit
exponential bounds for its two eigenvalue deficits, evaluated with Arb
in `prolate_concentration_13.json`. The same note bounds the in-window
scale-invariant sum of that defect and obtains an asymptotic origin-value
ratio from the Hermite limit. The [leakage sampling derivation](../../research/prime_spectral/PROLATE_LEAKAGE_SAMPLING_2026_09_23.md)
uses endpoint and sine-series cancellation to bound the out-of-window
sampled sum by `O(cutoff^(9/2)*exp(-pi*cutoff/4))` along growing cutoffs.
This is an asymptotic bound without an effective finite-cutoff constant.
Transfer to the
prime-defined Weil residual and a uniform gap remain open.
The [Weil-form projection budget](../../research/prime_spectral/PROLATE_WEIL_FORM_PROJECTION_2026_09_23.md)
shows that `modes=ceil(cutoff^9)` makes the even candidate's
projection error vanish in a shifted Weil-form norm, while
`modes=ceil(cutoff^13)` also preserves its Rayleigh quotient
asymptotically. These exponents are analytic existence bounds, not
practical finite-cutoff mode recommendations. The gap-aware refinement
in that note gives a sufficient mode budget on the scale of
`cutoff^12/m_C^2` to preserve a hypothetical continuous Rayleigh
margin `m_C`, with the additional `D=1+log(e+N)/log C` factor and an
independent exponential remainder condition. Neither estimate supplies
that margin or compares
the candidate with the Weil ground state.
The [Jacobi tail gate](../../research/prime_spectral/PROLATE_JACOBI_TAIL_GATE_2026_09_23.md)
certifies the first four even prolate eigenvalues at cutoff 13 against
the infinite Legendre tail; their consecutive interval gaps exceed
`209.0`, `204.9`, and `200.7`. Saved Arb residual certificates bound
the exact unit eigenfunctions for the first and third even modes
within `8.388e-56` and `1.024e-51` of their decimal trial vectors.
The closed-form Arb projection and certified error transfer now enclose
the exact prolate candidate's finite Fourier coefficients at modes 4
and 8. No uniform prolate-to-Weil ground-state comparison follows.

## Finite quotient operator and real-zero profile

`quotient_operator.py` constructs the finite perturbation in a positive
quotient metric. The [exact proof](../../research/prime_spectral/QUOTIENT_OPERATOR_2026_09_19.md)
uses the rank-two displacement identity to establish metric self-adjointness
and an entire Fourier profile with only real zeros. At cutoff 13, modes 8,
the quotient dimension is 16. These zeros are not identified with Xi zeros.

The same proof establishes a necessary condition for a nonzero locally
uniform limit with increasing support: `modes/log(cutoff)` must tend to
infinity. Otherwise the forced exterior grid zeros become dense on a finite
interval. This is not a sufficient convergence theorem.

The [origin-constrained Schur identity](../../research/prime_spectral/ORIGIN_SCHUR_RESOLVENT_2026_09_24.md)
computes the finite ground profile from the positive principal Weil
block after deleting the zeroth Fourier coordinate. It also gives an
exact candidate-to-ground residual transfer without requiring the
candidate Rayleigh quotient below the second even eigenvalue. The
saved cutoff-13 mode-4 and mode-8 Schur profiles agree with the
existing construction and narrow every noncentral coordinate
enclosure by more than `2.57e6` and `6.87e8`, respectively. The
sequence-wide constrained inverse-residual estimate remains open.
The [coupled rank recurrence](../../research/prime_spectral/COUPLED_RANK_SCHUR_RECURRENCE_2026_09_24.md)
splits a fixed-support mode increment into an eigenvalue-shift source
and a new-mode coupling, then applies one common constrained inverse.
At cutoff 13, modes 4 to 8, the separate profile contributions at
real frequencies 4 and 8 exceed the coupled change in aggregate by
certified factors above 7317 and 9393. An all-rank estimate must
preserve this cancellation; one finite increment does not supply a
uniform cumulative budget. Block elimination also gives a two-sided
law bounding the effective new-mode coupling energy by the least-even
eigenvalue shift times explicit origin-vector norms. The mode-4 to
mode-8 certificate verifies that law, while profile convergence still
requires control of the coupled Fourier-resolvent pairing.
Dividing each coupling energy by the squared norm of the old
origin-normalized vector yields a cumulative bound by the telescoping
least-eigenvalue decrease at fixed support, without a uniform norm
assumption. For the **combined** rank residual, the normalized energy
equals that eigenvalue decrease exactly. This is an all-rank energy
budget, not profile convergence: a dual Fourier-resolvent bound is
still needed to convert it into a profile estimate. At the stored
mode-4 to mode-8 step, the certified Cauchy profile bound from exact
energy is more than 186 times the actual coupled change at each of
three tested arguments, so the signed pairing remains important.
The [Parseval origin-norm obstruction](../../research/prime_spectral/ORIGIN_NORM_TIGHTNESS_OBSTRUCTION_2026_09_24.md)
corrects its support scaling: if the Fourier profiles converge locally
to a nonzero normalized limit while `L=log(cutoff)` grows, the squared
norm of the origin-normalized ground vector must grow at least linearly
in `L`. Positive spatial kernels give additional explicit lower bounds.
A support-independent norm bound cannot supply the all-rank budget on
the intended Xi convergence path.

The [grid-tail refinement](../../research/prime_spectral/GRID_TAIL_SCALING_2026_09_20.md)
proves the stronger necessary condition `modes/(log(cutoff))^2 -> infinity`
for convergence of the unmodified Fourier profiles to normalized Xi.
It factors each profile exactly into the normalized quotient characteristic
polynomial and an explicit exterior-grid product. `grid_tail.py` evaluates
the polynomial directly from the prime-defined quotient and bounds the
grid factor on any complex disk. At critical modes proportional to L^2,
the grid factor converges to a nontrivial Gaussian; it tends to one when
L^2/modes tends to zero. This separates an artificial grid contribution
from the actual quotient convergence problem, which remains open.

The [coefficient budget](../../research/prime_spectral/QUOTIENT_COEFFICIENT_BUDGET_2026_09_20.md)
proves `|R(z)|<=exp(S*|z|^2)` with `S=trace(B^(-2))/2` and gives a
factorial Taylor-tail bound. A uniform S bound would provide compactness;
convergence of every Taylor coefficient would identify the entire limit.
`quotient_coefficient_budget.py` computes prime-only coefficient intervals
from inverse matrix traces. At cutoff 13, modes 4 versus 8, the normalized
quotient polynomials differ by less than 0.003320983 on the unit disk.
This is a finite comparison, with no omitted-mode or increasing-support
convergence claim. The saved artifact is `coefficient_budget_13_4_8.json`.

The [Euler-region uniqueness gate](../../research/prime_spectral/PRIME_EULER_REGION_UNIQUENESS_2026_09_23.md)
gives a different sufficient route: bound the quotient at one positive
imaginary argument, then match its resolvent trace to the completed
finite prime-power expression on an interval where the Euler product
converges absolutely. The arithmetic trace convergence remains open.
`euler_region_trace.py` evaluates a shared-denominator rank-one secular
formula, avoiding the unstable dense interval inverse at mode 8. It
certifies finite mismatches at height 2 for modes 4, 8, 12 and 16 at
cutoff 13, and mode 16 at cutoffs 17 and 23. The saved outputs also
enclose the one-point compactness quantity `R(i)`. These six points
do not establish an asymptotic path. For certified positive spatial
kernels, the note also rewrites bounded `R(i)` as a weighted exponential
tail condition; the available variance bounds do not imply it.
The same note gives an effective interval-mesh criterion: a uniform
`R(i)` bound controls the quotient trace derivative, and an explicit
prime-power sum controls the finite target derivative. The two saved
16-segment budgets, `euler_mesh_13_16_m16.json` and
`euler_mesh_23_16_m16.json`, bound the whole-interval errors by
0.678528 and 0.563670 respectively. Their largest sampled errors occur
at height 1. These finite budgets expose the unresolved arithmetic
matching problem; they do not imply decay as cutoff and rank grow.
At 64 segments, `euler_mesh_13_16_m64.json` and
`euler_mesh_23_16_m64.json` additionally certify that the quotient
trace is below the *finite prime-power target* at every height in
`[1,2]`, by at least 0.011633128 and 0.006241783 respectively.
Their integrated absolute errors have positive lower bounds 0.118471527
and 0.082082877. The omitted-prime tail prevents this signed statement
from being transferred to the completed Xi trace over the entire interval.

The [direct eigenvector formula](../../research/prime_spectral/EIGENVECTOR_COEFFICIENTS_2026_09_20.md)
computes the same coefficients with a shared denominator, avoiding repeated
interval matrix inversions. For the stored mode-8 input, the spectral-sum
enclosure is more than ten orders of magnitude narrower. The unit-disk
comparison improves to below 0.003275386. The formula identifies the missing
uniform condition as `sum((1+2*c_n/c_0)/n^2)=O(L^(-2))`; that signed
eigenvector cancellation has not been proved along an infinite sequence.
The implementation and artifact are `eigenvector_coefficients.py` and
`eigenvector_coefficients_13_4_8.json`.

The [positive-kernel gate](../../research/prime_spectral/POSITIVE_KERNEL_2026_09_22.md)
certifies positivity of the actual spatial Fourier kernels on the entire
support at cutoff 13, modes 4 and 8, using Bernstein coefficients with
the boundary value enforced exactly. They normalize to even probability
densities, with variances near 0.0902350 and 0.0621260. Independent
integration verifies the moment and transform identities. Under the
real-zero gates, a uniform variance bound would provide entire-function
bounds; weak convergence to the Xi theta measure would then imply the
required local uniform convergence. Those sequence-wide facts remain open.
Artifacts: `positive_kernel_13_4.json` and `positive_kernel_13_8.json`.
The [semigroup sign obstruction](../../research/prime_spectral/SEMIGROUP_SIGN_OBSTRUCTION_2026_09_23.md)
shows that at log-support radius greater than `1/2`, the full Weil heat
semigroup cannot preserve pointwise positivity. Spatial positivity of
these particular kernels therefore supplies no semigroup positivity theorem.

The [isolated-eigenpair gate](../../research/prime_spectral/ISOLATED_KERNEL_2026_09_22.md)
extends the cutoff-13 certificates to modes 12 and 16. The previous
LDL-based path is unresolved there; FLINT's certified Rump eigenpair
algorithm isolates the same interval matrices and verifies the boundary
normalization directly. Both kernels pass whole-support Bernstein
positivity, with variances near 0.0530682 and 0.0489750. Existing artifacts
are preserved. Run `isolated_kernel.py --modes 16 --output PATH` for the
new gate; neither the finite trend nor these certificates prove convergence.

An [increasing-support audit](../../research/prime_spectral/SUPPORT_VARIANCE_AUDIT_2026_09_22.md)
also certifies cutoffs 17 and 23 at mode 16. Their variances increase to
approximately 0.0532823 and 0.0585733; cutoff 31 has unresolved even-block
eigenpair isolation. A separate, post-construction comparison with the
certified Xi variance gives rigorous finite distribution-distance lower
bounds. Xi data do not enter the prime construction. This audit prevents
confusing a fixed-support mode trend with an increasing-support theorem.

The [matrix perturbation certificate](../../research/prime_spectral/PERTURBATION_KERNEL_2026_09_23.md)
resolves the former cutoff-31, mode-16 isolation failure. It certifies a
midpoint eigensystem and transfers its eigenvalues and eigenvector to the
original interval matrix using a row-sum error bound and a separated
spectral gap. The boundary-anchored Bernstein calculation keeps the tiny
normalizing boundary value as one shared denominator. The resulting
kernel is positive on its full support, with variance near 0.0646575.
This extends finite evidence; uniform variance control and convergence
remain open.

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/quotient_operator.py --certificate research/prime_spectral/certified_weil_13_8.json --output research/prime_spectral/quotient_13_8.json
```
