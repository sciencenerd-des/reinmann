# A prolate candidate in the finite Weil Fourier space

The [strip residual transfer](STRIP_RESIDUAL_TRANSFER_2026_09_23.md)
requires a candidate vector in **the same even Fourier space** as the
prime-defined Weil matrix. We constructed the candidate proposed in
[Connes–Consani–Moscovici, §7](https://arxiv.org/html/2511.22755v1),
then measured its finite Rayleigh gate at support cutoff 13.

## Normalization and projection

Put `C=13`, `lambda=sqrt(C)`, and `L=log(C)`. The paper's support
`[lambda^-1,lambda]` becomes `[-L/2,L/2]` in `t=log(u)`, exactly the
centered interval used by our Fourier profile. On `z=x/lambda`, the
prolate operator is

```
-d/dz[(1-z^2)d/dz] + (2*pi*C)^2*z^2.
```

In the orthonormal even Legendre basis
`phi_l(z)=sqrt((2l+1)/2)*P_l(z)`, `l=0,2,4,...`, its derivative part is
diagonal with entries `l(l+1)`. Multiplication by `z` couples adjacent
degrees with `a_l=l/sqrt((2l-1)(2l+1))`; hence `z^2` has diagonal
`a_l^2+a_(l+1)^2` and off-diagonal `a_(l+1)*a_(l+2)` between `l` and
`l+2`. The first and third even eigenvectors represent `h_(0,lambda)`
and `h_(4,lambda)`. Their unique combination with zero integral is
`h_4-(h_4)_0/(h_0)_0*h_0`, because every Legendre basis function except
`phi_0` integrates to zero.

Extend this `h_lambda` by zero beyond `[-lambda,lambda]`, set
`k_lambda(u)=sqrt(u)*sum_(n>=1) h_lambda(nu)`, and split quadrature at
each `u=lambda/n`. The orthonormal even Fourier coefficients are

```
w_0 = L^-1/2 * integral_(-L/2)^(L/2) k_lambda(exp(t)) dt,
w_j = sqrt(2/L) * integral_(-L/2)^(L/2)
                  k_lambda(exp(t)) cos(2*pi*j*(t+L/2)/L) dt.
```

The vector is normalized in Euclidean norm and oriented with positive
central coordinate. No Xi coefficient or zero enters this construction.

## Finite outcome

The floating projection uses 80 even Legendre functions and 100
Gauss–Legendre nodes per piece. Repeating with `(48,64)` and `(120,160)`
changes any normalized coordinate by at most `2.14e-15`; an independent
ODE integration of the first and third even eigenfunctions agrees to
`2.07e-11` on `0<=z<=0.4`. The inversion-reflection defect is about
`1.53e-15`. These are **floating diagnostics**, not interval enclosures
of the exact prolate functions.

For each rounded candidate coefficient vector, however, we evaluate its
Rayleigh quotient and squared residual norm against the stored interval
Weil matrix using exact rational interval arithmetic. Even-block factors
of `sqrt(2)` use a 60-decimal rational enclosure. The comparison with the
certified second even eigenvalue is therefore rigorous for that explicit
rounded vector:

| Modes | Projected L2 fraction, floating | Rayleigh quotient, approximate | Residual norm, approximate | Second even eigenvalue, approximate | Certified lower Rayleigh ratio |
|---:|---:|---:|---:|---:|---:|
| 4 | 0.99990715 | `4.3326e-5` | `0.00430194` | `8.6492e-10` | `>50093` |
| 8 | 0.999999999666 | `8.1993e-10` | `0.0000237613` | `9.6237e-18` | `>85199037` |

Thus neither rounded candidate satisfies the necessary gate
`Rayleigh < second eigenvalue`. The residual norm is enclosed through
`||(B-mu I)w||^2/||w||^2`, with `mu=w^T B w/||w||^2` and interval even
block `B`; the table displays square roots of those enclosures only as
readable approximations. Since the Rayleigh clearance is negative in both
cases, the residual-over-clearance bound from the strip theorem is
inapplicable, regardless of the residual size. At the same support cutoff, post-hoc
floating comparisons with the certified lowest eigenvectors give
ordinary Euclidean distances of approximately `0.2576`, `0.1232`,
`0.0688`, and `0.0418` at modes `4`, `8`, `12`, and `16` respectively.
The last two use the saved boundary-normalized positive-half
coefficients, converted to the orthonormal even basis by multiplying
noncentral coefficients by `sqrt(2)`. These are finite trends, not
convergence bounds. At the two matrix cutoffs the candidate looks
closer in ordinary norm while its Rayleigh-to-gap ratio worsens
dramatically. A nearly complete unweighted Fourier projection is
therefore **not** enough to control this spectral gate.

The rounded-vector comparison alone does not establish the same inequality
for the **exact** prolate projection. The separate Jacobi, analytic
projection, and error-transfer certificates below now establish it at these
two finite configurations. Neither configuration establishes behavior as
mode or support grows.

The [robust exclusion certificate](robust_prolate_gate_13_4.json)
now quantifies the missing exact-prolate enclosure. For a unit even
coefficient vector `v` and the normalized recorded rounded vector `w`,
the Rayleigh quotient changes by at most `2*||A_even||*||v-w||_2`.
Exact rational row sums of the saved interval matrices therefore show
that every `v` within the following **strict** Euclidean radius still
has Rayleigh quotient above the certified second even eigenvalue:

| Modes | Certified strict radius, approximate | Exact certificate |
|---:|---:|---|
| 4 | `3.79916e-5` | [JSON](robust_prolate_gate_13_4.json) |
| 8 | `9.51734e-11` | [JSON](robust_prolate_gate_13_8.json) |

The generator is `experiments/prime_spectral/robust_prolate_gate.py`.
The floating refinement and ODE comparisons by themselves do not place
the exact projection inside either radius.
The [Jacobi tail gate](PROLATE_JACOBI_TAIL_GATE_2026_09_23.md)
proves a Schur-complement bound for the omitted Legendre modes and
an eigenfunction residual-to-distance inequality. Its cutoff-13
Arb certificate isolates the first four full even prolate eigenvalues,
including the first and third modes used here. The saved trial-vector
certificate now bounds their exact unit eigenfunction errors by
`8.388e-56` and `1.024e-51`, respectively. The
[analytic projection](prolate_projection_trial_13_4.json) expands the
Legendre trials with rational polynomial coefficients and evaluates each
logarithmic Fourier integral by a closed formula in 1024-bit Arb balls.
The [exact-prolate transfer](exact_prolate_gate_13_4.json) propagates the
eigenfunction errors through the zero-integral ratio, the finite-window
map, Fourier projection, and unit normalization. For an `L2[-1,1]`
input error `e`, its map bound uses
`||sqrt(u)e(nu/sqrt(C))||_(L2(du/u)) <= C^(1/4)*n^(-1/2)*e`;
the factor `sqrt(u)` cancels the logarithmic Jacobian. Summing
`n^(-1/2)` for `1<=n<C` is bounded by `2sqrt(C)-1`.

| Modes | Exact-to-rounded unit distance upper | Strict exclusion radius | Exact Rayleigh excess over second even, lower |
|---:|---:|---:|---:|
| 4 | `5.35800e-16` | `3.79916e-5` | `4.33254e-5` |
| 8 | `3.74586e-15` | `9.51735e-11` | `8.19896e-10` |

The exact rational lower excess is the rounded Rayleigh margin minus
`2*||A_even||` times the certified unit-vector distance. Thus the
**exact normalized prolate combination** fails the necessary
`Rayleigh < second even eigenvalue` gate at cutoff 13, modes 4 and 8.
The [mode-8 certificate](exact_prolate_gate_13_8.json) and its
analytic [projection](prolate_projection_trial_13_8.json) can be
replayed independently from their saved inputs. This is a finite
exclusion only; it does not rule out a different mode count or a
growing-support comparison.

The same exact-prolate transfer has now been replayed at two larger
Fourier dimensions using the previously isolated higher-mode prime
spectra. The generator recomputes the interval Weil matrix and its
Rump-isolated even and odd spectra, evaluates the closed-form prolate
projection, and subtracts `2*||A_even||` times the certified exact-to-trial
unit-vector error from the trial Rayleigh margin. It does not rely on
a rounded candidate or on an `L2` convergence extrapolation.

| Cutoff, modes | Trial Rayleigh, approximate | Second even eigenvalue, approximate | Certified exact-prolate Rayleigh excess lower | Certificate |
|---:|---:|---:|---:|---|
| `13,12` | `3.55210e-15` | `4.68190e-24` | `3.55210e-15` | [JSON](exact_prolate_gate_13_12.json) |
| `13,16` | `2.44796e-20` | `4.34408e-29` | `2.44796e-20` | [JSON](exact_prolate_gate_13_16.json) |

Thus the exact prolate candidate fails the necessary finite Rayleigh
gate at modes 4, 8, 12, and 16 for this one support cutoff. Its
decreasing absolute Rayleigh quotient does not by itself help: at
modes 12 and 16 it remains hundreds of millions of times larger than
the second-even threshold.
Four points at fixed support cannot establish an all-mode or
growing-support obstruction.

## A filtered finite diagnostic

Although the rounded candidate fails the raw residual gate, a
spectral-filter estimate can produce a vector near the finite ground
state when an overlap with that state is known.
For a positive selfadjoint matrix with lowest eigenpair `(lambda_0,v)`
and second eigenvalue at least `lambda_1`, write a unit candidate as
`w=alpha*v+u`, `u` perpendicular to `v`, `alpha>0`. With
`T_tau=(A+tau*I)^-1`, `tau>=0`, the normalized filtered vector obeys

```
tan angle(T_tau*w,v)
    <= ((lambda_0+tau)/(lambda_1+tau)) * ||u||/alpha.
```

This follows by applying the spectral theorem to `u`; every eigenvalue
on that subspace is at least `lambda_1`. It is an exact finite-dimensional
lemma. Applying it with `tau=0` and the **certified finite ground
eigenvector** gives the following bounds, valid for the exact inverse
filter of the recorded rounded vector by the exact finite Weil matrix:

| Modes | Certified filtered unit distance to ground | Profile difference on `|Im z|<=2/5` |
|---:|---:|---:|
| 4 | `<4.182e-6` | `<1.786e-5` |
| 8 | `<1.398e-6` | `<6.951e-6` |

The profile bounds combine the filter distance with the
Fourier-origin strip transfer. They compare the **filtered and ground**
profiles, not the filtered and prolate profiles. A reverse-triangle
calculation with Arb evaluations of the same centered Fourier functional
gives the following certified lower bounds for the latter difference:

| Modes | At real frequency 4 | At real frequency 8 |
|---:|---:|---:|
| 4 | `>0.22829068` | `>0.19190545` |
| 8 | `>0.10058924` | `>0.10819901` |

For example, write `P_w`, `P_f`, and `P_v` for the origin-normalized
profiles of the rounded prolate, filtered, and ground vectors. At any real
`x`, `|P_w(x)-P_f(x)| >= |P_w(x)-P_v(x)|-|P_f(x)-P_v(x)|`.
The final term is bounded on the entire strip by the preceding table;
the first is interval-evaluated at `x=4,8`. This is a rigorous statement
about the rounded finite vectors, not about exact prolate functions or an
unbounded family.

The finite success uses an overlap
computed against the already certified ground vector; it is not an
independent construction of the unknown infinite eigenvector. For an
RH argument, one would need a uniform overlap lower bound obtained
without knowing that vector, an effective gap ratio, control of filtering
across the finite-to-continuous limit, and convergence of the **filtered**
Fourier profile to Xi. None is provided by the finite certificate.
The [two-frequency constraint certificate](PROLATE_PROFILE_CONSTRAINT_2026_09_23.md)
strengthens this finite warning: at cutoff 13, any even vector retaining
the exact prolate profile at frequencies 4 and 8 within the certified
small tolerances still has Rayleigh quotient above the second even
eigenvalue. Thus a finite Rayleigh repair must distort at least one
of those profile values.

An exact two-dimensional control shows why a gap and overlap alone cannot
provide the last requirement. Let `A_epsilon=diag(epsilon,1)` and
`w=(1,1)/sqrt(2)` for `0<epsilon<1`. Its ground-state overlap is always
`1/sqrt(2)` and its gap ratio tends to zero, yet the normalized inverse
filter is `(1,epsilon)/sqrt(1+epsilon^2)`. For the origin-normalized
linear profile `P_(a,b)(z)=1+(b/a)z`, filtering changes `1+z` into
`1+epsilon*z`. At `z=1`, the profile difference tends to one. This
abstract example does not model the exact Weil matrix, but proves that
the filter inequality alone cannot transmit a candidate profile limit.

The missing analytic gate can be stated directly: along a growing family,
prove that the prolate and filtered origin-normalized profiles approach
each other locally uniformly on `|Im z|<1/2`, or prove that the prolate
candidate approaches the Weil ground vector strongly enough for the
strip functional. The first option must accompany a finite-to-continuous
Weil comparison. Neither follows from the finite numbers above.
The [finite-Fourier diagonal estimate](PROLATE_FOURIER_DIAGONAL_2026_09_23.md)
does show that some growing mode cutoff makes the **candidate's own**
even Fourier profiles converge to Xi; it supplies no Weil ground-state
comparison.
The [two-constraint defect identity](PROLATE_TWO_CONSTRAINT_DEFECT_2026_09_23.md)
shows exactly why the zero-integral prolate combination used here need
not vanish at the origin: its defect is proportional to the difference
between the first and third even compressed-Fourier eigenvalues.
The [leakage sampling estimate](PROLATE_LEAKAGE_SAMPLING_2026_09_23.md)
also bounds the out-of-window Fourier samples asymptotically, closing
the candidate's inversion-defect calculation. It does not establish
a uniform Weil Rayleigh excess, residual, or gap.
The [Weil-form projection budget](PROLATE_WEIL_FORM_PROJECTION_2026_09_23.md)
then shows that a polynomially growing even Fourier projection can
preserve the continuous candidate's Weil Rayleigh quotient. It does
not show that this quotient approaches the lowest Weil eigenvalue.

There is a cancellation-preserving form of the first gate. Let `F_z` be
the unnormalized centered Fourier functional, `P_x(z)=F_z(x)/F_0(x)`,
and let `A e_j=lambda_j e_j` be an orthonormal eigenbasis of a positive
finite matrix. Write `w=sum_j a_j e_j`, `s_j=1/lambda_j`,
`q_j(z)=F_z(e_j)`, and `b_j=F_0(e_j)`. Whenever both origin values are
nonzero, exact algebra gives

```
P_(A^-1 w)(z)-P_w(z)
  = [sum_(j<k) a_j a_k (s_j-s_k)
                     (q_j(z)*b_k-q_k(z)*b_j)]
    / [F_0(A^-1 w)*F_0(w)].
```

The factor `q_j*b_k-q_k*b_j` vanishes when two eigenmodes have the same
origin-normalized profile, even if the filter changes their amplitudes.
This suggests a sharper analytic target than norm convergence: bound the
displayed pairwise sum uniformly on closed substrips as support and mode
grow. No such bound has been established for the prime-defined Weil
operator; the finite profile-separation certificates show it is not small
at the two configurations tested here.

Replay:

```sh
python3 experiments/prime_spectral/prolate_candidate_diagnostic.py --certificate research/prime_spectral/certified_weil_13_4.json --output research/prime_spectral/prolate_candidate_13_4.json
python3 experiments/prime_spectral/prolate_candidate_diagnostic.py --certificate research/prime_spectral/certified_weil_13_8.json --output research/prime_spectral/prolate_candidate_13_8.json
uv run --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/filtered_candidate_transfer.py --certificate research/prime_spectral/certified_weil_13_4.json --candidate research/prime_spectral/prolate_candidate_13_4.json --output research/prime_spectral/filtered_candidate_13_4.json
uv run --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/filtered_candidate_transfer.py --certificate research/prime_spectral/certified_weil_13_8.json --candidate research/prime_spectral/prolate_candidate_13_8.json --output research/prime_spectral/filtered_candidate_13_8.json
uv run --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/higher_mode_prolate_gate.py --isolated research/prime_spectral/isolated_kernel_13_12.json --jacobi research/prime_spectral/prolate_jacobi_13_80.json --vectors research/prime_spectral/prolate_vectors_13_80.json --output research/prime_spectral/exact_prolate_gate_13_12.json
uv run --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/higher_mode_prolate_gate.py --isolated research/prime_spectral/isolated_kernel_13_16.json --jacobi research/prime_spectral/prolate_jacobi_13_80.json --vectors research/prime_spectral/prolate_vectors_13_80.json --output research/prime_spectral/exact_prolate_gate_13_16.json
uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/prime_spectral -p 'test_*.py' -q
```

For the modes-12 and modes-16 distance diagnostics, the following
uses only the saved prime eigenvector enclosures as post-hoc targets:

```sh
python3 - <<'PY'
import json, math, sys
from fractions import Fraction
sys.path.insert(0, 'experiments/prime_spectral')
from prolate_candidate_diagnostic import project_candidate
mid = lambda x: float((Fraction(x['lo']) + Fraction(x['hi'])) / 2)
for modes in (12, 16):
    w = project_candidate(13, modes, 80, 100)['unit_coefficients']
    data = json.load(open(f'research/prime_spectral/isolated_kernel_13_{modes}.json'))
    half = data['boundary_normalized_positive_half']
    v = [mid(half[0])] + [math.sqrt(2) * mid(x) for x in half[1:]]
    norm = math.sqrt(sum(x*x for x in v))
    v = [x / norm for x in v]
    print(modes, min(math.dist(w, v), math.dist(w, [-x for x in v])))
PY
```

The floating projection requires NumPy and SciPy. The exact rounded-vector
gate uses only Python's rational arithmetic and the existing certified
Weil matrix. The paper itself identifies candidate-versus-eigenvector
approximation as a missing step; this finite audit does not prove RH.
