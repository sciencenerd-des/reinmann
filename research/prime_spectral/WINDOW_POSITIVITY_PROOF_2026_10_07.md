# Full Weil positivity through C = exp(6/5)

Date: 7 October 2026. Status: written computer-assisted proof with an Arb
certificate and a separate verifier; not Lean formalization or external
peer review. This is an independent reproduction within ranges already
claimed in recent preprints, **not a record or a novelty claim**. See the
[dedicated prior-art check](WINDOW_POSITIVITY_PRIOR_ART_2026_10_07.md).

## Statement and conventions

Let `F(t) = integral f(x) exp(itx) dx` and
`g(y) = integral conjugate(f(x-y)) f(x) dx`. The full Weil form is

\[
 Q(f)=2\operatorname{Re}\left(F(i/2)\overline{F(-i/2)}\right)
 +\frac1{2\pi}\int_{\mathbb R}|F(t)|^2
 [\operatorname{Re}\psi(1/4+it/2)-\log\pi]dt
 -2\sum_{q=p^k}\frac{\log p}{\sqrt q}\operatorname{Re}g(\log q).
\]

**Theorem.** Every complex smooth test function supported in `[-3/5,3/5]`
satisfies

\[
                     Q(f)\ge 9\cdot10^{-13}\|f\|_2^2.
\]

The same inequality holds on its closed Weil form domain. We do not assert
that the unbounded form has a finite value on every L2 function. Equivalently,
this proves positivity on every multiplicative window
`[C^(-1/2),C^(1/2)]` with `1<C<=exp(6/5)=3.320116922736...` after the unitary
logarithmic coordinate change. No pole-neutrality constraint is imposed.
For smaller centered windows the functions are a subset of the stated class.
The underlying form is the same: extra prime shifts have zero correlation.
There is consequently no need to sample intermediate values of C.

The active prime powers at the largest window are exactly 2 and 3, because
`log(3)<6/5<log(4)`. Both have their full von Mangoldt weights. The pole
contribution is retained, including its **negative odd-sector term**.

## 1. An operator lower bound with a finite frequency band

Put `a=3/5`, `T=64`, and define

\[
 A=2\log(2)/\sqrt2+2\log(3)/\sqrt3,\qquad
 \beta=\log(T/(2\pi))-1/T-A>0.
\]

For real t the symbol is
`Psi(t)=Re psi(1/4+it/2)-log(pi)-sum_q 2 log(p)/sqrt(q) cos(t log(q))`.
For `t>=15/4`,

\[
 \operatorname{Re}\psi(1/4+it/2)-\log\pi
 \ge\log(t/(2\pi))-1/t.
\]

Here is a direct justification. Shift the argument to `z=5/4+it/2` and
use Binet's digamma integral. Its integral remainder has modulus at most
`1/(15t)`, since `|u^2+z^2|>=5t/4` and
`integral_0^infinity u/(exp(2pi u)-1)du=1/24`. The real parts of `1/(2z)`
and the shift correction `1/(1/4+it/2)` cost at most `5/(2t^2)` and
`1/t^2`. Their total with `1/(15t)` is at most `1/t` for `t>=15/4`.
Also `Re log(z)>=log(t/2)`. This is the classical envelope used in the
recent literature; no improved prime-comb constant is assumed.

Every cosine is at most one, so `Psi(t)>=beta` for `|t|>=T`.
Parseval therefore gives `Q>=R` on the original test space, where the
bounded form R is

\[
 R(f)=\beta\|f\|_2^2+\text{pole}(f)
       +\frac1{2\pi}\int_{-T}^{T}(\Psi(t)-\beta)|F(t)|^2dt.
\]

Real and imaginary parts decouple. Reflection parity also decouples.
On real even functions the pole is `+2|<f,cosh(x/2)>|^2`; on real odd
functions it is `-2|<f,sinh(x/2)>|^2`. These two signs are implemented
explicitly. It suffices to bound both real parity sectors.

## 2. Rigorous finite block, including quadrature error

Use the orthonormal functions
`h_n(x)=sqrt((2n+1)/(2a)) P_n(x/a)` for `0<=n<N=160`.
Their Fourier transforms are

\[
 \widehat h_n(t)=\sqrt{2a(2n+1)}\,i^n j_n(at),\qquad
 j_n(z)=\frac{z^n}{(2n+1)!!}\,{}_0F_1(n+3/2;-z^2/4).
\]

These formulas have no removable singularity in the implementation.
The cosh (even n) and sinh (odd n) coefficients are
`sqrt(2a(2n+1)) (a/2)^n/(2n+1)!! 0F1(n+3/2;(a/2)^2/4)`.
Thus each parity matrix has dimension 80, with entries

\[
 R_{nm}=\beta\delta_{nm}+2(-1)^n p_np_m
  +\frac{(-1)^{(n-m)/2}}\pi\int_0^T
      (\Psi(t)-\beta)b_n(t)b_m(t)dt,
\]

where `b_n=F_n/i^n` and n,m have the same parity.

The integral is computed on 64 unit panels, using 80-point Gauss-Legendre
quadrature on each. All nodes, weights, special functions and matrix
operations are evaluated in FLINT/Arb at 384 bits. To bound the quadrature
error as an **operator** error, extend the symbol analytically by replacing
the real digamma part with
`[psi(1/4+it/2)+psi(1/4-it/2)]/2`.
On the Bernstein ellipse with parameter rho=2 around a unit panel,
`|Im(t)|<=3/8`, `|Re(t)|<=T+1`, and both digamma arguments have real part
at least `1/16`. The Euler series

\[
 \psi(z)=-\gamma-1/z+\sum_{k\ge1}\frac{z}{k(k+z)}
\]

gives `|psi(z)|<=17+2 zmax`, where `zmax=1+(T+2)/2`; indeed
`|k+z|>=k`, `|z|<=zmax`, `gamma<1` and `sum 1/k^2<2`.
Each prime cosine has modulus at most `cosh((3/8)log(q))`.
It follows that `|Psi-beta|<=H`, with the explicit H computed by the script.
For the default run `H<88.682`.

The compressed Fourier kernel has operator norm at most
`2a exp(2a |Im(t)|)`, by Cauchy-Schwarz applied to `exp(itx)` and
`exp(-itx)`. This bound also holds for each parity compression and is
independent of N. Set `M=2a exp(3a/4) H`.

For a Banach-valued analytic kernel bounded by M on this ellipse, its
degree `2k-1` Chebyshev approximation has uniform error at most
`2M rho^(1-2k)/(rho-1)`. Gauss quadrature is exact on this polynomial;
its positive weights and the integral each have norm equal to the panel
length. The total operator error on all panels is consequently at most

\[
 E_Q=\frac{4TM}{\pi}\,2^{1-2k},\qquad k=80.
\]

This argument applies to the analytic parity kernel, not to a
non-holomorphic absolute-value formula. The computed matrix balls contain
all node and arithmetic errors; `E_Q` is an additional allowance for the
analytic quadrature remainder. The certificate verifies interval LDL
positivity of each quadrature matrix shifted by `(10^-12+E_Q) I`.
Every pivot is strictly positive. Hence each exact finite block exceeds
`10^-12 I`. This is a block certificate, not a list of small minors.

## 3. Every omitted polynomial mode and the coupling

Let P project onto degrees below N and S=I-P. If `f` is in S, all its
moments through degree N-1 vanish. Taylor's integral remainder on the real
axis gives, for `|t|<=T`,

\[
 |F_f(t)|\le r\|f\|_2,\qquad
 r=\sqrt{2a}\,(aT)^N/N!.
\]

No sum over omitted modes is truncated: this is a bound on their entire
orthogonal complement. For a unit vector in P the corresponding bound
is `sqrt(2a)`. The band-integral tail and cross-block norms are thus at most
`TH r^2/pi` and `TH sqrt(2a) r/pi` respectively.

The pole functions each have norm at most `p=sqrt(2a) exp(a/2)`.
Subtracting their Taylor polynomials below degree N bounds each omitted
pole vector by `rp=p (a/2)^N/N!`. Retaining both rank-one pole terms and
using their absolute operator norms gives

\[
 D=THr^2/\pi+4r_p^2,\qquad
 B=TH\sqrt{2a}\,r/\pi+4pr_p.
\]

Therefore `SRS >= (beta-D) S` and `||PRS||<=B`.
For `f=u+v`, the inequality `2||u||||v||<=||u||^2+||v||^2` yields

\[
 R(f)\ge\left(\min(10^{-12},\beta-D)-B\right)\|f\|_2^2.
\]

The saved Arb certificate encloses

| Quantity | Safe outward bound |
|---|---:|
| beta | >0.05655 |
| quadrature operator error E_Q | <1.862e-44 |
| cross-block allowance B | <1.431e-28 |
| tail-block deviation D | <9.444e-60 |

The displayed weaker conclusion `Q>=9e-13 ||f||^2` follows immediately.
This completes the infinite-dimensional argument. All constants are
computed without zeta zeros, RH, fitted eigenvalues, or a support limit.

## 4. Replay and scope of independent checks

From the repository root:

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/compact_window_certificate.py --output research/prime_spectral/window_positivity_exp_1p2.json
uv run --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/verify_window_positivity.py research/prime_spectral/window_positivity_exp_1p2.json --output research/prime_spectral/window_positivity_exp_1p2_verification.json
uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/prime_spectral -p 'test_window_positivity.py' -v
```

The certificate contains both full interval matrices, all shifted LDL
pivots, the analytic constants, and source hashes. The separate verifier
recomputes the constants and both LDL tests. It also adaptively integrates
four low matrix entries with complex-ball quadrature, independently of
the Gauss assembly, and checks the constant-function normalization against
the existing geometric-side explicit formula.

Executed verification: both shifted LDL blocks passed; all four adaptive
integral comparisons and the geometric constant check passed; **8 focused
tests passed**, including rejection of deleted prime/parity data, zeroed
complement allowance, and an exaggerated finite lower bound. Python
compilation and whitespace checks passed. No Lean build was run for this
Python/written-proof change. The numerical certificate generation took
21.332 seconds on this machine; this is an observed local runtime, not a
performance claim across methods or hardware.

These entry checks do not independently regenerate all 12,800 entries.
Both numerical paths share FLINT/Arb. The analytic argument above is
written mathematics, not a Lean theorem. The result establishes the
requested prime-containing window but neither RH nor a new literature
record. No inference is made from the old rank-eight support-17--19 tail
certificate to positivity of that much larger full window.

## 5. Lean interface and a smaller Schur certificate

The follow-up [WeilWindowHypotheses.lean](../../Reinmann/WeilWindowHypotheses.lean)
records `CertifiedExpSixFifthsHypothesis` as an explicit input about Q and
its admissible test class. `WindowBlockHypotheses` separates source
domination, energy splitting, form assembly, finite compression, the whole
infinite complement and full coupling. Lean proves their assembly and the
restriction to every smaller support. It also independently proves
`3<exp(6/5)<4` and completeness of the active prime-power set `{2,3}`.
The numerical matrices and the analytic identification of Q have **not**
been imported as axioms or proved in Lean.

There is a second numerical certificate, using the stronger block-Schur
inequality. If `ell>epsilon` and
`B^2 <= (ell-epsilon)(d-epsilon)`, then

\[
 ell x^2+d y^2-2Bxy\ge epsilon(x^2+y^2).
\]

To check this, multiply the difference by `ell-epsilon` and complete the
square `( (ell-epsilon)x-By )^2`; the remaining term is
`[(ell-epsilon)(d-epsilon)-B^2]y^2`. Both are nonnegative.
This inequality and its function-level assembly are now Lean-proved.

The new run has **124 total polynomial modes**, with two 62-dimensional
parity blocks, at the same half-width, frequency cutoff and quadrature order.
It verifies `ell=1e-12`, `epsilon=9.5e-13`, with outward bounds

| Quantity | Safe bound |
|---|---:|
| beta | >0.05655 |
| B | <4.124e-8 |
| D | <7.843e-19 |
| `(ell-epsilon)(beta-D-epsilon)-B^2` | >1.127e-15 |

Thus the same public bound `9e-13` holds. The old estimate `ell-B` is
negative here, so this is a concrete success of the Schur improvement,
not merely an algebraic restatement. The mode count drops by 22.5%; this
is an improvement to this certificate construction, **not** a new C
record, an optimal mode count, or a new Schur-complement theorem.

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/compact_window_certificate.py --count 124 --block-method schur --output research/prime_spectral/window_positivity_exp_1p2_schur.json
uv run --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/verify_window_positivity.py research/prime_spectral/window_positivity_exp_1p2_schur.json --output research/prime_spectral/window_positivity_exp_1p2_schur_verification.json
lake build Reinmann.WeilWindowHypotheses Reinmann.WeilWindowAudit
```

Both certificate runs were regenerated after separating this generator as
`compact_window_certificate.py` from a different implementation that had
replaced `window_positivity_certificate.py` in the shared checkout. Both
received the four adaptive integral comparisons and geometric constant
check. The focused suite now has **10 passing tests**, including the case
where Schur succeeds and the linear allowance fails. The earlier runtime
and eight-test count above describe the original run, not this replay.
See [the next-theorem plan](WEIL_WINDOW_NEXT_THEOREMS_2026_10_07.md).
