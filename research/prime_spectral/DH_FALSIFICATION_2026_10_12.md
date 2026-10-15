# Davenport–Heilbronn falsification: actual completion, actual form

The arithmetic control is now extended to ordinary completed Taylor coefficients, an independently certified off-line zero, the finite ground-state gates, and a negative **full Weil-form trial**. These are separate statements. A positive finite section is not full-window positivity; a negative finite trial does disprove positivity of the full form containing it.

## Datum and coefficient conventions

Use the periodic real coefficients
\[
 a_n=(1,\kappa,-\kappa,-1,0)\quad(n\bmod5=1,2,3,4,0),\qquad
 \kappa=\frac{\sqrt{10-2\sqrt5}-2}{\sqrt5-1},
\]
\[
 H(s)=5^{-s}\sum_{r=1}^4a_r\zeta(s,r/5),\qquad
 \Lambda_H(s)=(5/\pi)^{s/2}\Gamma((s+1)/2)H(s).
\]
The conductor is five, the gamma parity is odd, and the completion is entire and invariant under \(s\mapsto1-s\). The normalization agrees with [Gritsenko](https://www.mathnet.ru/eng/present13282) and [Bombieri–Ghosh](https://www.mathnet.ru/eng/rm9410).

For the Toeplitz experiment,
\[
 \mu_n=[z^{2n}]\Lambda_H(1/2+z)/\Lambda_H(1/2).
\]
These are ordinary folded coefficients. The classical Jensen convention would use \(n!\mu_n\); the scan does not do that. Neither sequence is the logarithmic-derivative sequence \(c_n\) used in the geometric form.

In fact positivity of **all** the ordinary coefficients is compatible with the DH counterexample. To see this, set
\[
 \theta_H(t)=\sum_{n\ge1}n a_n e^{-\pi n^2t/5}.
\]
The completed functional equation gives
\(\theta_H(t)=t^{-3/2}\theta_H(1/t)\). Thus
\(\Psi_H(u)=e^{3u/2}\theta_H(e^{2u})\) is even, and Mellin inversion gives
\[
 \Lambda_H(1/2+z)=4\sqrt{\pi/5}\int_0^\infty
 \Psi_H(u)\cosh(zu)\,du.
\tag{1}
\]
For \(t\ge1\), put \(b=\pi t/5>1/2\). Since \(a_2=\kappa>0\) and \(|a_n|\le1\),
\[
 \theta_H(t)\ge e^{-b}-\sum_{n\ge3}n e^{-bn^2}
 \ge e^{-b}-\frac{e^{-4b}}{2b}>0.
\]
The second inequality follows because \(x e^{-bx^2}\) decreases for \(x\ge2\), so its integral from 2 dominates the sum from 3. Every even moment in (1) is strictly positive. This written argument proves \(\mu_n>0\) at **every** order without implying PF infinity.

## Bounded Toeplitz test: 6,400 positive solid minors

[dh_toeplitz_scan.py](../../experiments/prime_spectral/dh_toeplitz_scan.py) generates 161 coefficients with rigorous Hurwitz-zeta/gamma power series at 4096 bits. Odd jets must enclose zero, checking the central functional-equation parity. It then checks
\[
 D_{r,s}=\det(\mu_{s+i-j})_{0\le i,j<r},\qquad
 1\le r\le80,\quad1\le s\le80,
\]
with \(\mu_k=0\) for \(k<0\). The positive rescaling \(\mu_n\mapsto100^n\mu_n\) improves arithmetic scaling and multiplies \(D_{r,s}\) by \(100^{rs}\), preserving its sign.

All 6,400 determinants are strictly positive, with no unresolved interval signs; the [result](verification_2026_10_12_remaining/dh_toeplitz_rank80_shift80.json) records per-rank counts, coefficient balls, source hashes and a digest of the full ordered sign stream. A synthetic polynomial \(1+z+z^2\) supplies a negative order-three control for the scanner.

**No first negative Toeplitz minor was found.** This experiment covers one explicitly ordered family of solid minors; it does not enumerate arbitrary row/column subsets or unbounded shifts. The independently certified nonreal folded zero excludes PF infinity by the classical entire-function characterization, so some minor must fail. This run does not identify it. The fact that this large finite family survives is itself a warning against treating finite coefficient positivity as a distinguishing step.

## Independent off-line zero certificate

[dh_zero_and_gates.py](../../experiments/prime_spectral/dh_zero_and_gates.py) certifies exactly one simple zero in the disk of radius \(10^{-30}\) centered at the exact dyadic representative of
\[
 0.80851718245663738555335196060684412785067026830502
 +85.699348485377592171929267708941729037987829423408\,i.
\]
At 768 bits, the center residual is below \(5.317\,10^{-49}\). On a rectangle containing the disk, the derivative variation from the exact midpoint derivative is below \(2.44\,10^{-28}\). The Rouché inequality
\[
 |H(s_0)|+r\sup_{|s-s_0|\le r}|H'(s)-d_0|<r|d_0|
\]
compares \(H\) to \(d_0(s-s_0)\) and proves the count. The disk lies strictly to the right of \(0.8085\). The gamma and conductor factors are finite and nonzero there, so this is also a zero of the completed datum.

The numerical center is from a [prior computational report](https://github.com/teal-sea/zeta-lab/issues/57); the special-function balls and Rouché check are independently executed here. The result is in [dh_zero_and_finite_gates.json](verification_2026_10_12_remaining/dh_zero_and_finite_gates.json). This does not certify that it is the lowest off-line zero.

## The correct geometric form and a negative window

Write \(q(y)=(f^**f)(y)+(f^**f)(-y)\), with \(f\) on an additive interval of length \(S=\log C\). Let \(A_{\gamma,\zeta}\) denote the zeta archimedean contribution **without** its pole term. The gamma-factor change has the exact form
\[
 Q_H(f)=A_{\gamma,\zeta}(f)+\log5\,\|f\|^2
 +\int_0^S\frac{q(y)}{2\cosh(y/2)}\,dy
 -\sum_{2\le n<C}\frac{c_n}{\sqrt n}q(\log n).
\tag{2}
\]
Here \(-H'/H=\sum c_n n^{-s}\) in its half-plane of absolute convergence. Equation (2) follows from the conductor term and the difference of the odd and even gamma kernels,
\[
 \frac{e^{-y/2}-e^{-3y/2}}{1-e^{-2y}}=\frac1{2\cosh(y/2)}.
\]
There is no zeta pole block. All integers in the support enter the last sum, including \(c_6=(1+\kappa^2)\log6\). Zeta's restriction of nontrivial zeros to \(0<\Re s<1\) is not assumed for DH.

[dh_weil_certificate.py](../../experiments/prime_spectral/dh_weil_certificate.py) independently integrates (2) in Arb on the repository trigonometric basis. Divided differences assemble off-diagonals; tests compare them against direct integrals and check the gamma change against the independent digamma reflection identity.

At **multiplicative \(C=31\)**, \(S=\log31\), the following statements are certified:

- Every even leading section through degree 59 is positive definite.
- The even section through degree 60 has a negative pivot. An exact rational trial recovered by backward substitution has full-form Rayleigh quotient
  \[
  -1.5310\,10^{-31}<Q_H(f)/\|f\|^2<-1.5309\,10^{-31}.
  \]
- The odd section through degree 60 is positive definite.

The [saved matrices, pivots and explicit trial](verification_2026_10_12_remaining/dh_weil_C31_N60.json) allow direct replay of the negative quotient. No omitted-mode correction is needed to prove negativity of this explicit finite trial in the full form.

This reproduces the transition reported by the [earlier computational study](https://github.com/teal-sea/zeta-lab/issues/57), using our own geometric integral assembly and rational witness rather than importing its certificate. **First degree 60 at C=31** is established within this nested even family. Neither the smallest full negative support nor the first cell on a two-parameter infinite grid has been established here.

## Which hypotheses survive the negative control?

At \(C=13\), degree 16, interval inertia and eigenvalue bisection additionally certify a positive simple even ground state and nonzero boundary evaluation. Its lowest even value is about \(1.18853\,10^{-10}\), its lowest odd value about \(1.35883\,10^{-7}\), and its full finite ground gap exceeds \(1.3576\,10^{-7}\). This is a **finite** statement.

| Hypothesis family in the active repository routes | DH outcome | Consequence |
|---|---|---|
| Entire completion, reflection equation, real central coefficients | Holds; normalization from primary references and parity jets checked | These symmetries do not distinguish zeta |
| Positive ordinary completed coefficients | Holds at all orders by (1) | Coefficient positivity alone is insufficient |
| Solid Toeplitz tests on the specified rank/shift grid | All 6,400 pass | This finite evidence misses a genuine off-line zero |
| PF infinity / all-degree all-shift Jensen hyperbolicity | Fails by the certified off-line zero and classical equivalence | Locating the first concrete failing minor remains open |
| Nonnegative prime-power-supported log-derivative measure | Fails at \(c_3<0\), mixed-prime support at \(c_6\ne0\) | A concrete Euler-specific distinction |
| Finite positivity, simple even ground state, nonzero boundary trace | Holds at C=13, degree 16 | These finite real-zero construction gates are not the missing global theorem |
| Positivity of the full form on every support | Fails by the C=31 rational trial | A genuine arithmetic/full-form falsification |
| Generic real-zero approximants and self-adjoint construction, under finite gates | The hypotheses pass at the certified finite DH cell | Generic construction by itself is insufficient |
| Nonzero locally uniform limit of real-zero approximants equal to the completed target | Impossible for DH by Hurwitz and the certified off-line zero | Uniform target identification is essential |
| Nonzero indefinite cross-pairing / generic pseudo-Hermitian algebra | Compatible with nonreal eigenvalues | Does not force the paired-defect budget |
| Paired-defect budget for a zero state | Violated by the off-line zero in the analogous Green identity | It remains the substantive spectral input, not a consequence of mass normalization |
| Prolate concentration estimates | Arithmetic-independent | Need an Euler-specific transfer to the actual Weil operator |
| Full growing-support cluster estimates / adjoint candidate transfer | Not instantiated for DH here | Need a new comparison construction; zeta certificates cannot be relabeled |

This is an audit of the active **hypothesis families**, not a claim that every Lean declaration was mechanically ported. The unperformed growing-support tests, first negative Toeplitz minor, and smallest full negative window remain explicit obligations.
