# Direct-side endpoint pricing and DH implication audit (1 November 2026)

**Outcome:** the current balanced probe would need
`|J_eta(Z)| << Z^(-(1+b)/6+epsilon)` to price B=1/2. At the previous
direct-only optimum this is a saving of **11/30**, changing the exponent
from **11/60 to -11/60**. Raising the prime-length cap alone cannot do it,
even if the reflection penalty is removed: the formal length required is
ell=5/3, outside the support geometry.

The **principal reciprocal-Mellin model** at this exponent is a zero-free
reformulation under the explicitly stated growth assumptions below, and
its genuine DH analogue fails. This does **not** establish a GRH
equivalence for the actual compensated arithmetic probe J_eta. A DH
metaplectic version of that probe remains uninstantiated. The gate therefore
does not admit a new arithmetic strategy or a conclusion excluding every
future method in this family.

## Preregistration and source boundary

The JSON and Markdown DH register were updated before development. The
new packet preserves that preregistration and all earlier packet hashes.
The actual probe target retains Eisenstein ideal norms, the fixed target
Hecke character with zero extensions, the original cubic-theta cusp/Gauss
coefficients, excluded primes, the finite subset compensation, and the
disjoint annular physical prime windows. No arbitrary-coefficient or
principal-term substitution is made for J_eta.

Primary source: [Xu–Sang v2](https://arxiv.org/html/2610.15291v2), Section 3
(probe, compensation and normalization), Section 6 (remainder), Section 8
(Mellin continuation). Its source archive is fingerprinted in the earlier
refined packet. [Liu v2](https://arxiv.org/html/2610.26835v2), Section 2.4,
supplies the free-length direct majorant and signal convention. The prior
13/15 audit remains the baseline; its analytic source estimates are not
reproved here.

## 1. Exact pricing

For balanced lengths,

\[
l_x=(1-b-\ell)/2,\quad l_y=(1+b-\ell)/2,\quad
C_b(s)=s-(4+b)/6.
\]

Consequently the required direct exponent is

\[
C_b(1/2)=-(1+b)/6<0\quad(b>0).
\]

The unpenalized current direct exponent is

\[
L=l_x/2+b/12=(1-\ell)/4-b/6,
\]

so the necessary cancellation gain is

\[
L-C_b(1/2)=5/12-\ell/4.
\]

Any retained Gram or reflection penalties must also be paid. The complete
direct-only minimum of B_low is 13/15, hence subtracting a hypothetical
blanket saving gamma from that full majorant would require
`gamma >= 13/15-1/2 = 11/30`. This is a necessary scalar price, not an
arithmetic estimate and not sufficient for the full comparison.

At `(lx,ly,ell)=(7/20,9/20,1/5)`, b=1/10:

\[
L=11/60,\quad C_b(1/2)=-11/60,\quad L-C_b(1/2)=11/30.
\]

For free lengths with the original Liu normalization,

\[
C(1/2)=-1/3+l_x/3+\ell/6,
\]

and the necessary gain is exactly `B_low-1/2`, still at least 11/30 for
the retained majorant.

### Cap-only and penalty-only changes fail

Even optimistically deleting the reflection penalty and continuing the
formula `B(ell)=11/12-ell/4`, B=1/2 would require **ell=5/3**.
But the physical support condition l_x>ell gives

\[
\ell<(1-b)/3,\qquad
B(\ell)=5/6+b/12+\{(1-b)/3-\ell\}/4>5/6.
\]

Even weakening this to l_x>0 gives ell<1-b and

\[
B(\ell)=2/3+b/4+(1-b-\ell)/4>2/3.
\]

At ell=5/3 the sum l_x+l_y=-2/3 is negative. This is formal
extrapolation, not an admissible probe. With the original reflection
penalty retained, the earlier 13/15 obstruction already applies.
Removing only the additive b/12 Gram cost is also insufficient in the
balanced geometry: l_x/2 remains positive while C_b(1/2) is negative.
These observations do not rule out a new estimate using cancellation in
the signed probe or a different normalization/construction.

## 2. The arithmetic probe is not its principal signal

Xu–Sang compare two separate statements for one fixed probe:

\[
J_\eta=f_\eta+R_\eta,\qquad
f_\eta(Z)=\frac1{2\pi i}\int_{(c)}
 Z^{s-c_0}e^{(s-5/6)^2}\frac{G_\eta(s)}{L^S(s,\eta)}\,ds,
\quad c_0=(4+b)/6.
\]

The paper denotes G_eta by H_eta; we rename it here to distinguish it from
the DH function. A strong bound for J alone does not imply the same bound
for f without control of R. Cancellation between f and R is not ruled
out by a bound on J. Conversely, zero-freeness of L alone does not supply
the proposed J bound without a suitable remainder estimate.

The published verification of G_eta's holomorphy and nonvanishing is on
Re(s)>87/100 (Liu's assembly uses an even narrower printed region). We do
not extend that correction or the source's contour/remainder analysis to
Re(s)>1/2 by replacing the direct exponent. These are further obligations.
Thus the implication audit establishes neither
`proposed J bound => family GRH` nor its converse. Not having such a proof
is not evidence that the proposed bound is weaker than GRH.

In particular, “a direct bound plus other assumptions would prove GRH”
does not establish “the direct bound is equivalent to GRH.” No conclusion
closing the whole cubic-theta method family is supported here.

## 3. A precise principal-model reformulation

Let A(s) be a normalized Dirichlet series with meromorphic continuation
to Re(s)>B and an absolutely convergent convolution reciprocal
`1/A(s)=sum beta_n n^(-s)` on some right half-plane. Define, with multiplier
**1**, a0=5/6 and fixed real c0,

\[
F_A(Z)=\frac1{2\pi i}\int_{(c)}
 Z^{s-c_0}\frac{e^{(s-a_0)^2}}{A(s)}\,ds.
\]

Initially choose c in that right half-plane, with bounded reciprocal
there. The Gaussian inversion identity gives the actual coefficient model

\[
F_A(Z)=\frac{Z^{a_0-c_0}}{2\sqrt\pi}
 \sum_{n\ge1}\beta_n n^{-a_0}
 \exp\!\left[-\frac{\log^2(Z/n)}4\right].
\]

Absolute reciprocal convergence implies a polynomial bound on beta_n;
the log-Gaussian makes this series absolutely convergent for every fixed
positive Z. Shifting the initial contour arbitrarily far to the right
shows rapid power decay as Z decreases to zero. This shift stays in the
absolute-convergence half-plane and requires no zero-free conjecture.

**Growth implies zero-freeness.** Suppose, for every epsilon>0,

\[
F_A(Z)=O_\epsilon(Z^{B-c_0+\epsilon})\quad(Z\to\infty).
\]

Then the transform

\[
\int_0^\infty F_A(Z)Z^{-(s-c_0)}\,\frac{dZ}{Z}
\]

is holomorphic for Re(s)>B, by absolute locally uniform convergence.
On the initial right half-plane Gaussian/Fourier inversion identifies it
with `exp((s-a0)^2)/A(s)`. The identity theorem and the exponential's
nonvanishing exclude every zero of A in Re(s)>B. Poles of A cause zeros,
not poles, of its reciprocal. This implication does not need a converse
growth assumption.

**Converse with its precise hypothesis.** If 1/A is holomorphic in that
half-plane and, for each epsilon>0, it satisfies a bound

\[
|1/A(\sigma+it)|\le C_\epsilon e^{\theta_\epsilon t^2},
\quad \theta_\epsilon<1,
\quad B+\epsilon\le\sigma\le c,
\]

uniformly across that strip, horizontal integrals vanish and the contour
may move to B+epsilon. The Gaussian supplies an integrable factor
`exp(-(1-theta_epsilon)*t^2)`, proving the stated growth bound. The
zero-free statement and growth bound are therefore equivalent **within
this explicitly stated contour-growth class**. We do not prove that the
actual arithmetic probe satisfies these hypotheses or identify it with
F_A. A correction multiplier would additionally need holomorphy and
nonvanishing throughout the target region.

For A ranging over the target Hecke family and B=1/2, the forward
implication is as strong as that family's GRH-type half-plane statement.
With the converse hypotheses it is a reformulation, not a new separator.
This is the standard reciprocal-Mellin paradigm already used in the
source's closure proof; no novelty is claimed.

## 4. The DH principal model is genuinely instantiated

Use the ordinary Dirichlet series

\[
D(s)=5^{-s}\{\zeta(s,1/5)+k\zeta(s,2/5)
 -k\zeta(s,3/5)-\zeta(s,4/5)\},\quad
k=\frac{\sqrt{10-2\sqrt5}-2}{\sqrt5-1}.
\]

Its coefficients have period `(0,1,k,-k,-1)` and a_1=1. The implemented
Dirichlet reciprocal uses

\[
\beta_1=1,\quad
\beta_n=-\sum_{d\mid n,\ d>1}a_d\beta_{n/d}.
\]

The code verifies the convolution exactly through n=91 and agrees with
the separate earlier implementation. In particular beta_4=1+k^2 is not
mu(4), and `beta_91-beta_7*beta_13=-1-k^2`. These are ordinary Dirichlet
reciprocal coefficients, not Xi coefficients or ideal-Mobius coefficients.

Since |a_n|<=1, at sigma=3 the nonconstant coefficient l1 norm is at most
`1/8+integral_2^infinity x^(-3)dx = 1/4`. The inverse l1 norm is at most
4/3 by the convergent convolution geometric series. This supplies an
explicit convergence bound for the Gaussian model.

The packet encloses one **infinite** F_D(1/100) value using the first 91
reciprocal terms and a rigorous tail bound. Writing u=log(n), z=log(Z),
the tail factor `exp((3-a0)u-(u-z)^2/4)` decreases for
`u >= z+2*(3-a0)`. At n>=92 and Z=1/100 this applies, so multiplying its
value at 92 by the l1 bound 4/3 and the positive Gaussian prefactor bounds
the full remaining sum. This finite evaluation is an implementation check,
not an asymptotic growth experiment.

The existing off-line disk near
`rho=0.808517182456637...+85.69934848537759...i`, radius 1e-30, is replayed
with 768-bit Arb Hurwitz-zeta derivative enclosures. Rouche's strict
inequality proves one simple zero; the Gaussian weight and resulting pole
residue are enclosed away from zero. No root search or stopped scan is
restarted, and no first/minimal zero is claimed. Therefore F_D cannot obey
the B=1/2 growth bound. A finite plot could miss this obstruction because
the Gaussian weight at this height is extremely small; the argument uses
the nonzero pole, not a fitted growth rate.

This tests the **principal model**, not a DH compensated cubic-theta
probe. A linear combination of individual Hecke probes does not fix that
gap: even when correction multipliers are 1 and p+q=1,

\[
\frac p{L_1}+\frac q{L_2}-\frac1{pL_1+qL_2}
=\frac{pq(L_1-L_2)^2}{L_1L_2(pL_1+qL_2)}.
\]

The actual DH weights have pq=(1+k^2)/4. Thus linearity of the probe or
its direct bound does not transfer the reciprocal-DH principal identity.
The coefficient obstruction and this identity do not prove a new
Hecke-specific cancellation estimate.

## 5. Gate decision

| Object | Status | Consequence |
| --- | --- | --- |
| Cap change or removal of reflection penalty alone | Excluded within retained support and signal normalization | Formal ell=5/3 is inadmissible |
| Strong bound on principal F_A at B=1/2 | Reformulation under stated contour-growth assumptions | Genuine DH growth analogue fails by its nonzero pole |
| Strong bound on actual J_eta | Uninstantiated arithmetic target | No equivalence proved; no DH metaplectic probe; no discriminator |
| Every future direct-side construction | Not classified by this audit | No whole-method impossibility conclusion |

The cheapest calculation is now complete. Arithmetic development stops at
the missing actual-probe DH gate; no RH strategy is activated. Directions B
and C remain optional conditional finite strengthening. A future direct
proposal would need to identify the actual signed coefficient structure
and inequality, instantiate the appropriate DH construction, and account
for the remainder and correction region. Merely restating reciprocal
continuation or invoking Euler support/multiplicativity would not suffice.

## 6. Verification and historical receipts

```sh
python3 -m unittest discover -s experiments/prime_spectral -p 'test_liu*.py' -v
python3 experiments/prime_spectral/check_dh_research_gate.py
uv run --offline --with python-flint==0.8.0 --with mpmath --with sympy==1.14.0 --python 3.12 python experiments/prime_spectral/liu_direct_endpoint.py --replay-dh-zero
python3 research/prime_spectral/verification_2026_11_01_direct_endpoint/validate.py
```

The new gate entry necessarily changes shared register files bound by the
previous refined packet. Its old manifest and validator are immutable:
running that old validator directly against today's evolved registry will
report source-state drift. Before updating the register we snapshotted all
25 previously bound inputs. The new validator replays the old packet in a
temporary historical source tree and separately checks that all 1,669
earlier verification files are unchanged. This preserves the earlier
scientific receipt without pretending that it checked the new register.
No commit, CI, Lean build, arithmetic endpoint proof, or publication is
claimed.
