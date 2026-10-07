# Assembled trials with certified full residuals: a failed trace-transfer test

The requested trial assembly and full-residual enclosure are now concrete
at primes 2 and 3. **These trials fail the nonzero minimizing-state trace
test.** The failure is certified by a lower bound on their full residual,
not just an overly large upper bound. No larger positive window or RH
proof results. The useful new information is a stronger actual spectral
gap and an explicit obstruction to reusing the saved cosine trials with
only a tiny endpoint repair.

All infinite-dimensional operator/renewal/form steps below are written
analysis. Arb encloses the constants and finite integrals. Lean checks
four scalar implications from named hypotheses, not these operator facts.

## 1. Stronger full-operator threshold gaps

Use the lower-operator construction and infinite-complement min–max
argument in [the window proof](WINDOW_POSITIVITY_PROOF_2026_10_07.md).
Both parity sectors and the complete polynomial complement are included.
For a comparison interval containing the threshold interval,

\[
 A_{\rm comparison}\ge (G-\varepsilon)\oplus\beta-(B+D)I.
\]

If exactly one eigenvalue of the combined finite block lies below
\(\eta+\varepsilon\), and \(\beta>\eta\), then
\(\lambda_2(A_{\rm threshold})\ge\eta-B-D\).
The support-inclusion step is the usual form min–max principle.
This is a full-operator bound, not a finite simplicity assertion or a
positivity-minor scan.

At prime 2 the saved length-0.7 comparison permits \(\eta=0.057\),
giving \(\lambda_2>0.0569999815\). At prime 3 a newly assembled
length-1.1 comparison, closer than the preceding length-1.2 comparison,
permits \(\eta=0.00000412\). Its infinite errors are small enough to
retain \(\lambda_2>0.000004119\). Use the weakened thresholds

\[
 L_{2,2}=0.056999,\quad L_{2,3}=0.000004119,
 \quad U_2=0.00142,\quad U_3=0.000000103.
\]

Thus the full complementary clearances are
\(g_2=0.055579\) and \(g_3=0.000004016\), compared with the earlier
0.00857 and \(6\,10^{-9}\). The retained reassembly checks every entry
of both lower blocks at different quadrature orders and 512 bits, then
replays these stronger shifts. It uses the same generator and backend,
not an independent implementation or analytic review.

## 2. The actual assembled functions

Let \(L=\log q\), with coordinate \(x\in(0,L)\). Normalize the saved
nine cosine coefficients in the orthonormal basis
\(e_0=L^{-1/2}\),
\(e_j=(2/L)^{1/2}\cos(2\pi jx/L)\), \(1\le j\le8\), to give \(g\).
Its equal endpoint values are denoted by \(b=g(0)=g(L)\).
The saved coefficients are exact decimal rationals; they are not
intervals asserted to contain the actual minimizing state.

Put \(r=e^{-64}\). On the half-line define \(\chi_r=1\) on \([0,r]\),
\(\chi_r=(2r-x)/r\) on \([r,2r]\), and zero thereafter.
With the normalized Green function \(h=h_{1/2}\) from
[the boundary-basis note](BOUNDARY_BASIS_RESIDUAL_TRACE_2026_10_07.md), set

\[
 \phi_-(x)=\chi_r(x)h(x),\qquad \phi_+(x)=\phi_-(L-x),
\]
\[
 F=g-b(\chi_r(x)+\chi_r(L-x))+\theta(\phi_-+\phi_+),
 \quad f=F/N,\quad N=\|F\|_2,
 \quad \theta_2=1/5,\quad\theta_3=1/400.                       \tag{1}
\]

The smooth part \(p=g-b(\chi_r+\chi_r^{\rm reflected})\) vanishes at
both endpoints and has a globally Lipschitz zero extension. The Green
parts belong to the operator domain by the cutoff/closedness proof.
Consequently \(f\in D(A_I)\). Its two EXACT normalized traces are
\(\theta J_{1/2}/N\), since \(p(x)=O(x)\) at either endpoint and
\(x/V(x)\to0\). This proves nonzero trial traces only.

The very small \(r\) tests a specific proposal: preserve the saved bulk
trial while repairing its endpoint behavior. No optimization claim is
made for these coefficients or for this cutoff. Failure of this proposal
does not exclude macroscopic renewal corrections or other trial families.

## 3. Bounds which include the full nonlocal tails

Write \(E_0=c+Lk_*+m\) for the bound on \(A-B_I\), as in the preceding
note. The Green function obeys
\(H=3J_{1/2}V(1)\ge\|h\|_\infty\).
On the cutoff supports, use
\(H_\ell=J_{1/2}V(e^{-32})\ge h(x)\), since \(2r<e^{-32}\).
The previously certified Laplace/concavity interval supplies this latter
mass bound. No evaluation at an unbounded endpoint derivative is used.

For \(0<r<1\),
\[
 E_1(r)=\int_r^\infty e^{-t}\frac{dt}{t}
 \le\log(1/r)+e^{-1}=:T_r.
\]
The half-line commutator is bounded by integrating
\(\min(1,|z|/r)\nu(z)\), \(\nu(z)=e^{-|z|}/(2|z|)\):
\[
 \|[B_H,\chi_r]h\|_\infty\le H(1+T_r),\quad
 P_B:=1+H(1+T_r)\ge\|B_H(\chi_rh)\|_\infty.                 \tag{2}
\]
This logarithmic allowance is sharper than the previous crude
Lipschitz-constant bound proportional to \(1/r\).

The zero-extended cutoff is nonnegative, bounded by 1, has total
variation 2, and \(\|\chi_r\|_2^2\le2r\). Therefore
\[
 \|\chi_r-T_z\chi_r\|_2^2\le\min(2|z|,4r).
\]
Integrating this in the Lévy form, and its square root in the Bochner
operator integral, gives respectively
\[
 Q_B(\chi_r)\le r(1+2T_r),\qquad
 \|B\chi_r\|_2\le\sqrt r(2\sqrt2+2T_r)=:D_r.                \tag{3}
\]
For the half-line commutator, extend \(h\) by zero and bound it by \(H\)
under the translated cutoff difference. Minkowski then gives
\[
 \|B_H(\chi_rh)\|_2\le\sqrt{2r}+H D_r,
 \quad Q_B(\chi_rh)\le2rH_\ell P_B.                         \tag{4}
\]
Importantly, (4) includes the forcing outside the cutoff support.
Multiplying an Linfinity bound by the square root of that support alone
would omit a nonlocal tail and would not prove the L2 assertion.

For \(e=F-g\), disjoint supports give
\(\|e\|_2\le d=\sqrt{4r}(|b|+\theta H_\ell)\) and
\(1-d\le N\le1+d\). Cauchy–Schwarz in the positive comparison form yields
\[
 Q_B(e)\le[2\theta\sqrt{2rH_\ell P_B}
                +2|b|\sqrt{r(1+2T_r)}]^2,
 \quad Q_A(e)\le Q_B(e)+E_0d^2=:E.
\]
The full comparison certificate gives \(A_I\ge0\), so Cauchy–Schwarz
in its ACTUAL positive form yields
\[
 |Q_A(F)-Q_A(g)|\le2\sqrt{Q_A(g)E}+E.                       \tag{5}
\]
Here \(Q_A(g)\) is an exact finite trial Rayleigh integral, not a lower
bound on the full operator. Dividing (5) by the enclosed \(N^2\)
certifies the actual assembled Rayleigh quotient \(\mu\).

For an upper bound on \(\|Af-\mu f\|_2\), let
\(P\ge\|g\|_\infty\), \(D\ge\|g'\|_\infty\).
The interior jump integral gives a regular part bounded by \(D\), and
the exterior term is
\(g(x)[E_1(x)+E_1(L-x)]/2\). Since
\(\int_0^\infty E_1(x)^2dx=2\log2\),
\[
 \|B_Ig\|_2\le\sqrt L D+P\sqrt{2\log2}.
\]
Equations (3)–(4) also bound \(\|Ae\|_2\), including its tails.
Adding \(E_0\), normalizing and adding \(|\mu|\) gives the recorded
full L2 residual upper bound.

For the full Linfinity upper bound use the globally Lipschitz part \(p\).
Let \(P_p=P+|b|\), \(M_1=D+|b|/r\), \(s=2P_p/M_1<1\).
Integrating its global modulus \(\min(M_1|z|,2P_p)\) proves
\[
 \|B_Ip\|_\infty\le2P_p[1+\log(1/s)+e^{-1}].
\]
Add \(2\theta P_B\), the bounded perturbation and \(\mu F\), then
divide by the norm lower bound. This certifies the WHOLE residual;
no projected residual is substituted for it.

## 4. A full-residual lower bound and the failed gate

Take the unit cosine \(e_9\), outside the saved trial space. Exact Arb
Weil integrals give
\[
 C_9=\langle Ag,e_9\rangle
 \approx0.00722377652138\ (q=2),\qquad
 0.000110357474957\ (q=3).
\]
Since \(\langle g,e_9\rangle=0\),
\[
 \| (A-\mu)f\|_2\ge
 \frac{|C_9|-\|Ae\|_2-|\mu|d}{1+d}.                        \tag{6}
\]
This is a lower bound on the FULL operator residual. The certified
lower endpoints in (6) exceed 0.00722377650 and 0.0001103574747.
The endpoint repair has not corrected this bulk error.

| Threshold | Enclosed actual trial Rayleigh quotient | Either actual trial trace | Full L2 residual lower bound |
|---|---|---|---|
| 2 | [0.0014190247689365, 0.0014190247689769] | [0.72569644250419, 0.72569644250421] | >0.00722377650 |
| 3 | [1.0256014537613, 1.0256014538036] times \(10^{-7}\) | [0.00907120553130244, 0.00907120553130245] | >0.0001103574747 |

The full L2 residual upper bounds are conservative: less than 17.298
and 15.601. The full Linfinity upper bounds are less than 910 and 218.
These are legitimate residual enclosures, not small-error certificates.
The JSON retains rational endpoints and precise norm intervals.

With the stronger gaps, the sufficient linear trace-error bound remains
\(A\epsilon_2+B\epsilon_\infty\). Even setting the second term to zero,
the certified LOWER bound on the first term exceeds the positive trial
trace by more than 278 at prime 2 and 376264 at prime 3. Thus these
trials cannot clear this interface's nonzero-trace sufficient condition,
even if their residual upper bounds were evaluated sharply. At prime 3,
(6) already exceeds the complementary clearance itself.

The improved split L2 budget for a complementary trace error of \(10^{-3}\)
is approximately \(1.29\,10^{-8}\) at prime 2 and \(1.47\,10^{-13}\)
at prime 3. These are requirements, not achieved residuals.
No lower bound on the true minimizing-state trace follows from (1).
No negative conclusion about that trace follows from the failed test.

### A structural obstruction: L2 graph convergence does not control traces

The cutoff estimates also prove more than the failure of two trials.
For any sequence \(r\downarrow0\), let \(\psi_r=\chi_r h\). Every
\(\psi_r\) belongs to \(D(A_I)\) and has bounded full forcing, and
\(\tau_-(\psi_r)=J_{1/2}\ne0\), \(\tau_+(\psi_r)=0\). Yet

\[
 \|\psi_r\|_2\le H\sqrt{2r}\to0,\qquad
 \|A_I\psi_r\|_2
 \le\sqrt{2r}+H\sqrt r(2\sqrt2+2\log(1/r)+2/e)
                         +E_0H\sqrt{2r}\to0.                \tag{7}
\]

Thus there is NO finite constant bounding this endpoint trace by the
L2 operator graph norm, even on the subset with individually bounded
forcing. The missing condition is a UNIFORM stronger forcing bound.
This is an explicit obstruction for the actual Weil operator; no priority
claim is made for general trace unboundedness in logarithmic spaces.

In particular, let \(u\) be a unit simple actual ground state with its
established finite trace, and fix real \(t\ne0\). Then
\(f_r=(u+t\psi_r)/\|u+t\psi_r\|_2\) converges to \(u\) in graph norm.
Its Rayleigh quotient tends to \(\lambda_1\), and its full L2 residual
tends to zero. Nevertheless
\(\tau_-(f_r)\to\tau_-(u)+tJ_{1/2}\), not \(\tau_-(u)\).
A complementary spectral gap does not repair this discontinuity.
These are trials, not a sequence of actual minimizing states; the
previous convergence proof for the two actual states uses their
uniform forcing bounds and is unaffected.

Consequently minimizing only a full L2 residual cannot validate the
boundary coefficient. Joint Linfinity or weighted-forcing certification
is an essential mathematical input, not an optional numerical refinement.

## 5. Larger-window status and next experiment

There is no positive-window enlargement from this experiment. A separate
repository certificate uses \(L=1.6094\), hence
\(C=e^{1.6094}=4.9998104414\ldots\), not 4.9976. Its summary previously
claimed every window below prime 5, but a proof up to this particular
\(L\) leaves the interval \(e^{1.6094}<C<5\) uncovered. That scalar
coverage error is corrected; its larger certificate is not newly audited
or extended here.

The next trial should correct the bulk residual and the boundary forcing
together, using renewal functions on a macroscopic endpoint interval
and interior corrections. Merely shrinking the repair layer leaves the
certified component (6) intact. Residual minimization must use the full
operator, and the final certificate must retain the complement. The
stronger gaps reduce the difficulty but do not resolve it. No paper or
novelty claim is justified by a failed trial certificate alone.

## 6. Targeted literature check for the graph-norm obstruction

The established Green/renewal input remains
[Grzywny–Ryznar, Proposition 3.2 and Lemma 4.3](https://arxiv.org/pdf/1107.0745).
Their normalization and half-line factorization are not discoveries here.
[Hernández-Santamaría, López Ríos and Saldaña, Theorem 1.1 and Introduction](https://arxiv.org/html/2401.18033v2)
give optimal logarithmic boundary bounds with bounded forcing, and
explicitly distinguish the symbols \(2\log|\xi|\) and
\(\log(1+|\xi|^2)\). They do not license replacing a bounded-forcing
estimate by an L2 graph-norm trace estimate. Our construction (7) explains
that distinction for this particular full Weil operator.

Searches combining logarithmic Laplacian, graph norm, boundary trace,
renewal and eigenfunction convergence did not establish priority for (7).
Generic Gaussian logarithmic Sobolev trace inequalities concern a
different function space and are not evidence for this normalized trace.
The two primary texts above were opened and compared; unrelated search
results were not adopted as sources. This is a targeted check, not an
exhaustive prior-art review or a novelty clearance.
