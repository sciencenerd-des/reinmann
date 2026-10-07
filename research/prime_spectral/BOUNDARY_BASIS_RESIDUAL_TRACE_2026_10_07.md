# Exact-trace trials and full-residual trace enclosures

This continues the actual-state trace calculation, not the support endpoint
record. The analytic arguments below are written proofs with established
potential-theory inputs; the Lean file checks explicitly conditional scalar
steps. No assembled unit trial has yet had its full residual certified.

## 1. Normalization and calibrated profiles

Use the exterior-Dirichlet operator with symbol
\(b(\xi)=\tfrac12\log(1+\xi^2)\), and its normalized ladder exponent
\(\kappa\). Proposition 3.2 and Lemma 4.1 of
[Grzywny–Ryznar](https://arxiv.org/pdf/1107.0745) specialize to

\[
 v(x)=V'(x)=\sqrt2+\int_1^\infty\rho(s)e^{-sx}\,ds,
 \qquad \rho(s)=\frac{2\kappa(s)}{\log^2(s^2-1)+\pi^2}.
\]

In particular \(v\) decreases, \(V\) increases and is concave, and
\(J_a:=\int_0^\infty e^{-at}v(t)dt=1/\kappa(a)\).
These are established representations, not novelty claims. For \(0<a<1\),
subtracting this known Laplace transform gives the faster convergent formula

\[
 V(x)=\sqrt2x+J_a-\frac{\sqrt2}{a}
 +\int_1^\infty\rho(s)
   \left(\frac{a}{s(s+a)}-\frac{e^{-sx}}s\right)ds.                 \tag{1}
\]

The half-line Green factorization gives a positive bounded basis function

\[
 h_a(x)=G_H(e^{-a\cdot})(x)
       =J_a\int_0^x v(x-t)e^{-at}dt,
 \qquad \lim_{x\downarrow0}h_a(x)/V(x)=J_a.                      \tag{2}
\]

Indeed the inner Green forcing equals \(e^{-as}J_a\). Convolution in (2)
and the same calibration give

\[
 h_a(x)=J_a\left[\frac{\sqrt2}{a}(1-2e^{-ax})+e^{-ax}J_a
 +\int_1^\infty\rho(s)
  \left(\frac{2ae^{-ax}}{s^2-a^2}-\frac{e^{-sx}}{s-a}\right)ds\right]. \tag{3}
\]

Also \(e^{-ax}J_aV(x)\le h_a(x)\le J_aV(x)\). Splitting the
convolution at renewal distance 1, and using \(v(1)\le V(1)\), proves
\(h_a(x)\le J_aV(1)(1+1/a)\) for all \(x\). It is not globally in
\(L^2(H)\); no global operator-domain claim for \(h_a\) is used.

## 2. Quadrature, interpolation and both infinite tails

Set \(z=\log(s^2-1)\), \(s(z)=\sqrt{1+e^z}\). Then
\(\rho(s)ds=g(z)e^z/[s(z)(z^2+\pi^2)]dz\), where
\(g(z)=\kappa(s(z))\). The Wiener–Hopf evaluator encloses every node,
including its own infinite tails. Arb integrates the resulting Newton
polynomial times the analytic kernels; interpolation is NOT treated as exact.

Here is the interpolation allowance. Complete Bernstein functions obey
\(|\kappa(w)|\le\sec(\arg w)\kappa(|w|)\) in the right half-plane:
apply the positive Stieltjes representation term by term. Concavity gives
\(\kappa(cs)\le c\kappa(s)\) for \(c\ge1\). On a unit complex disk
centered at a real \(t\in[A,B]\), \(|\arg s(z)|\le1/2\) and
\(|s(z)|\le e^{1/2}s(B)\). Hence
\(|g(z)|\le e^{1/2}\sec(1/2)\kappa(s(B))<2\kappa(s(B))\).
The Wiener–Hopf formula and Jensen give
\(\kappa(s)\le\sqrt{\log(1+s)}\): the half-Cauchy expectation of
\(b(sT)\) is \(\log(1+s)\). Cauchy's derivative estimate therefore gives
\(|g^{(n)}(t)|/n!\le2\sqrt{\log(1+s(B))}\).
For \(n\) Chebyshev roots on a panel of width \(d\), the monic product
has supremum \(2(d/4)^n\). The pointwise interpolation allowance is thus

\[
 E_{A,B,n}=4\sqrt{\log(1+s(B))}(d/4)^n.                        \tag{4}
\]

Multiply (4) by the rigorously integrated SUM of the two positive kernels
in (1) or (3). This bounds the signed-kernel error without taking a
nonanalytic absolute value inside the quadrature.

For a left cutoff \(A\le0\), use \(s\ge1\),
\(\kappa(s)\le\sqrt{\log(1+\sqrt2)}<1\), and \(z^2+\pi^2\ge\pi^2\).
The omitted absolute integrals are at most
\((1+a)e^A/\pi^2\) for (1), and
\([2a/(1-a^2)+1/(1-a)]e^A/\pi^2\) for the inner integral in (3).

For a right cutoff \(B\ge2\), put \(R=B/2\), \(S=e^R\),
\(H=R+\log2\). Since \(\rho(s)\le2\sqrt{\log(1+s)}/\pi^2\),
concavity of the square root yields

\[
 I_2:=\int_S^\infty\rho(s)s^{-2}ds
 \le\frac2{\pi^2}e^{-R}(\sqrt H+1/(2\sqrt H)),
 \quad
 I_e:=\int_S^\infty\rho(s)e^{-sx}s^{-1}ds
 \le\frac{2e^{-Sx}}{\pi^2x\sqrt S}.
\]

We enlarged the actual tail to start at \(S\), and used
\(\log(1+s)\le s\) in the second estimate. The allowances are
\(aI_2+I_e\) for (1), and \(2aI_2/(1-a^2)+I_e/(1-a)\) inside (3).
All errors are added before multiplying the basis formula by \(J_a\).

The retained runs use \(a=1/2\), \(z\in[-32,48]\), 256 bits,
12 nodes/width 1 and 24 nodes/width 2. They overlap at every requested
profile. A coarser 16-node/width-2 attempt failed the strict convolution
ratio check at \(e^{-8}\); it produced no successful certificate.
The alternate run changes discretization, not implementation or backend.
For example the first run encloses
\(V(1)\in[2.2329106422,2.2329106914]\),
\(h_{1/2}(1)\in[5.9204701603,5.9204704474]\), and
\(J_{1/2}\in[3.6284822125,3.6284822126]\).

## 3. A legitimate exact-trace operator-domain trial

Fix \(r=1/8\), \(L>4r\), and a Lipschitz cutoff \(\chi\), equal to 1
on \([0,r]\), zero on \([2r,\infty)\), with Lipschitz constant \(1/r\).
Then \(\phi_-(x)=\chi(x)h_a(x)\), and its reflection \(\phi_+\),
belong to \(D(B_I)=D(A_I)\), with traces respectively \((J_a,0)\)
and \((0,J_a)\).

For completeness use \(h_\epsilon=(B_H+\epsilon)^{-1}e^{-a\cdot}\).
Positivity gives \(0\le h_\epsilon\uparrow h_a\le H_a\), with the
global bound following (3). The commutator kernel is
\((\chi(x)-\chi(y))h_\epsilon(y)\nu(x-y)\), where
\(\nu(z)=e^{-|z|}/(2|z|)\) and \(\int|z|\nu(z)dz=1\).
It is bounded by \(H_a/r\); for \(x\ge2r+1\) its absolute value is
at most \(H_a r e^{2r}e^{-x}\). Dominated convergence holds in \(L^2\).
The Lipschitz multiplier identity, obtained first for truncated jump
kernels and then by the form identity, is

\[
 B_H(\chi h_\epsilon)=\chi(e^{-a\cdot}-\epsilon h_\epsilon)
                         +[B_H,\chi]h_\epsilon.
\]

Closedness gives the claimed half-line domain inclusion. Restriction to
\(I\) follows by the exterior-Dirichlet form identity and form density;
the restricted forcing is in \(L^2(I)\). The other terms of \(A_I\)
are bounded operators. Thus a trial
\(f=(\alpha\phi_-+\beta\phi_++p)/N\), with interior
\(p\in C_c^\infty(I)\) and its actual norm \(N>0\), has exact traces
\((\alpha J_a/N,\beta J_a/N)\). Certifying \(N\), the Rayleigh quotient
and the FULL residual of such a trial remains to be done.

## 4. Linear full-residual-to-trace estimate

Let \(A=B-c+K-S\), \(c=\log(2\pi)\),
\(\|K\|_{2\to2},\|K\|_{\infty\to\infty}\le\kappa_I=Lk_*\),
\(k_*=5/4+2\cosh(L/2)\), and corresponding norms of \(S\) at most
\(m\). Write \(E_0=c+\kappa_I+m\). Suppose the actual normalized simple
ground state satisfies \(\|u\|_\infty\le M\), and \(\lambda_2\ge L_2\).
For a real unit \(f\in D(A)\), put \(\mu=\langle Af,f\rangle\le U<L_2\)
and assume certified full residual bounds
\(\|(A-\mu)f\|_2\le\epsilon_2\),
\(\|(A-\mu)f\|_\infty\le\epsilon_\infty\).

Choose the ground-state sign so \(c_0=\langle u,f\rangle\ge0\).
For \(Q=1-|u\rangle\langle u|\), \(v=Qf\), and \(g=L_2-U\),

\[
 \|v\|_2\le\epsilon_2/g,\quad
 \sqrt{1-(\epsilon_2/g)^2}\le c_0\le1,\quad
 \|Q(A-\mu)f\|_\infty\le(1+M\sqrt L)\epsilon_\infty.          \tag{5}
\]

The square root requires \(\epsilon_2/g<1\). Heat smoothing from the
previous signed-operator analysis gives, for \(t>1/2\),

\[
 H_t=e^{E_0t}(C_t+t\sqrt L k_*),\quad
 C_t^2=\frac{\Gamma(t-1/2)}{2\sqrt\pi\Gamma(t)}.
\]

The \(L^\infty\) semigroup bound is \(e^{E_0s}\), obtained by bounded
perturbation of the sub-Markov comparison semigroup; positivity of the
Weil semigroup is not assumed. Duhamel applied to
\((A-\mu)v=Q(A-\mu)f\) implies

\[
 \|v\|_\infty\le e^{Ut}H_t\epsilon_2/g
       +t e^{(U+E_0)t}(1+M\sqrt L)\epsilon_\infty.              \tag{6}
\]

Here \(\mu\ge-E_0\). One may select \(M=e^{Ut}H_t\) at the same time
as the ground-state heat bound. Localizing \(v\) with the cutoff above,
its forcing has supremum at most \(G\|v\|_\infty+Q_\infty\epsilon_\infty\),
where
\(G=\max(\kappa_I+m,U+c)+\kappa_I+m+8\) and
\(Q_\infty=1+M\sqrt L\). Its integral is bounded by 5/4 times this
supremum plus \(\|v\|_\infty/(8e)\). The established signed Green trace
bound therefore gives, at either endpoint,

\[
 |\tau(v)|\le A\epsilon_2+B\epsilon_\infty,\qquad
 \alpha=V(1)(9G/4+1/(8e)),\quad A=\alpha M/g,
\]
\[
 B=Q_\infty\{\alpha t e^{(U+E_0)t}+9V(1)/4\}.                \tag{7}
\]

This is linear in actual residual bounds; a finite projected residual
does not establish either input. If \(\tau(f)\in[p,q]\), set
\(T=A\epsilon_2+B\epsilon_\infty\), \(s=\sqrt{1-(\epsilon_2/g)^2}\).
The actual \(\tau(u)\) lies between the minimum and maximum of
\(p-T,q+T,(p-T)/s,(q+T)/s\). All four corners are needed for signed
traces. The factor \(c_0\) must not be silently replaced by 1.

## 5. Sharper enclosures for both actual minimizing states

The previously enclosed threshold ground eigenvalues give
\(U_2=0.00142\), \(U_3=1.03\,10^{-7}\).
Zero extension of the threshold ground state to any larger interval in
the next prime cell preserves its old Rayleigh value. Its newly active
prime overlap is zero because its support has length \(\log q\).
Thus the SAME upper bound holds for both the full and prime-omitted
minimizers throughout each cell, without assuming their quantitative
convergence or a moving-window spectral gap.

Applying the heat/forcing estimates at the largest cell length gives
the following outward integer bounds on both actual normalized states:

| Prime cell | \(\|u\|_\infty\) | Either \(|\tau(u)|\) |
|---|---:|---:|
| \(\log2\le L\le7/10\) | 59 | 4336 |
| \(\log3\le L\le6/5\) | 389 | 41395 |

These replace the earlier common trace bound 579119 on these cells.
They are coarse absolute enclosures, not a nonzero trace certificate.
Together with the preceding common-limit proof they bound both states
while they converge to the same threshold state; they do not provide
an explicit rate of trace convergence in \(L-\log q\).

At the fixed thresholds, use the full complementary clearances
\(g_2=0.00857\), \(g_3=6\,10^{-9}\). Approximate coefficients in (7)
are \((A_2,B_2)=(2.50633\,10^5,1.02740\,10^4)\) and
\((A_3,B_3)=(2.28210\,10^{12},2.71600\,10^5)\).
The retained JSON supplies rational outward endpoints. Splitting a
complement-trace tolerance \(10^{-3}\) equally between the two residual
terms calls for approximately \(\epsilon_2\le2.19\,10^{-16}\) and
\(\epsilon_\infty\le1.84\,10^{-9}\) at prime 3. Use the lower endpoints
of the saved budgets, not these rounded figures, for an implementation.
These are requirements, not attained residuals or a normalized-state
trace-error certificate.

## 6. Status and the next concrete step

The calibrated Green basis supplies admissible trials with known traces;
(7) supplies the missing certificate interface. Next assemble one such
trial with interior corrections, certify its norm and full residual,
and propagate it through the signed four-corner enclosure. The tiny
prime-3 complementary gap is a practical obstruction worth improving
with a closer full-complement comparison, rather than finite minors.
No larger positive window, RH proof, or cleared novelty claim follows
from this continuation. The readiness decision remains unchanged.
