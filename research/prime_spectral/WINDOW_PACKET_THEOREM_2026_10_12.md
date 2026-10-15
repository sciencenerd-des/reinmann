# A packet-dependent window-to-zero bound

This note supplies a written quantitative implication for D3, with an explicit infinite zero tail. It does **not** prove the requested universal function \(\Phi(\gamma)\). Its remaining packet dependence is displayed rather than hidden. The calculator is [window_packet_bound.py](../../experiments/prime_spectral/window_packet_bound.py); no actual zero packet or window-positivity hypothesis is certified by that calculator.

## Conventions and statement

Write \(z_\rho=\rho-\tfrac12\), with multiplicity. The nontrivial zeta zeros lie in \(0<\Re\rho<1\) without assuming RH. For a real even test function \(h\), put
\[
 H(z)=\int h(x)e^{zx}\,dx,\qquad
 K(t)=W(h^**\tau_t h),\quad \tau_t h(x)=h(x-t).
\]
The zero-side explicit formula gives
\[
 K(t)=\sum_\rho H(z_\rho)^2e^{t z_\rho}.
\tag{1}
\]
The square is an ordinary complex square, **not** an absolute square. Reflection and conjugation make the sum real and even. This is the source of possible indefiniteness off the line.

Let \(h\) be the convolution of \(q\ge2\) normalized uniform densities on \([-a/q,a/q]\). Then \(h\) is real and even, supported on \([-a,a]\), and
\[
 H(z)=\left(\frac{\sinh(az/q)}{az/q}\right)^q,\qquad H(0)=1.
\tag{2}
\]
These continuous piecewise polynomial tests and their convolution squares satisfy the explicit-formula regularity and decay requirements; alternatively smooth each box and pass to the limit under the bounds below.

Assume the full Weil form is nonnegative on all tests whose support span is at most \(S=\log C\), where \(S>2a\). Set \(Q=K(0)\). Then
\[
 Q\ge0,\qquad |K(t)|\le Q\quad (0\le t\le S-2a).
\tag{3}
\]
Indeed the Gram matrix of \(h,\tau_t h\) has diagonal \(Q\) and off-diagonal \(K(t)\). Every linear combination fits in a common interval of length \(2a+t\); common translation preserves the form.

Choose \(T\ge e\) and let \(z_1,\ldots,z_m\) be the **complete** set of distinct centered zeros with \(|\Im z_j|\le T\). Their multiplicities are \(d_j\). Set
\[
 w_j=d_jH(z_j)^2,\quad \zeta_j=e^{h_0z_j},\quad
 V_{\ell j}=\zeta_j^\ell\quad(0\le\ell<m).
\]
Here \(h_0>0\) is a sampling step, chosen so the \(\zeta_j\) are distinct. Define
\[
 R_j=\sum_{\ell=0}^{m-1}|(V^{-1})_{j\ell}|.
\]
Take an integer \(M\ge1\), with
\[
 t_*=(M+m-1)h_0\le \log C-2a.
\tag{4}
\]
For every \(j\) with \(w_j\ne0\), positivity implies
\[
 \Re z_j\le
 \frac{\log\!\left(R_j\,[Q+\mathcal T(a,q,T,t_*)]/|w_j|\right)}
 {M h_0},
\tag{5}
\]
where the entirely explicit tail allowance is
\[
 \mathcal T(a,q,T,t)=
 \left(\frac qa\right)^{2q}e^{a+t/2}
 20q\,T^{1-2q}
 \left(\frac{\log(10T)}{2q-1}+\frac1{(2q-1)^2}\right).
\tag{6}
\]
In particular every off-line zero has \(H(z_j)\ne0\), because the zeros of the hyperbolic-sinc factor are purely imaginary. Formula (5) therefore applies to it if it belongs to the complete packet.

## Proof of the infinite-tail bound

For \(|\Re z|\le\tfrac12\) and \(|\Im z|>T\),
\[
 |H(z)|\le (q/a)^q e^{a/2}|\Im z|^{-q}.
\]
This uses \(|\sinh w|\le\cosh(\Re w)\le e^{|\Re w|}\), not RH. Let \(n(u)\) count zeros of both signs up to absolute ordinate \(u\), including multiplicity. The unconditional [Hasanalizade–Shen–Wong, Corollary 1.2](https://arxiv.org/pdf/2107.06506) implies the deliberately coarse bound
\[
 n(u)=2N(u)\le10u\log(10u),\quad u\ge e.
\]
For example, replace \(\log\log u\) by \(\log u\) in that corollary and drop the negative constant in its main term. Its upper bound is then at most
\(u\log u/\pi+0.7222\log u+18.735\), already smaller than the displayed coarse bound for \(u\ge e\).

Stieltjes integration by parts, dropping the nonpositive lower boundary term, yields
\[
 \sum_{|\gamma|>T}|\gamma|^{-p}
 \le 10p\,T^{1-p}
 \left(\frac{\log(10T)}{p-1}+\frac1{(p-1)^2}\right),\quad p>1.
\]
Multiply by \((q/a)^{2q}e^{a+t/2}\), with \(p=2q\), to obtain (6). This controls **every** omitted zero. It also justifies absolute convergence and the translations in (1).

## Proof of the packet inequality

For the \(m\) translations \(t_\ell=(M+\ell)h_0\), write
\[
 K(t_\ell)=\sum_{j=1}^m w_j\zeta_j^M\zeta_j^\ell+E_\ell.
\]
The tail proof gives \(|E_\ell|\le\mathcal T(a,q,T,t_*)\). Invert \(V\) and use (3):
\[
 |w_j|\,|\zeta_j|^M
 \le R_j[Q+\mathcal T(a,q,T,t_*)].
\]
Taking logarithms proves (5). This is elementary finite power-sum interpolation, closely related to the interpolation step in Turán's method. It is not a claimed new form of Turán's theorem.

## What this resolves and what it leaves open

This theorem makes the support cost, multiplicities, cancellation constant and infinite tail explicit. Completeness of a supplied packet requires an argument-principle count or another valid zero-counting certificate. The calculator does not infer completeness from a list of numerical roots.

The numerator in (5) still depends on the **whole packet**, through \(R_j\), \(Q\), and the choice of \(T,a,q,h_0,M\). Near collisions or sampling aliases make interpolation ill-conditioned. The tail grows with translation; choosing a large window alone need not make the bound useful. Thus replacing the numerator by a function only of the selected ordinate \(\gamma_j\), uniformly as the possible horizontal displacement tends to zero, is a substantive unsolved step.

The requested \(\beta\le\tfrac12+\Phi(\gamma)/\log C\) does not follow merely by renaming this numerator \(\Phi\). D3 has a proved packet-dependent theorem and a checked calculator; the universal calibrated region remains open. No novelty claim is made without a further dedicated comparison with quantitative Weil-criterion literature.
