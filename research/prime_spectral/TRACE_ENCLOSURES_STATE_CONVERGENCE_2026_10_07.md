# Trace enclosures and convergence of the two actual minimizing states

Date: 7 October 2026. Status: written analytic arguments plus reproducible
Arb certificates and five Lean scalar theorems. The operator arguments
require independent mathematical review and are not formalized in Lean.
This supplies quantitative obligations for the two-state prime-entry
argument, including full-operator simplicity certificates at thresholds
2 and 3. It does not increase the certified positivity window, establish
novelty, or prove RH.

This continues [the renewal trace argument](RENEWAL_ENDPOINT_TRACE_2026_10_07.md)
and [the comparison-semigroup argument](BOUNDARY_REGULARITY_PRIME_ACTIVATION_2026_10_07.md).
All operators below retain both pole terms, both parity sectors, and
every active prime power. The minimizing states are infinite-dimensional
minimizers of the full form.

## 1. Explicit renewal-mass enclosures

Use exactly the normalization

\[
 b(\xi)=\tfrac12\log(1+\xi^2),\qquad
 J(\lambda)=\int_0^\infty e^{-\lambda y}\,dV(y)=1/\kappa(\lambda).
\]

The density \(v=V'\) is positive and decreasing; \(V(0)=0\) and \(V\) is
concave. These are fluctuation-theory inputs from
[Grzywny–Ryznar, Proposition 3.2 and Lemma 4.3](https://arxiv.org/pdf/1107.0745).
The renewal function here is \(\sqrt2\) times that for their exponent
\(\log(1+\xi^2)\).

For \(\ell=\log\lambda\), put

\[
 f(t)=\log[\tfrac12\log(1+e^{2t})],\qquad
 \log\kappa(e^\ell)=\int_\mathbb R\frac{f(\ell+z)}{2\pi\cosh z}\,dz.
 \tag{1}
\]

The elementary estimate \(|f(t)|\le2|t|+2\) gives the whole-tail bound

\[
 \left|\int_{|z|>R}\frac{f(\ell+z)}{2\pi\cosh z}\,dz\right|
 \le \frac4\pi(|\ell|+R+2)e^{-R}.                         \tag{2}
\]

For \(t\le0\), sandwich \(\log(1+e^{2t})\) between \(e^{2t}/2\)
and \(e^{2t}\). For \(t\ge0\), use \(t\le\log(1+e^{2t})/2
\le t+\log2/2\), treating \(0\le t\le1\) separately. These inequalities
prove the displayed bound on \(f\). Integrating
\((|\ell|+|z|+1)e^{-|z|}\) on the two tails proves (2).

The code integrates over \([-128,128]\) with complex-ball adaptive
quadrature and adds (2) before exponentiating. Near very negative \(t\)
it evaluates

\[
 f(t)=2t-\log2+
 \log\bigl({}_2F_1(1,1;2;-e^{2t})\bigr),
\]

using \({}_2F_1(1,1;2;-w)=\log(1+w)/w\). This avoids subtracting numbers
at the scale of machine precision. All logarithms enforce the analytic
branch checks requested by Arb; unresolved integrals fail closed.

There is no numerical inverse Laplace transform. Integration by parts
identifies \(J(\lambda)=\mathbb E V(Y)\) for an exponential variable of
mean \(1/\lambda\). Jensen's inequality and concavity therefore give

\[
 J(1/d)\le V(d),\qquad
 V(d)\le \frac{hJ(h/d)}{1-e^{-h}}\quad(h>0).              \tag{3}
\]

For the upper bound use \(V(y)\ge\min(y/d,1)V(d)\) and integrate that
piecewise linear lower bound. A second valid lower bound is

\[
 J(h/d)-e^{-h/2}J(h/(2d))\le V(d).                      \tag{4}
\]

Indeed, the Laplace–Stieltjes integral over \(y>d\) is at most
\(e^{-h/2}J(h/(2d))\), and the integral over \(y\le d\) is at most \(V(d)\).
Maximizing valid lower bounds and minimizing valid upper bounds is
legitimate interval arithmetic, not an assumption about optimality.
Decreasing \(v\) also gives \(v(d)\le V(d)/d\).

The saved exact rational endpoints in
[the enclosure output](renewal_trace_enclosures_2026_10_07.json) imply
these deliberately widened decimal intervals:

| \(d\) | Enclosure of \(V(d)\) |
|---|---|
| \(1\) | \([2.18496,\ 3.32492]\) |
| \(e^{-8}\) | \([0.35750,\ 0.44725]\) |
| \(e^{-32}\) | \([0.17688,\ 0.19051]\) |
| \(e^{-128}\) | \([0.08839,\ 0.09068]\) |

These are bounds on the normalized renewal function, not on the
eigenfunction itself. Their width includes the Laplace inequalities;
the quadrature radius alone is not the error of \(V\).

## 2. Enclosing the actual endpoint traces

For either actual normalized minimizing state \(u\), localize its left
endpoint with
\(\chi(y)=1\) for \(y\le r\), \(\chi(y)=(2r-y)/r\) for \(r<y<2r\),
and \(\chi(y)=0\) for \(y\ge2r\). Lipschitz cutoffs suffice for the
commutator/form-domain proof in the preceding note; smoothness is not
required. The right endpoint is handled by reflection.

Writing \(A_L=B_{(0,L)}-c+K-S\), \(c=\log(2\pi)\), one has

\[
 F=\chi[(\lambda+c)u-Ku+Su]+[B,\chi]u,\qquad
 \tau=\int_0^\infty v(y)F(y)\,dy,
\]
\[
 \left|u(d)/V(d)-\tau\right|\le2M_FV(d)\quad(0<d\le r),
 \qquad M_F\ge\|F\|_\infty.                            \tag{5}
\]

Here \(B\) is the whole-line Lévy operator and the function \(u\) is
extended by zero. The preceding note proves the Green identification
at spectral parameter zero; no inverse bounded on all of \(L^2(H)\)
is being assumed.

If a certified enclosure of the **actual** profile is \(u(d)\in[p,q]\)
and (3)–(4) give \(V(d)\in[a,b]\), \(a>0\), then

\[
 \tau\in
 \left[\min\{p/a,p/b,q/a,q/b\}-2M_Fb,\
       \max\{p/a,p/b,q/a,q/b\}+2M_Fb\right].             \tag{6}
\]

This handles either sign. For complex states apply it to real and
imaginary parts after choosing phases. The function
\(\texttt{conditional_trace}\) implements (6); it does not certify its
profile input. Substituting a trial Fourier profile is not a certificate
of an actual trace. In particular a finite cosine trial generally has
nonzero ordinary endpoint values and need not obey (5).

There are unconditional, although coarse, enclosures from the analytic
bounds already available. On \(2/3\le L\le6/5\), which includes both
thresholds, set

\[
 k_*=\tfrac54+2\cosh(3/5),\quad k=(6/5)k_*,\quad
 m=2(\log2/\sqrt2+\log3/\sqrt3).
\]

They bound \(K\) and \(S\) for both the full and prime-omitted operators.
The normalized constant function belongs to the form domain and has

\[
 \langle B_Lu,u\rangle=(1-e^{-L})/L+E_1(L)
 \le1+e^{-2/3}/(2/3).
\]

Its prime contribution \(-\langle Su,u\rangle\) is nonpositive. Thus
\(\lambda\le U=1+e^{-2/3}/(2/3)-c+k\); also
\(\lambda\ge-c-k-m\).
The semigroup bound from the preceding note gives, for every \(t>1/2\),

\[
 \|u\|_\infty\le
 e^{(U+c+k+m)t}\left[
 \sqrt{\frac{\Gamma(t-1/2)}{2\sqrt\pi\,\Gamma(t)}}+
 t\sqrt{6/5}\,k_*\right].                              \tag{7}
\]

Choosing \(t=13/25\) and \(r=1/8\), the Arb output proves

\[
 \|u\|_\infty<3651,\quad
 \|F\|_\infty<77337,\quad
 \|F\|_1<96839,\quad |\tau|<579119.                    \tag{8}
\]

Specifically,
\(M_F=[\max(k+m,U+c)+k+m+8]M_u\).
For \(y\ge2r+1=5/4\),
\(|F(y)|\le D e^{-y}\), \(D=M_ur e^{2r}\), so
\(\|F\|_1\le(5/4)M_F+M_u/(8e)\).
Finally \(|\tau|\le V(1)M_F+v(1)\|F\|_1
\le V(1)(M_F+\|F\|_1)\), which proves (8).
Consequently each of the two real states has both endpoint traces in
\([-579119,579119]\). This is an actual universal enclosure, conditional
on the written operator/renewal inputs. It is not a useful estimate of
the trace's sign, nonvanishing, or numerical leading coefficient.

## 3. A quantitative continuity modulus for the traces

Ordinary \(L^2\) convergence by itself does not control this trace.
The singular density \(v\) need not belong to \(L^2\) near zero.
The uniform forcing and tail bounds above supply the missing control.

Suppose \(F,G\) satisfy \(\|F\|_\infty,\|G\|_\infty\le M\) and
\(|F(y)|,|G(y)|\le De^{-y}\) for \(y\ge R_0\). Put
\(e=\|F-G\|_2\). For \(0<\epsilon<R\), \(R\ge R_0\), split the trace
integral into \((0,\epsilon),(\epsilon,R),(R,\infty)\). Monotonicity
of \(v\) and Cauchy–Schwarz prove the explicit bound

\[
 \boxed{\quad|\tau(F)-\tau(G)|
 \le2M V(\epsilon)+
 e\sqrt{v(\epsilon)[V(R)-V(\epsilon)]}+
 2Dv(R)e^{-R}.\quad}                                  \tag{9}
\]

Every term can be bounded by the renewal enclosures:
\(v(\epsilon)\le V(\epsilon)/\epsilon\), \(v(R)\le V(R)/R\).
For example, if \(0<e<\exp[-\max(1,R_0)]\), take
\(\epsilon=e\), \(R=\log(1/e)\). Concavity implies
\(V(R)\le RV(1)\) for \(R\ge1\), and (9) becomes

\[
 |\tau(F)-\tau(G)|\le
 2M V(e)+\sqrt{eV(e)V(1)\log(1/e)}+2DV(1)e.            \tag{10}
\]

All terms tend to zero. The leading universal modulus is slow,
of order \(1/\sqrt{\log(1/e)}\); an \(L^2\) eigenvector error cannot
be reported as the same numerical trace error.

## 4. Common-domain convergence across a prime threshold

Let \(L_0=\log q\), \(L\downarrow L_0\), and let \(A_L^0\) omit just the
new \(q\)-term, whereas \(A_L^1=A_L^0+V_{q,L}\) retains it. Work in the
fixed space \(L^2(J)\), \(J=(-1/2,1/2)\), using
\((U_Lu)(x)=\sqrt L\,u(Lx)\).

The exterior-Dirichlet comparison form then has whole-line symbol
\(b_L(\xi)=\log[1+(\xi/L)^2]/2\). Direct differentiation gives

\[
 \|B_L-B_{L_0}\|\le|\log(L/L_0)|.                      \tag{11}
\]

More precisely the difference of forms is represented by compression
of that bounded multiplier. Thus their form domains coincide, and
their operator realizations differ by that bounded operator and have
the same operator domain. No moving-domain elliptic regularity is
inserted at this step.

The transformed \(K\) kernel is \(Lk(L(x-y))\).
Its removable value at zero is continuous, so Schur's bound proves
operator-norm continuity in \(L\) on a compact length interval.
Each supported translation in \(S_L\) is a compression of a whole-line
translation through \((\log n)/L\). Whole-line translations are strongly
continuous and uniformly bounded on \(L^2\). At \(L=L_0\), the
\(q\)-translation is through exactly one interval length, so its
compression vanishes almost everywhere. Both operator families therefore
have the representation

\[
 A_L^i=B_{L_0}+E_L^i,\qquad
 \sup_{L,i}\|E_L^i\|<\infty,\qquad
 E_L^i\longrightarrow E_{L_0}\ \hbox{strongly}.         \tag{12}
\]

This is strong, not operator-norm, convergence of the new prime term:
its action on arbitrary unit vectors in a shrinking layer need not be
small. The other prime powers remain fixed in a sufficiently small
one-sided cell.

The comparison operator has compact resolvent. Indeed, bounded form
energy and support in the fixed bounded interval give

\[
 \int_{|\xi|>T}|\widehat f(\xi)|^2\,d\xi
 \le \frac{\langle B_{L_0}f,f\rangle}{b_{L_0}(T)}
 \longrightarrow0
\]

uniformly on a form-bounded set. Together with tight support, the
Fourier compactness criterion proves the compact form embedding.
Bounded perturbations preserve compact resolvent.

Choose \(\mu>0\) so large that all \(A_L^i+\mu\ge1\), and write
\(R_L^i=(A_L^i+\mu)^{-1}\). Resolvent identities give

\[
 R_L^i-R_{L_0}=-R_L^i(E_L^i-E_{L_0})R_{L_0}
 \longrightarrow0\quad\hbox{in operator norm}.         \tag{13}
\]

For completeness, uniformly bounded strong convergence becomes norm
convergence after multiplication by a compact operator: approximate
\(R_{L_0}\) in norm by a finite-rank map; strong convergence is uniform
on the unit ball of its finite-dimensional range; the remaining
operator-norm error is uniformly bounded. Also \(\|R_L^i\|\le1\).
This proves (13) without a small norm for the prime translation.

Consequently the lowest eigenvalues converge and the spectral
projections onto an isolated limiting ground cluster converge in norm.
If the limiting ground space is multiple, each minimizing state
approaches that space; there need not be a common limiting vector.
If it is one-dimensional, choose phases so that each inner product
with its normalized generator \(u_*\) is nonnegative. Then

\[
 U_Lu_L^0\longrightarrow U_{L_0}u_*,
 \qquad U_Lu_L^1\longrightarrow U_{L_0}u_*
 \quad\hbox{strongly in }L^2(J).                       \tag{14}
\]

The physical zero extensions converge too, by strong continuity of
dilations on \(L^2\). The eigenvalues converge; \(K\) and each
physical supported translation are bounded and strongly continuous
in the corresponding embedding. Hence the localized forcings in (5)
converge in \(L^2(H)\). The fixed-cutoff commutator is bounded on
\(L^2\), by \(\int |z|\nu(z)\,dz=1\). Reflection gives the same conclusion
at the right endpoint. Applying (9) with uniform (8) and uniform tails
proves convergence of **both traces of both states**.

Continuity of the lowest Weil eigenvalue is already prior art:
[Suzuki, Theorem 1.3 and Section 4.4](https://arxiv.org/html/2606.09096v2).
That paper's Theorem 1.4 gives simplicity for sufficiently small support.
The common-domain argument and elementary spectral perturbation reasoning
above do not warrant a novelty claim. The specific trace conclusions and
certified threshold hypotheses need their own comparison with prior work.

## 5. Certifying simplicity at 2 and 3 for the full operator

The following is one full-operator min–max calculation at each threshold,
not a scan of fixed-order positivity minors. It uses the entire analytic
infinite-complement estimate already implemented by
\(\texttt{compact_window_certificate.py}\).

On a slightly larger comparison interval, its lower operator \(R\)
satisfies \(A\ge R\). If \(P\) is the Legendre projection, \(G\) the
quadrature matrix, \(\varepsilon\) its operator error, and \(B,D\) the
recorded coupling and complement-deviation bounds, then

\[
 R\ge (G-\varepsilon I)\oplus\beta I-(B+D)I.            \tag{15}
\]

To see this, the finite block differs from \(G\) by at most
\(\varepsilon\), the complement is at least \(\beta-D\), and the
off-diagonal quadratic form is bounded below by
\(-2B\|Pf\|\|(1-P)f\|\ge-B\|f\|^2\).
Spending \(D\) on the whole space only weakens the bound.
Both parity sectors are retained.

If interval LDL certifies exactly one negative eigenvalue of
\(G-(\eta+\varepsilon)I\), and \(\beta>\eta\), the second min–max
value of (15) is at least \(\eta-B-D\). Support inclusion, by zero
extension, then gives

\[
 \lambda_2(A_{\log q})\ge
 \lambda_2(A_{\text{larger interval}})\ge\eta-B-D.      \tag{16}
\]

For \(\lambda_1\), any exact rational finite cosine trial is admissible
and its full geometric-side Rayleigh quotient gives an upper bound.
Floating eigenvectors choose the rational coefficients; Arb evaluates
the quotient anew. No claim is made that the trial vector encloses a
true eigenvector. The constant cosine basis vector has norm one;
the factor two in the symmetric correlation is not a second norm factor.

The saved [gap witnesses](verification_2026_10_07_trace_stability/threshold_ground_gaps.json)
give:

| Threshold | Larger interval length | \(\eta\) | \(\lambda_1\) upper, widened | \(\lambda_2\) lower, widened | Ground gap, weakened |
|---|---|---|---|---|---|
| \(q=2\) | \(7/10\) | \(1/100\) | \(0.00142\) | \(0.00999\) | \(0.00857\) |
| \(q=3\) | \(6/5\) | \(11/10^8\) | \(1.03\cdot10^{-7}\) | \(1.09\cdot10^{-7}\) | \(6\cdot10^{-9}\) |

Unrounded gap bounds exceed \(0.00858095\) and \(7.43985\cdot10^{-9}\),
respectively. At each shift the even finite block has one negative
eigenvalue and the odd finite block has none. Equation (15) therefore
also places the whole odd sector above the ground trial bound. Each
threshold ground space is one-dimensional and even. A generator can be
chosen real. This uses no positivity-preserving property of the Weil
semigroup and no assumption that the ground eigenvalue is positive.

The prime-two lower operator uses 80 Legendre modes, cutoff 64 and
order-64 Gauss quadrature. The prime-three bound reuses the saved
160-mode, order-80 comparison at \(L=6/5\). Both input lower-operator
certificates are checked by their verifier, including independent
adaptive integrals of four low entries and geometric normalization.
The infinite-complement inequalities are still written analytic inputs;
these numerical checks do not formalize or independently review them.

## 6. Quantitative two-state distance and the common coefficient

Let \(u_0,u_1\) minimize \(Q_0,Q_0+V_q\) on the same interval and have
ground energies \(\lambda_0,\lambda_1\). The exact variational bracket is

\[
 \lambda_0+V_q[u_1]\le\lambda_1
       \le\lambda_0+V_q[u_0].                         \tag{17}
\]

If \(Q_0\) has simple ground state with gap \(\gamma>0\), expansion in
its spectral decomposition proves

\[
 \gamma\,d_{\rm ph}(u_0,f)^2
 \le2(Q_0[f]-\lambda_0),\qquad
 d_{\rm ph}(u_0,f)^2=2-2|\langle u_0,f\rangle|.
\]

Indeed \(1-|\langle u_0,f\rangle|
\le1-|\langle u_0,f\rangle|^2\).
If \(|V_q[u_i]|\le\eta\) for both actual minimizing states, (17) implies

\[
 \boxed{\quad d_{\rm ph}(u_0,u_1)^2\le4\eta/\gamma.\quad} \tag{18}
\]

The earlier uniform boundary bound gives, for
\(\delta=L-\log q\downarrow0\),
\(\eta\le2w_q K_b^2\delta/\log(1/\delta)\), for a common explicit
boundary constant \(K_b\) and sufficiently small \(\delta\). Therefore

\[
 d_{\rm ph}(u_0,u_1)\le
 \sqrt{\frac{8w_qK_b^2}{\gamma}
                 \frac{\delta}{\log(1/\delta)}}.       \tag{19}
\]

More generally \(\eta/\gamma\to0\) suffices; a fixed gap is not required.
At thresholds 2 and 3, (13) and the certified threshold gaps imply a
uniform positive gap on some one-sided neighborhood. No numerical
radius for that neighborhood is claimed.

One can make the same-interval forcing comparison explicit too. Equations
(5),(8) and \(V(r)\le V(1)<3.32492\) give the uniform, deliberately
coarse bound

\[
 |u(t)|,\ |u(L-t)|\le K_V V(t)\quad(0<t\le1/8),
 \qquad K_V=1100000.
\]

In fact \(579119+2(77337)(3.32492)<K_V\).
For \(0<\delta\le1/8\) put
\(\eta_\delta=2w_qK_V^2\delta V(\delta)^2\). Both statewise prime
quadratic forms have magnitude at most \(\eta_\delta\). The newly active
translation and its adjoint send the state to disjoint endpoint layers,
since \(\delta<L/2\), so

\[
 \|S_qu_1\|_2\le\sqrt2\,w_qK_V\sqrt\delta\,V(\delta).
\]

Choose the relative phase to realize \(d=d_{\rm ph}(u_0,u_1)\).
Subtracting the two localized equations (5), and using the commutator's
\(L^2\) norm bound 8, gives at either endpoint

\[
 \boxed{\quad e_\delta:=\|F_1-F_0\|_2
 \le22d+\eta_\delta+
            \sqrt2\,w_qK_V\sqrt\delta\,V(\delta),\qquad
 d^2\le4\eta_\delta/\gamma.\quad}                       \tag{19a}
\]

Here \(22\) exceeds
\(\max(k+m,U+c)+k+m+8\). The extra eigenvalue-difference term is bounded
by \(\eta_\delta\), by (17). This derivation compares the actual states
and their actual forcings on the same interval; it does not estimate a
trace from a trial vector. Substitution of (19a) into (9) gives a fully
explicit trace-difference enclosure once a gap bound at the chosen
length is supplied. For a uniformly positive gap,
\(e_\delta=O(\sqrt{\delta/\log(1/\delta)})\); equation (10) then yields
the coarse trace-difference rate \(O(1/\sqrt{\log(1/\delta)})\).

For those two thresholds, (14) and (9) now give the missing common
endpoint product:

\[
 \overline{\tau_-(u_L^i)}\tau_+(u_L^i)
 \longrightarrow
 \overline{\tau_-(u_*)}\tau_+(u_*),\qquad i=0,1.         \tag{20}
\]

The exact newly activated correlation has the form

\[
 g_u(\log q)=\int_0^\delta\overline{u(t)}u(L-\delta+t)\,dt.
\]

Using (5), with \(a_\delta=2M_FV(\delta)\),
\(W_\delta=\int_0^\delta V(t)V(\delta-t)\,dt\), gives the explicit error

\[
 \left|g_u(\log q)-\overline{\tau_-(u)}\tau_+(u)W_\delta\right|
 \le[a_\delta(|\tau_-|+|\tau_+|)+a_\delta^2]W_\delta.   \tag{21}
\]

Since \(W_\delta\sim\delta/\log(1/\delta)\), equations (17),(20),(21)
yield, for \(q=2,3\),

\[
 \lambda_1(L)-\lambda_0(L)=
 -2w_q\operatorname{Re}(\overline{\tau_-(u_*)}\tau_+(u_*))
       \frac{\delta}{\log(1/\delta)}
 +o\!\left(\frac{\delta}{\log(1/\delta)}\right).         \tag{22}
\]

The real even threshold state has \(\tau_-=\tau_+\), so the coefficient
is \(-2w_q\tau_*^2\le0\). Neither nonvanishing of \(\tau_*\) nor its
useful numerical enclosure is proved here. If it vanishes, (22) remains
valid with zero leading coefficient. There is also no all-scale
margin budget or exclusion of zero crossings between prime thresholds.

## 7. Formal and computational boundary

[WeilTraceStability.lean](../../Reinmann/WeilTraceStability.lean) proves
five scalar results: propagation of a trace interval, the two-state
squared-distance bound, convergence when error/gap tends to zero, and
two weakened rational threshold-gap deductions. The full-space gap
coercivity and spectral enclosures are named hypothesis predicates.
There are no global axioms asserting the analytic theorem.

The target module and its audit build. All five audited declarations use
only \(\texttt{propext}\), \(\texttt{Classical.choice}\),
\(\texttt{Quot.sound}\). This does not certify the operator analysis,
renewal quadrature, or mathematical novelty.

Reproduction:

~~~sh
uv run --with python-flint==0.8.0 --python 3.12 python \
  experiments/prime_spectral/renewal_trace_enclosures.py \
  --output research/prime_spectral/renewal_trace_enclosures_2026_10_07.json
uv run --with python-flint==0.8.0 --with mpmath==1.3.0 --python 3.12 python \
  experiments/prime_spectral/threshold_ground_gap.py \
  --output-dir research/prime_spectral/verification_2026_10_07_trace_stability
uv run --with python-flint==0.8.0 --with mpmath==1.3.0 --python 3.12 python \
  -m unittest discover -s experiments/prime_spectral -p test_trace_stability.py -v
lake build Reinmann.WeilTraceStability Reinmann.WeilTraceStabilityAudit
~~~

The verification directory retains independent lower-operator checks,
gap witnesses, test/build logs, and a manifest. Tight actual profile
enclosures, a reviewed analytic proof, and a dedicated priority check
remain necessary before a publication claim about the threshold formula.
