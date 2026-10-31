# The two proposed closure inputs (1 November 2026)

**Outcome:** Xu–Sang's supplied remainder majorant does not give absolute
decay below C_b(1/2). More decisively, the printed principal correction
contains a shifted **angular Hecke L-function**, so it is holomorphic but
has zeros on Re(s)>1/2. Global nonvanishing of that same correction cannot
supply the missing forward implication. The concrete obligations are an
endpoint-compatible remainder estimate and exclusion of cancellation
between target reciprocal poles and the angular factor's zeros.

This is a source-interface audit, conditional on the printed probe/local
identities and using standard Hecke analytic theory. Exact algebra and
inequalities are machine checked; analytic continuation and Hecke zero
existence are mathematical inputs explained below, not software-certified
theorems. No target L-zero or common zero is located; no new arithmetic
estimate, GRH implication for J_eta, novelty or whole-method impossibility
claim follows. The actual probe stays uninstantiated under the DH gate.

## Sources and preregistration

The DH register was updated before calculation. The new packet preserves
that entry, the preceding register/review bytes, and every earlier
non-cache verification-file hash.

- [Xu–Sang 2610.15291v2](https://arxiv.org/html/2610.15291v2): Section 6.6,
  especially the final choice gamma=(1/100)min{Delta,g_*,l_y/20,h/600,mu}
  and rho=2gamma; Proposition 6.1 and Appendix C.4; Section 8 closure.
- [OpenAI, pinned source](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex):
  alpha(a)=a/|a| at line 575; local parameters at 3859–3869; complete
  local identity at 4013–4039; principal correction at 5520. The fetched
  source blob is `268c4e3206d460c617d3d2129742a72b831b3def`.
  Numbered excerpts are preserved in the packet.
- [Liu 2610.26835v2](https://arxiv.org/html/2610.26835v2), Section 13.3:
  the same j=0 local table and principal correction, with Lambda replacing
  alpha in its cyclotomic extension. Its coefficient-character lemma
  explicitly retains the nonzero angular type. The algebra below is
  checked against the original OpenAI table, not just Liu's transcription.

The archived arXiv versions retain the fingerprints in the earlier source
provenance. The present audit does not replay the complete theta identity,
the global proof or any Lean build. All later conclusions are scoped to
this printed correction and normalization.

## 1. The remainder bound supplied by Section 6

Write B=B(ell), Delta=beta_*-B>0. The construction gives

\[
\rho=\frac1{50}\min\{\Delta,g_*,l_y/20,h/600,\mu\}
\le\Delta/50,
\qquad R_\eta\ll Z^{C_b(\beta_*)-\rho}.
\]

Since C_b has slope one, its supplied exponent lies above C_b(1/2) by
at least

\[
\beta_*-\tfrac12-\Delta/50
=B-\tfrac12+\frac{49}{50}(\beta_*-B).
\]

With the retained cap this exceeds 11/30. Thus this **printed upper
majorant** cannot establish
`R_eta << Z^(C_b(1/2)-delta0)` for delta0>0. This is not a lower bound on
the actual R_eta and does not disprove a stronger estimate for it.

The theorem also assumes beta_*>B(ell)>87/100 and its other admissibility
conditions. Changing only a claimed exponent for J does not extend those
hypotheses to every beta_*>1/2.

This is not merely a conservative choice of gamma: Appendix C.4's
principal-remainder majorant contains a branch with exponent
`C_b(beta_*)-h/600` even after all positive losses are optimistically
suppressed. Source support gives h=1-l_x+ell<1. With beta_*>87/100,
this branch remains above C_b(1/2) by more than **221/600**. The printed
sum of majorants therefore needs further analysis to imply absolute
endpoint decay; merely enlarging the final reserved margin does not do it.

### The sufficient remainder condition can be weaker

The proposed absolute decay would suffice, but the original supremum
argument only needs, under beta_*>1/2, a fixed probe and some rho>0
uniform over all target characters such that

\[
R_\eta\ll_\eta Z^{C_b(\beta_*)-\rho}.
\]

Combine it with the hypothetical direct estimate at C_b(1/2)+epsilon,
choosing epsilon<(beta_*-1/2)/2. Then f_eta=J_eta-R_eta has a common
positive exponent saving below C_b(beta_*). Mellin continuation would
contradict the supremum **if** the correction cannot cancel the target
poles in that newly reached strip. Constants/onsets may depend on eta;
the displacement must be common to the family. A relative rho may depend
on beta_*. Its being smaller than beta_*-1/2 is not itself an obstacle to
that supremum argument. The missing result is applicability throughout the
needed endpoint range, not necessarily an absolute negative remainder.

## 2. Exact specialization of the principal correction

Use q=N(p), T=q^(-s), eta_p=eta(p), and
`psi_p=conjugate(alpha(p))^6*eta(p)^6`. The principal row has j=0,rho=1;
at w=1,z=1/6, Y=V=1/q and R=psi_p*q^3*T^6. The original table gives

\[
P^*=\frac1{1-R}\left\{
\frac{R(1-q^{-1})-\eta_p(q-1)TYV}{1-V}
-\eta_pT+YR\right\},
\]

\[
P_0=(1-V)^{-1}+Y/(1-Y)+P^*,\qquad
H_p=\frac{(1-V)(1-Y)P_0}{1-\eta_pT}.
\]

Symbolic simplification gives

\[
H_p=(1-q^{-2})\,
\frac{1-(1-q^{-1})\eta_pT-\psi_pq^2T^6}
{(1-\eta_pT)(1-\psi_pq^3T^6)}
=\frac{(1-q^{-2})E_p(s)}{1-\psi_pq^{3-6s}},
\]

\[
E_p(s)=1+
\frac{\eta_pq^{-s-1}-\psi_pq^{2-6s}}{1-\eta_pq^{-s}}.
\]

Every target-character power is retained. In particular psi is not
silently replaced by 1 or by a finite-order character.

### The remaining product is holomorphic and nonzero

For sigma=Re(s)>1/2 and q>=9,

\[
|E_p-1|\le
\frac{q^{-\sigma-1}+q^{2-6\sigma}}{1-q^{-\sigma}}
\le\frac{q^{-3/2}+q^{-1}}{1-q^{-1/2}}\le\frac29<1.
\]

On a compact sub-half-plane sigma>=1/2+epsilon, the numerator terms
decay as q^(-3/2-epsilon) and q^(-1-6epsilon). Their sums over prime
ideals converge, so `E_eta=product_(p notin S) E_p` converges normally
and has no zeros. The fixed source cutoff can include every q<9.
The constant product `product(1-q^-2)=zeta_F^S(2)^(-1)` is nonzero.

Consequently, initially on Re(s)>2/3 and then by continuation,

\[
\boxed{G_\eta(s)=\zeta_F^S(2)^{-1}
 L_F^S(6s-3,\psi_\eta)E_\eta(s),\qquad
 \psi_\eta=\overline\alpha^{\,6}\eta^6.}
\]

This is the principal-residue slice, not an extension of all the joint
(s,w,z) contour regions or the principal-remainder estimates.

## 3. What the angular factor implies

For the Eisenstein field alpha(a)=a/|a|. Its sixth power is independent
of the choice of generator, since all units have sixth power 1. Because
eta has finite order, psi_eta has nonzero angular degree -6 (up to the
embedding convention); it is a genuine infinite-order unitary Hecke
character. In Liu's extension the analogous nonzero angular components
are retained at the infinite places.

Standard Hecke theory gives an entire primitive L(s,psi_eta), with
completed function of order one, functional equation, Euler product and
the appropriate Gamma factor. In the quadratic field the Gamma factor
is Gamma(s+3), up to the conductor normalization. These are analytic
inputs here, not new arithmetic theorems or assertions checked by SymPy.

For completeness, these standard properties force infinitely many
completed zeros: if there were only finitely many, Hadamard factorization
would give `completed_L(s)=exp(A+Bs)P(s)`. Along large positive real x,
L(x) tends to 1 and Stirling gives `log|completed_L(x)|=x log x+O(x)`,
contradicting the linear-plus-logarithmic growth of that factorization.
The functional equation and conjugation pair zeros of this same unitary
L-function by rho -> 1-conjugate(rho); the Euler product excludes zeros
to the right of 1. The standard nonvanishing on Re(s)=1 makes the
upper endpoint strict (the argument is recalled below). Thus there are
nontrivial zeros with `1/2 <= Re(rho) < 1` and nonzero sufficiently large height. They are
zeros of L rather than Gamma poles. Removing finitely many Euler factors
does not remove them: those finite factors have zeros only on Re(rho)=0.

Each such zero gives a zero of G_eta at

\[
s=(\rho+3)/6,\qquad 7/12\le\Re(s)<2/3.
\]

E_eta is nonzero there. Under angular GRH the zeros would lie exactly on
Re(s)=7/12, which is still strictly to the right of 1/2. Hence **the same
printed G_eta cannot be nonvanishing on the whole half-plane Re(s)>1/2**.
It does extend holomorphically there; it is nonzero on Re(s)>=2/3. This
is consistent with its published nonvanishing region above 87/100.
No angular zero is numerically located or certified in this audit.

## 4. The concrete second obligation

Mellin continuation concerns `G_eta(s)/L_F^S(s,eta)`. Its holomorphy
does not exclude a zero of the denominator canceled by a zero of G_eta.
The now explicit sufficient noncancellation condition is, for example,

\[
L_F^S(s,\eta)=0\quad\Longrightarrow\quad
L_F^S(6s-3,\overline\alpha^{\,6}\eta^6)\ne0
\quad(\Re(s)>1/2).
\]

This condition is **not proved**. Distinct infinity types or Euler
multiplicativity do not prove absence of common zeros. A more economical
argument could use a sufficient multiplicity comparison or exclude
cancellation only for zeros approaching the family supremum. Alternatively
one could change the correction/probe, with a newly justified identity,
direct bound and remainder. None of these is implemented as an arithmetic
strategy here, and no DH metaplectic probe exists for them.

### The explicit 2/3 threshold and the supremum boundary

For every correction zero with Re(s)>1/2, the shifted angular argument
u=6s-3 has Re(u)>0. The angular Hecke L-function has no zeros for
Re(u)>=1, so the possible cancellation region is exactly confined to

\[
1/2<\Re(s)<2/3.
\]

Here “confined” is a restriction on possible locations, not a claim that
every point in this strip is a correction zero or a common zero.
The correction cannot cancel target poles on or to the right of 2/3.
This leaves the published range above 87/100 unaffected. An attempted
extension excluding target zeros strictly to the right of 2/3 has direct
and remainder obligations but no additional correction-cancellation
obligation. This principal-slice statement does not supply the missing
joint-contour estimates.

The classical boundary nonvanishing used here follows particularly simply
for the nonzero angular character psi. Its square has nonzero angular
degree too, so neither L(s,psi) nor L(s,psi^2) has a pole. The Euler-product
inequality, from `3+4*cos(theta)+cos(2*theta)=2*(1+cos(theta))^2>=0`, is

\[
\zeta_F^S(\sigma)^3
 |L_F^S(\sigma+it,\psi)|^4
 |L_F^S(\sigma+2it,\psi^2)|\ge1\qquad(\sigma>1).
\]

A zero of L(1+it,psi) of order m>=1 would make the left side tend to
zero like at least (sigma-1)^(4m-3), since zeta has a simple pole and
the squared-character factor is bounded. This contradicts the inequality.
Finite deleted factors have no zeros on Re(u)=1. The argument uses
standard Hecke continuation and the Dedekind-zeta pole, with no GRH input.

The family supremum needs one qualification:

- **beta_*>2/3:** choose a strip near beta_* wholly above 2/3. Correction
  zeros cannot cancel any target poles there.
- **beta_*=2/3:** pointwise nonvanishing on the line does not supply a
  uniform zero-free strip below it across all heights and characters.
  Shifted angular zeros are not known here to stay a fixed distance from
  2/3. Unless the supremum is attained by a target zero on that line,
  near-supremum noncancellation or a uniform angular zero-free gap may
  still be needed. No accumulation at a finite point is being asserted.
- **1/2<beta_*<2/3:** the stated near-supremum coincidence or multiplicity
  obligation remains unproved.

Under **angular GRH**, every relevant correction zero is on Re(s)=7/12.
Actual possible coincidences are then confined to that line. In a
near-supremum argument the remaining boundary case is beta_*=7/12;
suprema strictly above or below that line have a strip near the supremum
avoiding correction zeros. These are conditional location statements,
not an assumption of angular GRH or a proof of target GRH.

The scope is therefore three priced obligations for the audited probe:
the 11/30 direct-side saving at the direct-only optimum, a suitable
family-uniform relative remainder saving down to the endpoint range, and
noncancellation where shifted angular zeros can approach the target
supremum. This is not an exhaustive exclusion of every future method.
The route remains uninstantiated; B and C remain optional strengthening
of the zero-free constant.

Thus both proposed cheap facts fail as available inputs: the first is not
delivered by the source majorant, and the second's global nonvanishing is
false for the printed principal correction. The direct target remains
priced and uninstantiated. This does not prove or refute a GRH implication
for J under additional hypotheses or close every future method family.

## Reproduce and preserve history

```sh
python3 experiments/prime_spectral/liu_closure_interface.py
python3 -m unittest discover -s experiments/prime_spectral -p 'test_liu*.py' -v
python3 experiments/prime_spectral/check_dh_research_gate.py
python3 research/prime_spectral/verification_2026_11_01_closure_interface/validate.py
```

The new source packet binds the formulas, source excerpts, preregistration,
tests and current registers. The preceding direct-endpoint packet is
replayed in a temporary tree using its snapshotted source inputs; that
validator in turn replays the refined packet's historical sources. Shared
register/review evolution is distinguished from changing old evidence.
Earlier manifests are not edited. No commits, CI, external review, Lean
builds, zero searches or stopped scans accompany this audit.
