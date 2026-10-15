# Whole-cluster certification and the D1–D6 program

The immediate target is a separated spectral block of the **full**, prime-defined Weil operator. An individual ground-state error bound that divides by the first internal gap is no longer the main scaling strategy. The implementation is [full_cluster_certificate.py](../../experiments/prime_spectral/full_cluster_certificate.py); its fixed-support results and hashes are in [full_clusters.json](verification_2026_10_12_cluster/full_clusters.json). This is written operator mathematics plus Arb verification, rather than a Lean formalization of the operator.

## Conventions and the proposed count

Here \(C=e^{2a}=\lambda^2\), the additive test-function window is ([-a,a]), and the autocorrelation is supported in ([-2a,2a]). Equivalently the shifted additive interval has length \(\log C\). Thus **multiplicative \(C=3.2\)** means additive test-function support length \(\log(3.2)\), not 3.2. The two problems are substantially different. Following the user's instruction to decide, D5 uses this repository convention.

Write \(A_C\) for the lower-bounded self-adjoint operator associated to the closed geometric Weil form; enumerate its discrete eigenvalues from index zero, with multiplicity. A cluster needs a threshold: define

\[
 N_C(t)=\dim\mathbf1_{(-\infty,t)}(A_C).
\]

The requested staircase

\[
 k(C)=\lfloor 2C-7/4\rfloor+1
\]

is treated as a **rank proposal**. The verifier obtains its counts from interval inertia and min–max, without assuming this formula. A selected rank, a count below a specified threshold, and the number of exponentially small eigenvalues are different assertions. A leading term \(2C\) alone supplies neither the offset nor a definition of “near zero.”

[Connes–Consani, §3](https://ems.press/content/serial-article-files/44477) explains the approximate \(2\lambda^2\) prolate count and its arithmetic near-radical construction. Its even Euclidean prolate functions can produce both inversion parities in the Weil space; that count must not be assigned wholly to the even Weil block. Two linear constraints also enter the arithmetic construction. The paper does not supply the proposed exact staircase as a prime-side counting theorem.

[Karnik–Romberg–Davenport, §3.2 and Corollary 3](https://arxiv.org/html/2006.00427) gives quantitative transition-width information for the concentration operator. These results support a threshold-dependent transition analysis. They do not identify the spectrum of \(A_C\) with the prolate spectrum. No novelty claim is made here.

## D1: the two-sided full-operator block certificate

Let a slightly larger window \(C'\ge C\) have a frequency comparison operator \(R\le A_{C'}\). The existing analytic reduction gives

\[
 R\ge (G-\varepsilon_q I)\oplus\beta I
       -(\varepsilon_B+\varepsilon_D)I.
\]

Here \(G\) is the polynomial quadrature matrix, \(\varepsilon_q\) its operator integration allowance, \(\varepsilon_B\) the coupling allowance, and \(\varepsilon_D\) the infinite-complement deviation. The comparison includes both parities and the entire discarded polynomial space.

Suppose interval LDL proves that \(G-(s+\varepsilon_q)I\) has exactly \(k\) negative eigenvalues, counted across both sectors, and \(s<\beta\). Form min–max, including restriction from the larger support, gives

\[
 \lambda_k(A_C)\ge b:=s-\varepsilon_B-\varepsilon_D.
\tag{1}
\]

Separately integrate the **actual geometric form at the target (C)** on the trigonometric trial space. If its two parity matrices have a total of \(k\) eigenvalues below \(U<b\), their negative spectral subspaces give a \(k\)-dimensional trial space with form less than \(U\). Consequently

\[
 \lambda_{k-1}(A_C)<U<b\le\lambda_k(A_C).
\tag{2}
\]

The implementation additionally matches the upper and lower counts in each parity. Every threshold \(t\in[U,b\)) therefore defines exactly the same rank-\(k\) full spectral projector. The certificate uses no internal eigenvalue gap and no zero data. It also does not deduce positivity of the cluster from the outer separation; that is a separate assertion.

The completed replay gives these conservative public bounds. Ranks count both Weil parities; “outside” is the first level after the indicated block.

| C | Rank | Even / odd | Cluster top < | Outside > | Outer gap > |
|---|---:|---|---:|---:|---:|
| 2 | 3 | 2 / 1 | 0.67 | 0.899 | 0.229 |
| 3 | 5 | 3 / 2 | 0.70 | 0.739 | 0.039 |
| 3.2 | 5 | 3 / 2 | 0.40 | 0.739 | 0.339 |
| 3, alternative | 4 | 2 / 2 | 0.11 | 0.629 | 0.519 |
| 3.2, alternative | 4 | 2 / 2 | 0.025 | 0.299 | 0.274 |

The last two rows are in [alternative_rank_four.json](verification_2026_10_12_cluster/alternative_rank_four.json). In particular the fifth **full** eigenvalue at C=3 is >0.629. The five-dimensional block is separated, but its levels are not all near zero at a threshold of 0.1. This is a certified qualification to the proposed interpretation, not a rejection of cluster certification.

The JSON contains exact outward rational endpoints, shifts, all inertia pivots and source/input hashes. The C=3.2 comparison uses \(a'=72697/125000\), which contains the target support, with frequency cutoff 128, 320 polynomial coefficients, 80-point Gauss panels and 384-bit assembly. Its geometric upper blocks use 16 positive trigonometric modes in each parity and 512-bit Arb integration.

The original independent comparison verifier's 256-bit adaptive calculation did not meet its radius requirement at C=3.2. [cluster_comparison_replay.py](../../experiments/prime_spectral/cluster_comparison_replay.py) retains that requirement, raises independent integration to 512 bits, and records both its own hash and the original verifier hash. The initial unsuccessful replay log is retained as history.

### Stable cluster estimates

Let \(P=\mathbf1_{(-\infty,t)}(A_C)\) for a certified separator. If \(A_C\ge\ell I\), a unit trial \(f\) with \(q_C(f)\le\mu<b\) satisfies

\[
 \|(I-P)f\|^2\le\frac{\mu-\ell}{b-\ell}.
\tag{3}
\]

This follows by splitting the spectral measure into the cluster and its complement. It remains valid when \(\ell<0\). It measures cluster membership, not closeness to a particular ground eigenvector.

For a trial isometry \(V:\mathbb C^k\to D(A_C)\), a Hermitian \(B\le UI\), and **full** residual \(E=A_CV-VB\), one also has

\[
 \|(I-P)V\|_{\rm HS}\le\frac{\|E\|_{\rm HS}}{b-U}.
\tag{4}
\]

To prove this, diagonalize \(B\). For each column, the restriction of \(A_C-B_{jj}\) to \((I-P)H\) has inverse norm at most \(1/(b-U)\); square and sum the column estimates. The operator norm is bounded by this Hilbert–Schmidt norm. Only the **external** separation appears. A compressed residual \(V^*E\) can vanish while \((I-P)V\ne0\), so it cannot replace \(E\).

If \(\Pi=VV^*\) and \(P\) have the same finite rank, the largest-angle projection norm is \(\|P-\Pi\|=\|(I-P)\Pi\|\). With an available bound \(s\) on this norm, every unit \(u\in PH\) obeys

\[
 |\langle u,v\rangle|
 \le\|\Pi v\|+s\|(I-\Pi)v\|.
\tag{5}
\]

This is the block analogue of the previous ground-angle adjoint bound. Scalar evaluation of (4) alone is not a full residual construction.

### An actual four-column full residual at C=3

[full_cluster_residual.py](../../experiments/prime_spectral/full_cluster_residual.py) supplies a construction for the alternative rank-four block. It selects two columns in each parity of the 16-mode geometric Ritz matrices, converts them to exact decimal rationals, checks their Gram matrices, and certifies the compressed Rayleigh upper bound \(U=0.11\). It computes every action coordinate through mode 256 and bounds the entire remaining tail.

For the even columns the exact high-mode identity is

\[
 (A_Cv)_m=\sqrt2 E_v b_m/m
 +\sum_{n=1}^N\frac{2n^2b_mv_n}{m(m^2-n^2)}
 -\sum_{n=1}^N\frac{2n b_nv_n}{m^2-n^2},
 \quad E_v=v_0+\sqrt2\sum_{n=1}^N v_n.
\]

For the odd columns it is

\[
 (A_Cv)_m=\sum_{n=1}^N\frac{2(n b_m-m b_n)v_n}{m^2-n^2}.
\]

With a uniform all-mode \(|b_m|\le B\), \(\rho=1-(N/(P+1))^2\), and \(W_j=[(2j-1)P^{2j-1}]^{-1/2}\), the odd tail has the rigorous norm bound

\[
 2\left|\sum b_n v_n\right|W_1
 +\frac{2B}{\rho}\sum n|v_n|W_2
 +\frac2\rho\sum n^2|b_n v_n|W_3.
\]

The even bound retains the signed leading moment \(\sum n b_n v_n\) and the nonzero boundary term, with \(W_1,W_2,W_3,W_4\) allowances. Tests compare both bounds with directly evaluated known omitted-mode actions. No retained-space residual substitutes for these tails.

Let \(V\) be the exact decimal columns, \(G=V^*V\), and \(W=VG^{-1/2}\). The Gram gate gives a lower bound \(g\) on \(G\), while interval inertia of \(UG-V^*A_CV\) proves \(W^*A_CW<U I\). For any selected diagonal shifts \(D_0\),

\[
 (I-WW^*)A_CW=(I-WW^*)(A_CV-VD_0)G^{-1/2}.
\]

Consequently its full Hilbert–Schmidt residual is bounded by the computed column residual norm divided by \(\sqrt g\). This avoids assuming that rounded columns are exactly orthonormal or that \(D_0\) commutes with \(G\).

The resulting certificate is

\[
 \|P-WW^*\|<0.531,
\]

where \(P\) is the actual rank-four spectral projection, separated by the certified outer gap \(>0.519\). The result and exact columns are in [C3_rank_four_full_residual.json](verification_2026_10_12_cluster/C3_rank_four_full_residual.json). The bound is moderate: the second odd column's prefix residual is about 0.263 and its tail bound about 0.080, the principal bottleneck. Improving the trial basis and signed tail cancellation is now a concrete subspace problem. This is a full residual certificate, not yet an accurate growing-support projector or an identification of the ground vector.

### What remains fragile inside the block

For an orthogonal trial split, formally write

\[
 A_C=\begin{pmatrix}H&B^*\\B&D\end{pmatrix},\qquad D\ge dI>0.
\]

When the block/domain identities and bounded coupling justify completing the square,

\[
 q_C(x,y)=\langle x,(H-B^*D^{-1}B)x\rangle
 +\|D^{1/2}(y+D^{-1}Bx)\|^2.
\tag{6}
\]

Positivity then reduces to the effective finite block \(H-B^*D^{-1}B\ge0\). This exposes the next arithmetic target. Replacing its signed correction by a coarse norm bound can still destroy its extremely small eigenvalues. A block certificate stabilizes the subspace problem; it does not manufacture the missing internal sign identity or a uniform computational cost bound.

The finite-support real-zero theorem in the existing route applies to a simple even **lowest** eigenvector. An arbitrary vector in the cluster has no such established theorem. Stable cluster approximation alone cannot be inserted into that theorem as if it selected the ground state.

## D2: a precise prime-side counting target

Start with a two-sided enclosure for \(N_C(t)\) at a **specified** threshold, with both parities and the arithmetic map's constraints counted. A realistic first asymptotic target is a main term \(2C\) with a quantified, threshold-dependent remainder; an (O(1)) remainder or the exact (-7/4) staircase needs additional proof.

The lower-count direction must produce a large trial space and control its geometric form uniformly over every linear combination, including its Gram matrix after the arithmetic map. Small quotients on individual vectors are insufficient. The upper-count direction needs a prime-side coercive estimate on the orthogonal complement. Prolate concentration alone establishes neither assertion for \(A_C\).

The fixed-support counts in (2) are unconditional written/computer-assisted results, not an asymptotic theorem. A threshold chosen after examining a spectrum is useful for certification but provides weak evidence for a universal counting law.

## D3: window positivity versus a zero-free region

The target is a contrapositive witness theorem: from an off-line zero \(\beta+i\gamma\), construct a compactly supported test function whose full Weil form is negative once \(\log C\) exceeds an explicit function of \(\gamma\) divided by \(\beta-1/2\). Turán power sums are a candidate tool for controlling cancellation among neighboring zeros.

The missing work is quantitative: select a finite zero packet without assuming RH, suppress its competitors, control the infinite zero tail, and track the support enlargement under every filter and convolution. The natural growth unit for this convention is \((\beta-1/2)\log C\); factors of two must come from the constructed witness rather than importing a different support convention. No function \(\Phi\) or universal bound \(\beta\le1/2+\Phi(\gamma)/\log C\) has been proved in this continuation.

Acceptance requires explicit constants, a zero-tail theorem, and evaluation of the actual geometric form, not an isolated negative off-line pair with the rest of the zeros omitted.

## D4: Davenport–Heilbronn control

The implementation [davenport_heilbronn_control.py](../../experiments/prime_spectral/davenport_heilbronn_control.py) uses the mod-5 datum

\[
 H(s)=\tfrac12(1-i\kappa)L(s,\chi)
       +\tfrac12(1+i\kappa)L(s,\bar\chi),\quad\chi(2)=i,
\]

\[
 \kappa=\frac{\sqrt{10-2\sqrt5}-2}{\sqrt5-1}.
\]

The periodic real Dirichlet coefficients are \(1,\kappa,-\kappa,-1,0\). [Gritsenko's primary research abstract](https://www.mathnet.ru/eng/present13282) states this normalization, its completed functional equation and its off-line zeros. [Bombieri–Ghosh](https://www.mathnet.ru/eng/rm9410) is the longer reference for this datum.

Define \(c_n\) by \(-H'/H=\sum c_n n^{-s}\) sufficiently far to the right. Dirichlet multiplication gives the finite recurrence

\[
 c_n=a_n\log n-\sum_{\substack{d\mid n\\1<d<n}}c_d a_{n/d}.
\]

In particular \(c_3=-\kappa\log3<0\) and

\[
 c_6=(1+\kappa^2)\log6>0.
\]

Thus coefficient nonnegativity first fails at 3 and prime-power support first fails at 6. Arb checks the first 64 coefficients, the closed forms, and a parallel zeta control giving the von Mangoldt values. These are log-derivative coefficients, not the paper's Taylor or Jensen coefficients.

This supplies an explicit arithmetic distinction but **does not** locate a first failing Toeplitz minor or a first negative Weil window. The latter requires the correct conductor, odd gamma factor, absence of zeta poles, and the **general** \(c_n\), including composite non-prime powers. Running the current zeta prime-power matrix with a changed label would not test (H). An all-hypothesis control run is still open.

A dedicated search also found a July 2026 preprint claiming this same mixed-prime obstruction and negative-control program \([author-hosted manuscript](https://www.researchgate.net/publication/410698893_THE_DAVENPORT-HEILBRONN_FUNCTION_AS_A_NEGATIVE_CONTROL_WEIL_WITNESSES_AN_OBSTRUCTION_TO_SPECTRAL-TRIPLE_CONVERGENCE_AND_THE_INDEX_STAIRCASE)\). Its linked Zenodo records could not be fetched in this session. This is a prior-art lead, not a validated external computation. The elementary coefficient calculation here is independently reproduced and is not claimed as new.

## D5: a precise robustness theorem

The separate [short note](ROBUSTNESS_OBSTRUCTION_C3P2_2026_10_12.md) defines robustness against **all bounded self-adjoint additive perturbations in operator norm**. The explicit C=3.2 trial supplies a rigorous upper bound on that radius. It makes no impossibility claim about exact arithmetic proofs or perturbations restricted to preserve prime structure. The undefined reference “result 2” is replaced by this explicit statement, following the user's instruction to decide.

## D6: what a one-direction induction must identify

The staircase increases by one when C increases by one half, but this arithmetic fact about the proposed rank is not an operator identity. Increasing support adds an infinite-dimensional \(L^2\) space. A newly active prime term is also an infinite-rank compressed translation, not a rank-one update: choose infinitely many independent functions on a small interval \(I\subset(0,\log C-\log q)\), with (I) shorter than the translation distance; the component of their images on \(I+\log q\) remains independent.

Consequently a one-direction induction must work on an exact effective quotient or Schur complement, with a proved cancellation of the other directions. The finite matrix inertia identity for a one-row extension is available algebraically, but applying it to growing C needs a coherent basis, full tail/coupling identities and the sign of the new Schur pivot. None is supplied merely by the observed count.

The rank-four C=3 trial cluster now has a full residual and projector-angle certificate. The next experiment is to improve its second odd column, extend the cluster family, and compare effective blocks at C and C+1/2 in a common arithmetic basis. Search for an exact identity there before accumulating more approximate coincidences.

## Validation and present boundary

Nine cluster tests, four full-residual tests and four arithmetic-control tests pass, for 17 new tests. All five full-operator block certificates replay; the four independent frequency entries and geometric normalization at C=3.2 pass at 512 bits. The full cluster and arithmetic-control test logs, independent comparison replay, and source/artifact manifest are saved in [the verification directory](verification_2026_10_12_cluster). The prior free-boundary adjoint batch now has its own [manifest](verification_2026_10_11_boundary_moment/manifest.json); its targeted six-lemma Lean build passed, while its separate axiom-print audit timed out without output and is explicitly incomplete.

No all-support counting theorem, calibrated zero-free region, first Davenport–Heilbronn Toeplitz/window failure, exact induction, or RH proof is established here.
