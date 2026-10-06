# An Euler-region uniqueness gate for prime quotient polynomials

The [quotient construction](QUOTIENT_OPERATOR_2026_09_19.md) and
[grid factorization](GRID_TAIL_SCALING_2026_09_20.md) produce a normalized
even polynomial from each certified finite prime-defined Weil matrix:

\[
 R_j(z)=\frac{\det(zI-B_j)}{\det(-B_j)}
       =\prod_{\ell=1}^{N_j}(1-z^2/\lambda_{j,\ell}^2),
 \qquad \lambda_{j,\ell}\in\mathbb R\setminus\{0\}.
 \tag{1}
\]

The real, paired, nonzero spectrum in (1) requires the existing finite
quotient gates; it does not follow from the determinant formula alone.
The [coefficient budget](QUOTIENT_COEFFICIENT_BUDGET_2026_09_20.md)
identified the two missing sequence-wide facts: bounded
\(S_j=\sum_\ell\lambda_{j,\ell}^{-2}\), and identification of a limit.
The second fact can be tested in the absolutely convergent Euler region,
without computing any Xi Taylor coefficient or zero.

## Conditional uniqueness theorem

Let \(C_j\to\infty\), and assume (1) holds for every \(j\). Set
\(y_0=1\), \(E=\mathbb Q\cap(1,2)\), \(s=\tfrac12+y\), and
\(s_0=\tfrac32\). Define the finite prime-power expression

\[
 A(s)=\tfrac12s(s-1)\pi^{-s/2}\Gamma(s/2),\qquad
 Z_C(s)=\exp\!\left(\sum_{p^k\le C}\frac{p^{-ks}}{k}\right),\qquad
 T_C(y)=\frac{A(s)Z_C(s)}{A(s_0)Z_C(s_0)}.
 \tag{2}
\]

Here \(p\) runs over primes and \(k\ge1\); thus \(Z_C\) uses exactly
prime powers through the matrix support cutoff, not all powers of primes
\(p\le C\). Suppose

\[
 \sup_j R_j(i)<\infty,\qquad
 \log\frac{R_j(iy)}{R_j(i)}-\log T_{C_j}(y)\longrightarrow0
 \quad\text{for every }y\in E.
 \tag{3}
\]

Then \(R_j\to\Xi/\Xi(0)\) locally uniformly on \(\mathbb C\), so RH
follows. This is a sufficient condition, **not** a claim that (3) holds.

**Proof.** Every factor of \(R_j(i)\) is positive, and

\[
 R_j(i)=\prod_\ell(1+\lambda_{j,\ell}^{-2})
       \ge 1+S_j.
 \tag{4}
\]

The first bound in (3) therefore bounds \(S_j\). Expanding the product
or using \(1+t\le e^t\) gives
\(|R_j(z)|\le\exp(S_j|z|^2)\) on every disk. Montel's theorem (or the
explicit factorial-tail argument in the coefficient-budget note) gives
a locally uniformly convergent subsequence with entire limit \(F\).
It has \(F(0)=1\), and \(F(i)\ge1\).

For real \(s>1\), the Euler product and elementary integral comparison
give the effective tail

\[
 0\le\log\zeta(s)-\log Z_C(s)
   =\sum_{p^k>C}\frac{p^{-ks}}{k}
   \le\sum_{n>C}n^{-s}
   \le\frac{C^{1-s}}{s-1}.
 \tag{5}
\]

Consequently \(T_{C_j}(y)\to\xi(s)/\xi(s_0)\) for every \(y\in E\),
uniformly on compact subintervals of \(y>1/2\). The functional equation
\(\xi(s)=\xi(1-s)\) gives
\(\Xi(iy)=\xi(\tfrac12-y)=\xi(\tfrac12+y)=\xi(s)\).
Passing to the subsequence limit in (3) yields

\[
 F(iy)=F(i)\frac{\Xi(iy)}{\Xi(i)}\qquad(y\in E).
 \tag{6}
\]

Both sides are entire in \(z=iy\), and \(E\) has an accumulation point,
so the identity theorem extends (6) to all complex \(z\). At \(z=0\),
\(F(0)=1\) fixes \(F=\Xi/\Xi(0)\). Every convergent subsequence has
this same limit, proving convergence of the full family. Each \(R_j\)
has only real zeros. A small disk around a nonreal zero of the nonzero
limit would be zero-free for every \(R_j\), contradicting Hurwitz's
theorem. Thus every Xi zero is real. \(\square\)

Here \(\Xi(0)\ne0\): the alternating eta series at \(s=1/2\) is
positive, so \(\zeta(1/2)=\eta(1/2)/(1-\sqrt2)\ne0\), and the other
factors in \(\xi(1/2)\) are nonzero.

The one-point bound in (3) is essential to this argument. Ratios alone
do not bound normalization: \(1-j^2z^2\) has an unbounded value at
\(z=i\), while ratios of its values at fixed positive imaginary
arguments still have finite nonzero limits.

## A resolvent-trace version of the missing arithmetic gate

Because \(B_j\) has paired real eigenvalues, its *exact* logarithmic
derivative on the positive imaginary axis is

\[
 D_j(y):=\frac{d}{dy}\log R_j(iy)
      =y\operatorname{Tr}(B_j^2+y^2I)^{-1}
      =2y\sum_\ell(\lambda_{j,\ell}^2+y^2)^{-1}.
 \tag{7}
\]

The prime-power target uses \(\Lambda(p^k)=\log p\). Differentiating
(2), with \(s=\tfrac12+y\), gives

\[
 H_C(y):=\frac{d}{dy}\log[A(s)Z_C(s)]
  =\frac1s+\frac1{s-1}-\frac12\log\pi
   +\frac12\psi(s/2)-\sum_{n\le C}\frac{\Lambda(n)}{n^s},
 \tag{8}
\]

where \(\psi=\Gamma'/\Gamma\). For \(C\ge3\) and \(s>1\),
\(\Lambda(n)\le\log n\) and \((\log x)x^{-s}\) decreases on
\([C,\infty)\), so

\[
 0\le H_C(y)-\frac{d}{ds}\log\xi(s)
  =\sum_{n>C}\frac{\Lambda(n)}{n^s}
  \le C^{1-s}\left(\frac{\log C}{s-1}
                    +\frac1{(s-1)^2}\right).
 \tag{9}
\]

Thus a concrete sufficient replacement for the second condition in
(3) is

\[
 \int_1^2 |D_j(y)-H_{C_j}(y)|\,dy\longrightarrow0.
 \tag{10}
\]

Integrating (7) and (8) from \(1\) to any \(y\in(1,2)\) gives the
log-ratio condition. Equation (9) gives an explicit independent
prime-power tail for comparing \(H_C\) with the completed zeta target.
The bounded value \(R_j(i)\), finite quotient gates along a path, and
trace estimate (10) all remain **unproved**. The cutoff-13 certificates
do not imply them.

### Effective interpolation from a finite height mesh

The interval in (10) need not be checked point by point. Differentiating
the paired-root expression (7) gives, for \(1\le y\le2\),

\[
 |D_j'(y)|\le2\sum_\ell\lambda_{j,\ell}^{-2}
             =2S_j\le2(R_j(i)-1).                 \tag{10a}
\]

For the finite prime-power target, differentiate (8). With
\(s=y+1/2\), the negative rational part has magnitude at most
\(1/s^2+1/(s-1)^2\le40/9\). The trigamma series
\(\psi_1(t)=\sum_{k\ge0}(k+t)^{-2}\) gives
\(\psi_1(s/2)/4\le7/9\) by bounding its first term and integrating
the remainder. The other derivative terms are nonnegative and bounded
at \(s=3/2\). Therefore the explicit finite constant

\[
 K_C=\max\left\{\frac{40}{9},\;\frac79+
       \sum_{p^k\le C}\frac{(\log p)\log(p^k)}{(p^k)^{3/2}}\right\}
 \quad\text{satisfies}\quad |H_C'(y)|\le K_C.          \tag{10b}
\]

The constants \(K_C\) are uniformly bounded as \(C\to\infty\), since
the prime-power sum is at most
\(\sum_{n\ge2}(\log n)^2n^{-3/2}<\infty\).
For a mesh \(y_k=1+k/m\), \(0\le k\le m\), let \(M\ge R(i)\) and let
\(\varepsilon\) bound all sampled \(|D(y_k)-H_C(y_k)|\). Every point is
within \(1/(2m)\) of a node, so

\[
 \int_1^2|D(y)-H_C(y)|\,dy
 \le\sup_{1\le y\le2}|D(y)-H_C(y)|
 \le\varepsilon+\frac{2(M-1)+K_C}{2m}.         \tag{10c}
\]

Thus a path with certified uniform \(R_j(i)\) bounds, increasing mesh
sizes, and vanishing maximum sampled errors would satisfy (10), hence
the conditional RH theorem. No such path has been proved. Equation
(10c) makes finite sampled values into a rigorous interval-wide
budget; it does not promote the six certificates below to a sequence
theorem. The trigamma series is [DLMF 5.15.1](https://dlmf.nist.gov/5.15#E1).

The interval implementation now evaluates (10c) with 16 equal segments
for the existing isolated mode-16 certificates at \(C=13\) and \(23\).
At both cutoffs \(K_C=40/9\) is the active target bound. The saved
[cutoff-13](euler_mesh_13_16_m16.json) and
[cutoff-23](euler_mesh_23_16_m16.json) budgets are:

| \(C\) | Largest sampled error | Interpolation allowance | Whole-interval upper bound |
|---:|---:|---:|---:|
| 13 | `0.538734` | `0.139794` | `0.678528` |
| 23 | `0.423888` | `0.139782` | `0.563670` |

The maxima occur at \(y=1\). Their size shows that these small prime
cutoffs do not meet the Euler-region trace gate, even though the
mode-16 pointwise deficit at \(y=2\) was much smaller. Increasing the
number of mesh segments would reduce only the interpolation allowance,
not the sampled mismatch. This finite result directs attention to the
prime-power cutoff and the joint mode/support estimate; it is not an
asymptotic statement.

The same Lipschitz constant gives a *lower* bound on integrated error.
Let \(L_* = 2(M-1)+K_C\), \(h=1/m\), and let \(\delta_k\) be a certified
lower bound on \(|D(y_k)-H_C(y_k)|\). On the cell to the right of \(y_k\),
the reverse triangle inequality gives

\[
 |D(y)-H_C(y)|\ge \max\{0,\delta_k-L_*(y-y_k)\}.
\]

With \(a_k=\min\{h,\delta_k/L_*\}\), integration over the disjoint
cells proves

\[
 \int_1^2|D-H_C|\,dy\ge
 \sum_{k=0}^{m-1}\left(\delta_k a_k-\tfrac12L_*a_k^2\right). \tag{10d}
\]

There is a signed version as well. If \(g_k\) is a certified lower
bound on \(H_C(y_k)-D(y_k)\), nearest-node interpolation proves

\[
 H_C(y)-D(y)\ge\min_{0\le k\le m}g_k-\frac{L_*}{2m}
 \quad(1\le y\le2).                                      \tag{10e}
\]

For the two existing isolated mode-16 kernels, 64 segments make the
right side of (10e) strictly positive. All numbers below are outward
interval bounds from the saved
[cutoff-13](euler_mesh_13_16_m64.json) and
[cutoff-23](euler_mesh_23_16_m64.json) certificates:

| \(C\) | Minimum sampled \(H_C-D\) | Uniform \(H_C-D\) lower bound | Integrated absolute-error lower bound | Integrated absolute-error upper bound |
|---:|---:|---:|---:|---:|
| 13 | `0.046581543` | `0.011633128` | `0.118471527` | `0.573681778` |
| 23 | `0.041187152` | `0.006241783` | `0.082082877` | `0.458833127` |

The displayed decimals are rounded downward for lower bounds and upward
for upper bounds; the JSON records exact rational endpoints. This proves
that **these finite quotients** lie below the *finite prime-power target*
throughout the interval, and that their integrated mismatch cannot be
removed by refining the mesh. It does not compare them throughout the
interval to the completed Xi derivative: the omitted-prime tail in (9)
may exceed the signed gap, especially near \(y=1\). Nor does it give an
asymptotic lower bound for a growing cutoff-and-mode sequence.

## Rank-one secular cancellation

The quotient matrix is a diagonal Fourier grid minus a rank-one term.
The [direct eigenvector identity](EIGENVECTOR_COEFFICIENTS_2026_09_20.md)
therefore gives a trace formula that avoids a full interval inverse.
Write \(L=\log C\), \(a_n=(L/(2\pi n))^2\), and use the real even
boundary-normalized eigenvector \(c_{-n}=c_n\), with \(c_0\ne0\). Put

\[
 E_N(y)=\prod_{n=1}^N(1+a_ny^2),\qquad
 U_N(y)=c_0+2y^2\sum_{n=1}^N\frac{c_na_n}{1+a_ny^2}.
\]

The determinant lemma, or the polynomial identity in the linked note,
gives exactly

\[
 R(iy)=E_N(y)\frac{U_N(y)}{c_0},\qquad
 D_N(y)=2y\sum_{n=1}^N\frac{a_n}{1+a_ny^2}
       +\frac{4y\sum_{n=1}^N c_na_n/(1+a_ny^2)^2}{U_N(y)}.
 \tag{11}
\]

Under the real-zero gates \(R(iy)>0\); thus \(U_N(y)/c_0>0\).
The second term cancels most of the grid derivative in the finite
examples. Formula (11) keeps all eigenvector entries over the *same*
secular denominator. It is also an explicit version of the two open
sequence-wide bounds in (3) and (10).

For example, if \(R_j(i)\le M\), then exactly

\[
 0<\frac{U_{N_j}(1)}{c_{0,j}}\le\frac{M}{E_{N_j}(1)}.
 \tag{12}
\]

On a path with \(L_j\to\infty\) and \(N_j/L_j^2\to\infty\), the
[sine product](https://dlmf.nist.gov/4.22#E1) and the exterior-grid
bound give
\(E_{N_j}(1)=(1+o(1))\sinh(L_j/2)/(L_j/2)\). Hence (12) requires
\(U_{N_j}(1)/c_{0,j}=O(L_je^{-L_j/2})\). This is a necessary
quantitative eigenvector cancellation, not a derived estimate.

Similarly, for fixed \(y>0\), the omitted grid derivative is at most
\(yL^2/(2\pi^2N)\). Thus on that path the first term of (11) is
\(L/2-1/y+o(1)\). If the quotient trace converges pointwise to the
finite limit \(\xi'(1/2+y)/\xi(1/2+y)\), the secular correction must
cancel \(L/2\) to additive \(O(1)\). Neither this cancellation nor the
one-point estimate (12) follows from the finite certificates.

There is also a spatial version of the one-point gate. If the
[positive-kernel condition](POSITIVE_KERNEL_2026_09_22.md) holds, let
\(\nu_{C,N}\) be its even probability measure on \([-L/2,L/2]\), and
let \(T\) have that law. The exact profile factorization gives

\[
 R(i)=\frac{\mathbb E_\nu\cosh T}{G(i)},\qquad
 \mathbb E_\nu\cosh T
   =1+\int_0^{L/2}\sinh u\;\Pr_\nu\{|T|>u\}\,du.
 \tag{13}
\]

The second equality is the layer-cake identity for \(\cosh|T|-1\).
On a path with \(N/L^2\to\infty\), \(G(i)\to1\); hence the first
condition of (3) is equivalent to a uniform bound on the weighted tail
integral in (13). For example, a support-uniform bound
\(\Pr\{|T|>u\}\le K e^{-(1+\varepsilon)u}\) would suffice. The
previously certified variance controls only a polynomially weighted
tail and does not imply (13): a symmetric probability law putting
mass \(L^{-2}\) at \(\pm L/2\) can have bounded variance while its
\(\cosh\) moment diverges. The required exponential tail for the
actual prime-defined kernels remains unproved.

An exact Fourier-space control makes the arithmetic dependence plain.
Set \(c_0=1\) and \(c_n=0\) for \(n\ne0\). The spatial kernel is the
positive uniform density on \([-L/2,L/2]\), and the quotient polynomial
has only real grid zeros, but \(U_N(y)/c_0=1\) and
\(R(i)=E_N(1)\). Along \(N/L^2\to\infty\), this grows like
\(e^{L/2}/L\). Thus real-rootedness, kernel positivity, and boundary
normalization alone cannot establish the needed one-point bound;
the ground-eigenvector equations for the arithmetic Weil matrix must
provide the cancellation in (12).

## Six certified finite probes

The interval implementation `experiments/prime_spectral/euler_region_trace.py`
accepts the original mode-4/mode-8 Weil certificates and the separately
isolated higher-mode certificates. Both provide an enclosed even ground
eigenvector for (11). The calculation uses only prime powers through
\(C\) in (8). At \(y=2\), the certificates give:

| Cutoff \(C\) | Modes \(N\) | \(R(i)\), approximate | \(D_N(2)\), approximate | Certified deficit below \(\xi'(5/2)/\xi(5/2)\) |
|---:|---:|---:|---:|---:|
| 13 | 4 | `1.008253162` | `0.0324538611` | `>0.02515` |
| 13 | 8 | `1.011528546` | `0.0453711268` | `>0.01223` |
| 13 | 12 | `1.013278896` | `0.0522716237` | `>0.00533` |
| 13 | 16 | `1.014476372` | `0.0569891686` | `>0.00061` |
| 17 | 16 | `1.014406616` | `0.0567145497` | `>0.01051` |
| 23 | 16 | `1.014281417` | `0.0562218568` | `>0.01820` |

Each strict deficit uses the [elementary tail bound (9)](#a-resolvent-trace-version-of-the-missing-arithmetic-gate),
not a numerical zeta evaluation. The exact interval bounds and
input/source hashes are in the corresponding
`euler_trace_<C>_<N>_y2.json` files. The mode-4 secular formula also
overlaps the independently evaluated dense-matrix trace; that interval
inverse is unresolved at mode 8. At fixed \(C=13\), the four certified
derivatives increase with the tested mode counts. At fixed \(N=16\),
the tested derivatives decrease as \(C\) rises from 13 to 23, while
the certified lower bound for the arithmetic target rises. These
opposing finite trends make joint mode/support growth the next
experiment and proof target. They do not establish any asymptotic
monotonicity, convergence, or uniform separation.

Replay from the repository root:

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/euler_region_trace.py --certificate research/prime_spectral/certified_weil_13_4.json --height 2 --output research/prime_spectral/euler_trace_13_4_y2.json
uv run --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/euler_region_trace.py --certificate research/prime_spectral/certified_weil_13_8.json --height 2 --output research/prime_spectral/euler_trace_13_8_y2.json
uv run --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/euler_region_trace.py --certificate research/prime_spectral/isolated_kernel_23_16.json --height 2 --output research/prime_spectral/euler_trace_23_16_y2.json
uv run --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/euler_region_trace.py --certificate research/prime_spectral/isolated_kernel_23_16.json --height 2 --mesh-segments 16 --output research/prime_spectral/euler_mesh_23_16_m16.json
uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/prime_spectral -p 'test_*.py' -q
```

This route studies \(R_j\) directly, so the exterior-grid condition
\(N_j/(\log C_j)^2\to\infty\), necessary for convergence of the
original Fourier profile, is not logically required by this theorem.
It does not follow that any convenient mode path satisfies (3) or
(10). The finite quotient spectra still need arithmetic control.

References for the classical identities: [DLMF 25.4.3–4](https://dlmf.nist.gov/25.4#E3)
for \(\xi\) and its functional equation, and
[DLMF 25.2.11](https://dlmf.nist.gov/25.2#E11) for the Euler product.
