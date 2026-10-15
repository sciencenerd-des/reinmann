# Orthogonality improves the Fourier certificate but preserves its growth exponent

Date: 11 October 2026. Status: written Hilbert-space argument and Arb certificate, not a new operator realization, novelty claim, or RH proof. This continues the [full-ground-state enclosure](FULL_GROUND_FOURIER_2026_10_11.md) in the separate `codex/xi-eigenvector-reduction` worktree. The original spectral certificates and nine-mode trials are unchanged.

The subsequent [full adjoint certificate](ADJOINT_FOURIER_CERTIFICATE_2026_10_11.md) implements the proposed local operator test below, with complete residual tails and a compact complex-rectangle cover. The canonical arithmetic candidate and growing-support comparison remain open.

## Result

At fixed support length L=log C, let u be the genuine real even unit ground state, oriented toward the exact unit trial g. Normalize Fourier transforms by their value at zero. The following are weakened outward bounds, uniform over **all** real parts of z with |Im z|≤0.4:

| Quantity | C=2 | C=3 |
|---|---:|---:|
| Previous normalized Fourier-profile error | <0.14072 | <0.45309 |
| New normalized Fourier-profile error | **<0.05310** | **<0.17867** |
| Previous normalized ground mean lower bound | >0.83604 | >0.64162 |
| New normalized ground mean lower bound | **>0.86479** | **>0.68014** |

The state-distance bounds remain <0.05509 and <0.12407. The improvement comes entirely from retaining orthogonality when transferring to the Fourier observable. It does not depend on a larger Ritz space or a new spectral-gap estimate.

All full-operator inputs retain their original trust boundary: written closed-form realization, compactness, comparison and min-max analysis plus rigorously enclosed finite arithmetic. The new calculation certifies scalar geometry and a universal kernel bound; it does not formalize these operator facts in Lean.

## Sharper protection of the mean

Use the normalized centered Fourier functional

\[
 F_z(f)=L^{-1/2}\int_{-L/2}^{L/2}f(x)e^{-izx}\,dx.
\]

Let e=L^-1/2 be the unit constant function and m=F_0(g)=⟨g,e⟩>0. The full form-energy bound gives

\[
 1-|\langle u,g\rangle|^2\le r
 =\frac{\mu-\ell}{b-\ell}<1,
\]

where μ is the full-form Rayleigh upper bound, ell is a full ground lower bound and b is a full second-level lower bound. Write u=cg+w, with c≥sqrt(1−r), w⊥g and ||w||≤sqrt r. These facts follow from the same angle bound as the previous transfer, since both vectors have unit norm.

The constant function's projection on g-perp has norm sqrt(1−m²). Hence

\[
 F_0(u)\ge D(m,r):=m\sqrt{1-r}-\sqrt{r(1-m^2)}.
\]

This is positive exactly when r<m², and is a sharp universal geometric lower bound: a two-dimensional real unit-vector example attains it. Using a lower enclosure for m and an upper enclosure for r is valid because D increases with m and decreases with r. A protected Fourier mean is still not an endpoint trace.

## Transfer of the normalized observable

Evenness replaces exp(−izx) by ψ_z(x)=cos(zx) in the Fourier integral. Identify normalized integrals with inner products against the corresponding kernels. Put

\[
 s_z=F_z(e)=\operatorname{sinc}(Lz/2),\qquad
 V_L(z)=\|\psi_z\|_{L^2(dx/L)}^2-|s_z|^2.
\]

The physical Riesz kernel is ψ_z/sqrt(L); the displayed weighted norm equals its ordinary L2 norm. V is the squared norm after removing its constant component. For a=L Re z and b=L Im z,

\[
 V(a,b)=\frac12\left(\frac{\sinh b}{b}+\frac{\sin a}{a}\right)
        -\left|\operatorname{sinc}\frac{a+ib}{2}\right|^2,
\]

with entire continuation at zero.

Let p_z=F_z(g)/m. The functional L_z(f)=F_z(f)−p_zF_0(f) vanishes on g. Its kernel decomposes into a mean-zero part and a constant part. Since ||g−me||=sqrt(1−m²), Cauchy–Schwarz gives

\[
 \|L_z\|^2=V_L(z)+|p_z-s_z|^2\le V_L(z)/m^2.
\]

The c*g contributions cancel **before** estimating the normalized difference:

\[
 \left|\frac{F_z(u)}{F_0(u)}-\frac{F_z(g)}m\right|
 =\frac{|L_z(w)|}{F_0(u)}
 \le\frac{\sqrt{r V_L(z)}}{m D(m,r)}.
\]

In particular the error is exactly zero at z=0. The previous triangle estimate did not retain this cancellation. The displayed bound uses only a uniform variance enclosure and does not numerically evaluate the unknown ground state.

## Complete horizontal-strip coverage

V(a,b) is even in both a and b. The code encloses it over rectangular cells covering 0≤a≤16 and 0≤b≤L*Y. There are 512 real cells and 16 imaginary cells at positive Y, hence 8192 rectangles per positive-height strip. At height zero the cover has 512 intervals. Arb's entire sinc routine handles cells containing zero without dividing by an unresolved interval.

For a≥16, the nonnegative final term can be discarded and |sin a/a|≤1/16. Thus the remaining, infinite-frequency tail obeys

\[
 V(a,b)\le\frac12\left(\frac{\sinh(LY)}{LY}+\frac1{16}\right).
\]

Monotonicity of sinh b/b on b≥0 justifies the height endpoint. The maximum of the rectangle bounds and this tail bound covers the full strip. This is a finite interval cover plus an analytic tail argument, not a dense point scan. The certificate records the cover counts, maximum cell, separate compact/tail bounds and source hashes.

## Why this does not remove the growing-support obstruction

Removing the constant mode preserves exponential amplification on nonreal strips. At the imaginary frequency z=iY, put B=LY. The exact mean-zero even kernel norm is

\[
 V(0,B)=\frac12+\frac{\sinh B}{2B}
                 -\frac{2(\cosh B-1)}{B^2}
       \sim\frac{e^B}{4B}.
\]

For B≥8 this is at least e^B/(8B). Indeed, expansion into e^B and e^-B gives

\[
 V(0,B)=\frac{e^B}{4B}(1-4/B)
 +\frac12+\frac2{B^2}
 -e^{-B}\left(\frac1{4B}+\frac1{B^2}\right),
\]

whose first term is at least e^B/(8B), and whose remainder is positive for B≥8. The universal upper bound V(a,b)≤(1+sinh B/B)/2 has the same leading asymptotic. Consequently sup_{|b|≤B,a∈R}V(a,b)~e^B/(4B).

This growth is attained by a real even mean-zero error proportional to cosh(Yx) minus its mean. It is an obstruction to improving the **unrestricted L2 observable norm**, not a counterexample to convergence of the arithmetic Weil ground states. More generally the normalized-difference kernel has norm squared V+|p−s|²≥V, even though it annihilates the trial.

The new sufficient acceptance quantity is sqrt(r_L V_L*)/(m_L D_L). If r_L/m_L²→0, its square is asymptotic to r_L V_L*/m_L^4. Thus the earlier sufficient requirement r_L=o(L*m_L^4*exp(−LY)) remains at fixed Y>0. Orthogonality improves the constants substantially but does not by itself change this exponent.

The next global estimate must therefore either deliver the required support-dependent energy/gap rate for the specified Xi-producing candidate, or exploit additional arithmetic structure in the observable error. Another generic L2 triangle inequality cannot supply that structure.

## A precise next test: a full adjoint residual for the observable

There is a standard duality alternative that deserves an actual operator experiment. It is a proposed test, not an achieved estimate. Work in the physical L2 space and let k_z be the Riesz vector of the linear functional F_z−p_z F_0, where p_z is the specified candidate's origin-normalized Fourier profile. Thus ||k_z|| is measured with the same normalization as F_z. Suppose Au=λ0u, ||u||=1, F_0(u)≥M>0, and |λ0−ν|≤δ. For an explicit h_z in the **operator domain**, suppose

\[
 \|(A-\nu)h_z-k_z\|_2\le\varepsilon_z,
 \qquad \|h_z\|_2\le H_z.
\]

Self-adjointness, followed by Cauchy–Schwarz, gives

\[
 \left|\frac{F_z(u)}{F_0(u)}-p_z\right|
 \le\frac{\varepsilon_z+\delta H_z}{M}.
\]

For complex functionals use the Riesz convention making evaluation linear in u; conjugating the displayed residual vector if required changes none of these norms. The proof moves A from h_z to the genuine eigenvector u. This is why a form-domain polynomial or a projected residual cannot replace the stated operator-domain vector and full L2 residual.

This criterion has no explicit spectral-gap denominator. It does not make the gap difficulty disappear: the correction norm H_z can diverge near other spectral levels, the residual has a ground component equal to the observable mismatch when ν=λ0, and the term δ H_z can undo a small computed residual. It supplies a falsifiable alternative, not a way to assume the desired comparison.

At C=2 and C=3 the protected means above give concrete M, and the earlier full spectral lower bounds plus trial upper bounds supply an interval for λ0. The first experiment should construct a finite correction for selected z, enforce the actual operator domain, and enclose its entire residual, omitted modes, and δ H_z. Proceed to compact sets of z and growing support only if that complete bound improves the existing observable certificate. Any eventual Xi comparison must use the same specified arithmetic candidate, rather than a fitted profile that only matches the ground state locally.

## Validation and reproduction

Run from the worktree root with Python 3.12, `python-flint==0.8.0`, and `mpmath`:

```sh
uv run --with python-flint==0.8.0 --with mpmath --python 3.12 python experiments/prime_spectral/orthogonal_fourier_transfer.py --output research/prime_spectral/verification_2026_10_11_orthogonal_fourier/orthogonal_transfer.json
uv run --with python-flint==0.8.0 --with mpmath --python 3.12 python -m unittest discover -s experiments/prime_spectral -p test_orthogonal_fourier_transfer.py -v
```

Ten tests pass, including a saturating two-mode geometry, independently integrated complex Fourier kernels, normalized complex profiles, analytic-tail regressions, fail-closed inputs, provenance tampering, and the exponential lower bound. The original five scalar Lean lemmas have now also passed their standard-axiom audit, with exact source/log hashes checked. The new orthogonal functional theorem is written mathematics, not an additional Lean theorem.

The [verification directory](verification_2026_10_11_orthogonal_fourier/) stores exact rational outward endpoints. These results concern C=2 and C=3. No increasing-support candidate family, Xi identification or RH proof is established by this continuation.
