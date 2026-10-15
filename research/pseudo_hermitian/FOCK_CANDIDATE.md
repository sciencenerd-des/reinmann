# Xi-generated coefficient operator and its mass estimates

Date: 2026-10-10. This is an arithmetic candidate and an explicit audit of its
remaining symmetry obligation. It is not a pseudo-Hermitian witness for RH.
No novelty claim is made.

## Construction without a zero list

Let `ξ = xiCompleted` be the corrected entire Xi function, and let
`a_k = ξ⁽ᵏ⁾(0)/k!`. These are Taylor coefficients about `s=0`, distinct from
the folded coefficients `μₙ` and their classical Jensen weights `n! μₙ`.
Since ξ is entire, `Σ a_k s^k = ξ(s)` for every complex s.

On complex coefficient sequences `c=(c_n)`, define

```text
(A c)_n = (n+1)c_(n+1),     T = -i(A - 1/2).
R_n(c) = Σ_(k≥0) a_k (A^(k+n)c)_0.
D_ξ = {c : each row series R_n converges and R_n(c)=0 for every n≥0}.
```

Each row is linear on its convergence domain, so `D_ξ` is a complex submodule.
The identity `R_n(Ac)=R_(n+1)(c)` proves invariance under A and T. This is a
fixed operator defined using ξ and differentiation; its definition does not
take zeros as a basis or assume their real parts.

For every complex s define `v_s(n)=s^n/n!`. Then

```text
A v_s = s v_s;        T v_s = -i(s-1/2) v_s;
R_n(v_s) = s^n ξ(s);  v_s ∈ D_ξ iff ξ(s)=0.
```

Every critical-strip zero of ζ therefore gives an explicit state in `D_ξ`,
using the product identity between ξ and completed ζ away from 0 and 1.
The membership assertion uses the entire Taylor series, not a truncated
polynomial or a numerically estimated zero.

## Exact mass and pairing

The Fock coefficient pairing, linear in its first slot, is

```text
η(c,d) = Σ_(n≥0) n! c_n conjugate(d_n).
η(v_s,v_t) = exp(s conjugate(t)).
η(v_s,v_s) = exp(|s|²) > 0.
```

These coherent-vector series converge absolutely. In particular the selected
states have a finite, nonzero mass at every height, without RH. The normalized
state `u_s = exp(-|s|²/2)v_s` has mass exactly 1. Normalization also gives the
explicit Gram kernel

```text
η(u_s,u_t) = exp(s conjugate(t) - (|s|²+|t|²)/2),
|η(u_s,u_t)| = exp(-|s-t|²/2).
```

The coefficient identity and convergent unnormalized pairing are checked in
[FockEigenvectors.lean](../../Reinmann/FockEigenvectors.lean). The arithmetic
domain and zero-to-state identities are checked separately in
[XiAnnihilator.lean](../../Reinmann/XiAnnihilator.lean). See
[construction validation](construction_validation_2026_10_10.json) for
the exact list of successful theorem checks; do not infer a full Hilbert-space
construction from the coefficient results.

For arbitrary raw sequences a `tsum` can be undefined analytically; Lean returns
zero for a nonsummable series. Consequently the totalized raw-sequence form is
only used as a scalar-homogeneous interface, and no global additivity,
positivity, norm or completeness is asserted on that carrier. A genuine Fock
Hilbert carrier is the subspace satisfying `Σ n! |c_n|² < ∞`, with maximal
derivative domain additionally satisfying `Σ n! |(n+1)c_(n+1)|² < ∞`.
The coherent states belong to both because A acts as multiplication by s on
them. Formal Hilbert-space domain/closure/density assertions remain open.
The separate written [analytic domain estimates](FOCK_DOMAIN_ESTIMATES.md)
derive a Gaussian growth bound from the theta kernel, bounded arithmetic row
functionals, and a closed restricted operator with unit-mass zero states.
That argument is not a Lean theorem or an independently reviewed result;
density and symmetry are not established there.

## Why the mass estimate does not finish the reduction

With `λ(s)=-i(s-1/2)` and `d(v,w)=η(w,v)-η(v,w)`, the exact identity is

```text
d(u_s,T u_s) = -2i (Re(s)-1/2).
|d(u_s,T u_s)| = 2|Re(s)-1/2|.
```

Thus the diagonal symmetry condition at these states is equivalent to
`Re(s)=1/2`. The mass and eigendata are constructed, but no arithmetic estimate
has made this defect vanish at Xi zeros. Treating this identity as such an
estimate would assume the desired conclusion.

There is a second obstruction to seeking *global* symmetry for the same Fock
form. For s and t on the critical line with different heights,

```text
η(Tu_s,u_t) - η(u_s,Tu_t)
    = (Im(s)-Im(t)) η(u_s,u_t) ≠ 0.
```

Coherent overlaps never vanish, whereas distinct real eigenvalues of a symmetric
operator must have orthogonal states. This rules out global symmetry for this
form whenever the arithmetic domain contains two such zero states. It does not
rule out a different form, or the weaker diagonal-only criterion.

There is an explicit cost to changing the metric. If a replacement form
`η_G(c,d)=η(Gc,d)` makes two such states with distinct real eigenvalues
orthogonal, then, since both have Fock norm one,

```text
|η((G-I)u_s,u_t)| = |η(u_s,u_t)| = exp(-|s-t|²/2).
```

For bounded G, Cauchy–Schwarz therefore forces
`||G-I|| ≥ exp(-|s-t|²/2)`. This is a written consequence of the Gram formula,
not an additional Lean theorem. It rules out a perturbation smaller than that
bound for the selected pair; it does not rule out a more substantial metric
change or prove the existence of a suitable one.

The next substantive task is therefore an arithmetic form or estimate that
controls diagonal defects independently of zero criticality. Rephrasing
`ξ(s)=0 ⇒ d(u_s,Tu_s)=0` supplies no new content: for this candidate it is RH.
Finite Gram orthogonalization needs its own infinite-domain and mass estimates.

## Candidate screening and classical context

The original [BBM proposal](https://arxiv.org/pdf/1608.03679) uses Hurwitz zeta
states and shift conjugation. Its graph-metric candidate transforms these states
to `x^(-s)`. Directly,

```text
∫_0^∞ |x^(-s)|² dx = ∫_0^∞ x^(-2 Re(s)) dx = ∞
```

for every s: convergence at zero requires `Re(s)<1/2`, while convergence at
infinity requires `Re(s)>1/2`. Thus this particular full-half-line mass cannot
supply finite selected-state masses. On `x≥1`, an off-critical state with
`Re(s)>1/2` instead has mass `1/(2 Re(s)-1)` and a nonzero dilation boundary
defect. Dropping the boundary term would falsely prove reality.

[Bellissard's 2017 comment](https://arxiv.org/abs/1704.02644) identifies domain
and weighted-space difficulties. [Liu's 2026 preprint](https://arxiv.org/abs/2607.19067)
studies the standard L² metric completion and reports absent critical-line BBM
point states. That broader completion theorem has not been replayed here; the
elementary integral obstruction above is independently derivable.

The coherent-state and reproducing-kernel facts are classical; see Daubechies
and Grossmann, [Frames in the Bargmann Space of Entire Functions](https://wiki.math.ntnu.no/_media/ma8104/2021h/2387_daubechiesgrossmann.pdf),
with rescaling to our `exp(-|z|²)` convention and a first-slot-linear pairing.
[Meyer's spectral realization](https://arxiv.org/pdf/math/0412277) uses an
arithmetic summation operator and a nuclear Fréchet quotient, whose transposed
generator has the zeta zeros as eigenvalues. Its quotient and dual topology must
be retained when considering mass estimates. It does not supply a positive
symmetric metric for the present construction.

These are initial primary-source checks, not an exhaustive novelty audit.
