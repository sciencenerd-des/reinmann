# A bounded arithmetic Hermitian form and its mass obstruction

Research construction, 2026-10-10. The kernel identities and Jordan-chain
algebra have companion Lean checks listed in the
[validation record](form_validation_2026_10_10.json). The
Hilbert-space construction and estimates below are written proofs, not Lean
formalizations or independently reviewed results. No novelty or RH claim is
made. In particular, the nonzero masses of the ordinary Fock form cannot be
transferred to this different form.

## The removable divided difference

Use the corrected entire function `ξ=xiCompleted`, with
`ξ(1-s)=ξ(s)` and `ξ(conjugate s)=conjugate ξ(s)`. Define

```text
H(s,t) = i [ξ(s)-ξ(conjugate t)] / [s+conjugate t-1]
         if s ≠ 1-conjugate t,
H(s,t) = i ξ'(s) if s = 1-conjugate t.
```

The second line is essential. At a reflected pair the quotient has a removable
singularity; setting it to zero would lose the simple critical-line masses.
Equivalently, with `u=conjugate t`,

```text
H̃(s,u) = i ∫_0^1 ξ'((1-θ)(1-u)+θs) dθ,
H(s,t) = H̃(s,conjugate t).
```

The integral gives a jointly entire function of `(s,u)` by local dominated
convergence. It agrees with the quotient by the fundamental theorem along a
complex line segment and with `i ξ'(s)` on the removable locus. This is the
usual two-point divided difference with derivative value at repeated nodes;
see de Boor, [Divided Differences, Example 2, equation (10)](https://ftp.cs.wisc.edu/Approx/divdif.pdf).

Conjugating the quotient and using the two Xi symmetries proves
`H(s,t)=conjugate H(t,s)`. On the removable locus one also uses
`ξ'(1-s)=-ξ'(s)` and `ξ'(conjugate s)=conjugate ξ'(s)`.
For `λ(s)=-i(s-1/2)`, the exact arithmetic identity is

```text
[λ(s)-conjugate λ(t)] H(s,t) = ξ(s)-conjugate ξ(t).        (1)
```

It remains valid on the removable locus, since both sides are zero there.
Thus it supplies spectral symmetry at every pair of Xi zeros, including
hypothetical off-critical zeros, without assuming RH.

## Constructing a bounded operator from the arithmetic coefficients

Use the Fock space and the constants `C_b` from
[FOCK_DOMAIN_ESTIMATES.md](FOCK_DOMAIN_ESTIMATES.md). For any `0<b<1/6`,
the previously derived theta bound is
`|ξ(w)|≤C_b exp(b|w|²)`. Cauchy's derivative estimate on the radius-one circle
gives

```text
|ξ'(w)| ≤ C_b exp(b(|w|+1)²).
```

For the segment in the integral defining `H̃`,
`|w|+1≤2+|s|+|u|`, and
`(2+|s|+|u|)²≤12+3|s|²+3|u|²`. Consequently

```text
|H̃(s,u)| ≤ C_b exp(12b) exp(3b(|s|²+|u|²)).             (2)
```

Expand `H̃(s,u)=Σ_(m,n≥0) b_(m,n) s^m u^n`. The two-variable Fock norm
identity, obtained by applying the one-variable polar-coordinate identity
twice, implies

```text
Σ_(m,n≥0) m! n! |b_(m,n)|²
  = (1/π²) ∫_(ℂ²) |H̃(s,u)|² exp(-|s|²-|u|²) dA(s)dA(u)
  ≤ C_b² exp(24b) / (1-6b)².                            (3)
```

In the orthonormal monomial basis `e_n(z)=z^n/sqrt(n!)`, define the matrix

```text
G_(n,m) = sqrt(m! n!) b_(m,n).
```

By (3) this defines a Hilbert–Schmidt, hence bounded compact operator G on H,
with the explicit arithmetic bound

```text
||G|| ≤ ||G||_HS ≤ C_b exp(12b)/(1-6b).                  (4)
```

Hermitian kernel symmetry implies `b_(m,n)=conjugate b_(n,m)`, so G is
self-adjoint as a bounded operator on the ambient Fock space. Define the
bounded Hermitian form, linear in its first argument, by

```text
η_G(c,d)=η_Fock(Gc,d).
```

For `c(z)=Σ c_m z^m` and `d(z)=Σ d_n z^n`, this is the absolutely convergent
double series

```text
η_G(c,d)=Σ_(m,n≥0) m! n! b_(m,n) c_m conjugate d_n.
```

Absolute convergence follows by Cauchy–Schwarz on the product indices:
the Hilbert–Schmidt norm times `||c|| ||d||` bounds the absolute sum.
In particular,

```text
η_G(exp(sz),exp(tz))=H(s,t),
|η_G(c,d)| ≤ C_b exp(12b)/(1-6b) * ||c|| ||d||.           (5)
```

Neither positivity nor invertibility of G follows. In particular a compact
operator on the infinite-dimensional ambient H has no bounded inverse.
We therefore call `η_G` a bounded Hermitian form, without asserting that it
defines an equivalent Hilbert norm or a nondegenerate Krein-space metric.

In fact the form is indefinite on the ambient H. The theta representation gives
`Ξ'(0)=0` and `Ξ''(0)=-2∫_0^∞ u²Φ(u)du<0`. Thus `Ξ'(t)<0` for sufficiently
small positive t, while `Ξ'(-t)>0` by evenness of Ξ. Since
`H(1/2+it,1/2+it)=Ξ'(t)`, coherent vectors give both signs. Those particular
vectors have not been shown to lie in K_ξ; this argument classifies the ambient
form and does not establish indefiniteness of its restriction to K_ξ.

## Symmetry on the actual Xi operator domain

Keep the previously constructed `K_ξ=intersection ker R_n`,
`Dom(T_ξ)=K_ξ∩Dom(A)` and `T_ξ=-i(A-1/2)`. Put
`R_0(c)=Σ m! a_m c_m=η_Fock(c,ξ)`, where `a_m=ξ⁽ᵐ⁾(0)/m!`.
For all `c,d∈Dom(A)`, identity (1) yields

```text
η_G(Tc,d)-η_G(c,Td)
    = R_0(c) conjugate(d_0)-c_0 conjugate(R_0(d)).        (6)
```

Here is a domain justification rather than an assumption of (6). First compare
the Taylor coefficients in (1); the coefficient of `s^m u^n` gives (6) for
the monomials `z^m,z^n`, including the boundary indices zero. Finite linear
combinations give it for polynomials. Polynomial truncations converge in the
graph norm of A: both `Σ n! |c_n|²` and
`Σ n! |(n+1)c_(n+1)|²` have tails tending to zero. The boundedness of G,
`R_0` and coordinate evaluation at zero therefore extends (6) to `Dom(A)`.

For `c,d∈Dom(T_ξ)`, both R_0 terms vanish. Thus this construction supplies

```text
η_G(T_ξ c,d)=η_G(c,T_ξ d)                                (7)
```

on the full previously defined Xi domain. This is form symmetry, not
self-adjointness of T_ξ in the Fock inner product. Density, the adjoint and the
full spectrum of T_ξ remain unestablished. The fact that G itself is a bounded
self-adjoint operator does not establish self-adjointness of T_ξ.

## Exact masses, their decay, and the missing lower bound

For a Xi zero ρ and the coherent state `v_ρ=exp(ρz)`,

```text
η_G(v_ρ,v_ρ) = 0                     if Re(ρ) ≠ 1/2,
η_G(v_ρ,v_ρ) = i ξ'(ρ)               if Re(ρ) = 1/2.     (8)
```

The critical-line quantity is real because ξ' is purely imaginary there.
It need not be positive. It vanishes at a multiple critical-line zero.
Precisely, at any Xi zero,

```text
η_G(v_ρ,v_ρ) ≠ 0
    iff Re(ρ)=1/2 and ξ'(ρ)≠0.                          (9)
```

The same equivalence holds after Fock normalization
`u_ρ=exp(-|ρ|²/2)v_ρ`, with mass `exp(-|ρ|²)H(ρ,ρ)`.
Even at simple critical-line zeros there is no uniform positive lower bound
along an unbounded sequence of these normalized states. Indeed the derivative
estimate and `(|ρ|+1)²≤2|ρ|²+2` give the explicit upper bound

```text
|η_G(u_ρ,u_ρ)| ≤ C_b exp(2b) exp(-(1-2b)|ρ|²).           (10)
```

The right side tends to zero as `|ρ|→∞`. The local reduction does not require
a uniform lower bound over zeros, so this decay alone does not refute it.
However, approximate states need error budgets relative to this possibly tiny
mass. Fock norm one is not a lower bound for `|η_G(u_ρ,u_ρ)|`.

There is no independently proved nonvanishing bound in (8)–(10) for all zeros.
By (9), requiring it would assume both RH and simplicity of all Xi zeros.
This exact-state candidate supplies an arithmetic form and symmetry but does
not finish the full operator-and-mass objective. The companion
[approximate packet construction](APPROXIMATE_PACKET_MASS.md) avoids the
extra simplicity requirement and proves nonzero approximate-state masses in
the same form. Its paired residual estimate, needed for RH, remains open.

For a hypothetical simple off-critical zero ρ, its partner
`σ=1-conjugate ρ` is also a zero. The coherent states are linearly independent
(their coefficients at zero and one already distinguish them). On their
two-dimensional span the form has matrix

```text
[[0, B], [conjugate B, 0]],   B=i ξ'(ρ)≠0.
```

Its determinant is `-|B|²`, so it is nondegenerate, despite both eigenvectors
having zero diagonal mass and the eigenvalues being nonreal conjugates. This
conditional example inside the arithmetic construction explains why ordinary
nondegeneracy would still not supply the required mass hypothesis. It asserts
neither the existence nor the absence of an off-critical zero.

## Why the multiple-zero obstruction is structural

At a zero with `ξ(ρ)=ξ'(ρ)=0`, set

```text
j_ρ(z)=i z exp(ρz),
T_ξ j_ρ=λ(ρ)j_ρ+v_ρ.
```

The generalized state's Fock norm is explicitly
`||j_ρ||²=(1+|ρ|²)exp(|ρ|²)`: shift the coefficient sum to obtain
`Σ_(m≥0)(m+1)|ρ|^(2m)/m!` and differentiate the exponential series.
Its derivative is `i v_ρ+ρ j_ρ`, also in H. Thus these functions belong to the
maximal derivative domain. Differentiating the
entire Taylor series locally uniformly in ρ gives

```text
R_n(j_ρ)=i [ρ^n ξ'(ρ)+n ρ^(n-1) ξ(ρ)]=0,
```

with the second term interpreted as zero at n=0. Thus `j_ρ` also lies in the
Xi domain. At a critical-line ρ, λ is real. For *any* sesquilinear form F
symmetric between `j_ρ` and `v_ρ`,

```text
F(v_ρ,v_ρ)
 = F(Tj_ρ-λj_ρ,v_ρ)
 = F(j_ρ,Tv_ρ)-λ F(j_ρ,v_ρ)
 = (conjugate λ-λ)F(j_ρ,v_ρ)=0.                          (11)
```

This does not assume positive definiteness or nondegeneracy. It shows that
changing the bounded form alone cannot supply non-isotropy for the bottom
eigenvector of this real Jordan chain while retaining that paired symmetry.
The generic Jordan calculation, explicit coefficient chain and Xi-domain
membership via the convergent derivative Taylor series are formalized in
the companion modules. The Fock norm calculation and Hilbert-space domain
membership remain written arguments.

The local diagonal-only criterion avoids demanding symmetry against every
generalized state. Another possible change is a justified realization without
these Jordan chains. Simply discarding multiplicities or assuming simple zeros
would add an unproved condition and would not solve the original objective.

## Reproduction and contribution scope

The companion modules are
[XiDividedDifference.lean](../../Reinmann/XiDividedDifference.lean) and
[PseudoHermitianJordan.lean](../../Reinmann/PseudoHermitianJordan.lean), with
[XiJordanDomain.lean](../../Reinmann/XiJordanDomain.lean) checking the actual
Xi-row domain membership of the first jet and the resulting mass obstruction.
The first checks Xi symmetries, the regular kernel, spectral identity, Hermitian
symmetry and the exact mass obstruction. The second checks the Jordan-chain
mass identity and concrete coherent coefficient chain. The preceding bounded
operator, graph-core argument and mass decay are written mathematics and must
not be described as Lean-checked by those modules. Later
[packet mass modules](APPROXIMATE_PACKET_MASS.md) check the generic estimates,
and the [higher-jet milestone](HIGHER_JET_MASS_BRIDGE.md) checks all-order
coefficient-domain membership, finite multiplicity and the nonzero kernel
derivative. Full Fock-space compatibility and the general Hilbert packet
construction remain written mathematics.

The nonreal-eigenvector isotropy mechanism is classical; see Mostafazadeh,
[Pseudo-Hermiticity versus PT Symmetry, Proposition 2](https://arxiv.org/pdf/math-ph/0107001).
Divided differences and repeated-node derivatives are also classical. These
references establish context, not a novelty audit or external validation of
this particular Xi construction. No preprint's RH claim is used as a premise.

```sh
lake build
bash scripts/safe-verify.sh research/pseudo_hermitian/symmetry_mass_axiom_audit.lean
python3 research/pseudo_hermitian/check_packet_polynomials.py
```

The earlier form verification covers the 3,538-job build, a shortcut scan of 101
project Lean files, 28 new theorem-axiom checks using only `propext`,
`Classical.choice` and `Quot.sound`, and six exact synthetic polynomial cases.
Those checks do not formalize the written Hilbert-space or general packet proofs.
