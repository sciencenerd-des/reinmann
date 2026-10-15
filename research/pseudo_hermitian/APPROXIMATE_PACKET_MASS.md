# Approximate-state masses without a simplicity assumption

Written mathematical construction, 2026-10-10. This note uses the bounded
Hermitian form and domain constructed in
[XI_DIVIDED_DIFFERENCE.md](XI_DIVIDED_DIFFERENCE.md). The generic packet mass
and normalization estimates below are checked in Lean. The
[all-order arithmetic jet and kernel-derivative lemmas](HIGHER_JET_MASS_BRIDGE.md)
are also checked. Their identification with the full Hilbert-space pairing has
not been formalized or independently reviewed. This note constructs nonzero
masses and small ordinary residuals for the
same arithmetic operator and form; it does not prove the paired residual
estimate needed for RH.

## A nonzero pairing at every zero, including multiple zeros

Let ρ be any zero of ξ. It has some finite multiplicity `m≥1`, because ξ is
entire and not identically zero (`ξ(0)=1/2`). Thus

```text
ξ⁽ʲ⁾(ρ)=0 for 0≤j<m,       ξ⁽ᵐ⁾(ρ)≠0.
```

Set `σ=1-conjugate ρ`, which is a zero of the same multiplicity, and let

```text
v(z)=exp(ρz),    w(z)=z^(m-1) exp(σz).
```

Both belong to `Dom(T_ξ)`. For w, differentiating the entire Xi row identity
`R_n(exp(tz))=t^n ξ(t)` exactly `m-1` times at t=σ gives zero by the
multiplicity conditions. All such polynomial-times-exponential vectors lie
in the maximal derivative domain. For each integer `p≥0`, their explicit
Fock norm is the convergent positive series

```text
||z^p exp(σz)||² = Σ_(k≥0) (k+p)! |σ|^(2k)/(k!)².
```

The ratio of consecutive terms tends to zero, and differentiating the vector
gives a finite combination of two such vectors. Hence every operation in the
following calculation lies in the operator domain. Parameter differentiation
also converges in the Fock norm locally uniformly: on any fixed parameter
disk the same coefficient series is dominated by the one at a larger radius.
The boundedness of the form then justifies differentiating its kernel.

For the form η_G from the divided-difference construction, define
`B=η_G(v,w)`. Its kernel gives the exact formula

```text
B = i (-1)^(m+1) ξ⁽ᵐ⁾(ρ)/m ≠ 0.                        (1)
```

To verify it, fix the first kernel argument at ρ and put `u=conjugate t`:

```text
H(ρ,t) = -i ξ(u)/(u-(1-ρ)).
```

The numerator has a zero of order m at `u=1-ρ`. The derivative of order m-1
of this removable quotient there is
`-i ξ⁽ᵐ⁾(1-ρ)/m`, which equals (1) by differentiated Xi reflection.
For m=1 the same computation is the regular kernel value, not division by zero.

Thus even when v itself is isotropic, a vector w in the actual arithmetic
domain has a provably nonzero cross pairing with it. No assumption of RH or
simple zeros enters this construction. The pointwise constant in (1) uses
the first nonzero derivative at the given zero; it supplies no uniform bound
over zeros or their multiplicities.

## A positive mass lower bound in the isotropic case

Suppose `η_G(v,v)=0`. Hermitian symmetry makes `C=η_G(w,w)` real. Put
`α=B/|B|`, so `|α|=1`, and choose a real h with

```text
0<h≤min(1, |B|/(1+|C|)).
```

For `x_h=v+h α w`, sesquilinearity gives

```text
q_h=η_G(x_h,x_h)=2h|B|+h² C,
h|B| ≤ q_h ≤ 3h|B|.                                   (2)
```

Indeed the two cross terms are each h|B|, and
`h²|C|≤h|B|`. In particular q_h is strictly positive and real. Define

```text
ψ_h=x_h/sqrt(q_h).
```

Then `η_G(ψ_h,ψ_h)=1` exactly. Since the domain is a complex vector space,
ψ_h still lies in `Dom(T_ξ)`.

The finite ordinary residual is explicit. Write `λ=λ(ρ)`, `p=m-1`, and
`R=(T_ξ-λ)w`. Then

```text
R=(λ(σ)-λ(ρ))w - i p z^(p-1)exp(σz),
r_h=T_ξψ_h-λψ_h = h α R/sqrt(q_h),
||r_h|| ≤ sqrt(h/|B|) ||R|| → 0.                        (3)
```

At p=0 the second term in R is zero. Its norm is bounded by the convergent
norm series above, using `|λ(σ)-λ(ρ)|=2|Re(ρ)-1/2|`.
Thus (2) and (3) give a constructive mass lower bound and an ordinary
eigenvector-residual bound at every isotropic zero state, including all
hypothetical off-critical zeros and multiple critical-line zeros.

If instead `η_G(v,v)≠0`, the earlier kernel theorem implies that ρ is a
simple critical-line zero. The exact eigenvector
`ψ=v/sqrt(|η_G(v,v)|)` has *absolute* form mass one and zero residual.
Its signed mass can be -1; complex scalar rescaling cannot change that sign.
Together the two cases give states with absolute form mass one and arbitrarily
small ordinary residual for every Xi zero, without assuming simplicity or RH.

## A simpler parameterization with checked estimates

The same family admits a parameterization that avoids division by `|B|`.
For an isotropic v, let

```text
y_h = v + h B w,               0<h≤1/(1+|C|),
Q_h = η_G(y_h,y_h) = |B|²(2h+h²C),
h|B|² ≤ Q_h ≤ 3h|B|²,
φ_h = y_h/sqrt(Q_h),           η_G(φ_h,φ_h)=1,
||(T_ξ-λ)φ_h|| ≤ sqrt(h) ||(T_ξ-λ)w||.                (5)
```

This is the earlier mixture with its parameter replaced by `h|B|`.
The lower bound controls the normalization factor directly:
`h|B|/sqrt(Q_h)≤sqrt(h)`. Given any `τ>0`, choosing

```text
0<h<min(1/(1+|C|), (τ/(||(T_ξ-λ)w||+1))²)
```

makes the ordinary residual strictly smaller than τ. No continuity or operator
symmetry is needed for this generic estimate; Hermitian symmetry of the form,
isotropy of v, a nonzero cross pairing and the exact eigenvector identity are
its premises.

[PseudoHermitianPacketMass.lean](../../Reinmann/PseudoHermitianPacketMass.lean)
checks the exact mass formula, both bounds, positivity, normalization and the
residual identity. [PseudoHermitianPacketNorm.lean](../../Reinmann/PseudoHermitianPacketNorm.lean)
checks the square-root residual estimate and existence of a unit-mass packet
for every positive ordinary residual tolerance. These abstract proofs apply
to any normed complex vector space with the specified form and linear action;
they do not supply the higher-jet Xi domain or cross-pairing premises.

## Checked arithmetic core for reflected simple-zero pairs

[XiKernelPackets.lean](../../Reinmann/XiKernelPackets.lean) defines a
two-coordinate packet form directly from the Xi kernel Gram matrix
`H(s,s), H(s,t), H(t,s), H(t,t)`. It checks Hermitian symmetry and form
symmetry of the diagonal action at Xi zeros. The realization

```text
(a,b) ↦ a exp(sz) + b exp(tz)
```

maps into the independently defined arithmetic coefficient domain. Lean
checks that it intertwines the action with `spectralOnDomain`, preserves the
residual identity and is injective when s and t are distinct, using coefficients
zero and one.

For a hypothetical simple off-critical zero `s`, take `t=1-conjugate s`.
The checked kernel formula gives the required nonzero cross pairing
`H(s,t)=i ξ'(s)`. Lean then constructs a packet with signed mass one,
nonzero realization in the actual coefficient domain and arbitrarily small
ordinary residual in the **coordinate packet norm**. Its paired residual
defect is exactly `2|Re(s)-1/2|`. This conditional theorem asserts neither
existence nor absence of off-critical zeros.

The formal norm is not the Fock norm. Transferring the coordinate estimate
to Fock space follows in the written construction from the bounded map on
this finite span, but that analytic transfer has not been formalized. The
general higher-jet kernel derivative and coefficient-domain membership are
now checked in [HIGHER_JET_MASS_BRIDGE.md](HIGHER_JET_MASS_BRIDGE.md).
Identifying that derivative with the Fock form value in (1) remains a written
proof. The checked generic bounds in (5) can apply once that compatibility
and the Fock-space premises are formalized. The objective continues to cover
all zero multiplicities.

## The paired residual does not become small off the line

This construction does not satisfy the approximate RH reduction merely by
making h small. Symmetry of T_ξ for the same form and the exact residual
identity imply, for either construction above,

```text
d_G(ψ,T_ξψ)=0,
d_G(ψ,r)=-(λ-conjugate λ)η_G(ψ,ψ),
|d_G(ψ,r)|=2|Re(ρ)-1/2|.                               (4)
```

The last equality uses absolute form mass one. For an off-critical zero this
is a fixed nonzero number for every h, even though (3) tends to zero.
The unit-mass paired identity (4) is also checked as
`Reinmann.PacketMass.paired_residual_norm_of_unit_mass`.
There is no conflict with Cauchy–Schwarz: in the isotropic construction,
`||ψ_h||_Fock` tends to infinity. In fact `x_h→v≠0`, whereas q_h tends to
zero linearly by (2), so normalizing q_h magnifies the Fock norm by order
`h^(-1/2)`. The paired term need not shrink with the ordinary residual norm.

At a critical multiple zero the paired defect is zero. Consequently the
approximate interface can accommodate multiplicities even though an exact
non-isotropic eigenvector is impossible for a globally symmetric form on the
full Jordan domain. Simplicity is an extra requirement of the exact-state
version of this particular realization, not a requirement of RH itself or
of the verified approximate reduction.

The unresolved arithmetic step is still an independent bound making (4)
arbitrarily small relative to the mass at every zero. The mass construction
does not provide that bound. Fock norm control, a small unpaired residual,
ordinary nondegeneracy and combining estimates from different forms cannot
replace it. The full research objective therefore remains open.

There is an optional sufficient norm estimate to investigate. For any bounded form
with `|η(x,y)|≤K||x|| ||y||`, the triangle inequality and (4) give

```text
|Re(ρ)-1/2| ≤ K ||ψ|| ||(T_ξ-λ(ρ))ψ||,   |η(ψ,ψ)|=1.   (6)
```

The generic inequality and its local criticality criterion are checked as
`distance_le_norm_product` and `critical_of_arbitrarily_small_norm_product`
in `Reinmann.PacketMass`. Thus making this product arbitrarily small at
every zero would suffice for the reduction. The present isotropic packets
cannot achieve that at an off-critical zero: (6) gives a fixed positive lower
bound for their product. A bounded family of unit-mass approximate states
with residuals tending to zero would meet the criterion, but no such
arithmetic family has been established. This sufficient criterion is stronger
than the paired-defect requirement and must not replace it.

[PseudoHermitianNormProductObstruction.lean](../../Reinmann/PseudoHermitianNormProductObstruction.lean)
checks the distinction on a real length-two Jordan block:

```text
N(a,b)=(b,0),     η(x,y)=x₁ conjugate(y₂)+x₂ conjugate(y₁).
```

N is symmetric for this nondegenerate Hermitian form. There are unit-mass
packets with arbitrarily small ordinary residual `||Nx||` and exactly zero
paired residual, yet every state with `|η(x,x)|=1` satisfies
`||x|| ||Nx||≥1/2`. Thus successful paired cancellation need not force the
norm product to zero, even at a real eigenvalue. This synthetic example makes
no assertion about actual Xi zero multiplicities. It prevents the optional
norm-product route from silently strengthening the original objective, which
continues to admit multiple zeros on the critical line.

The [packet mass validation record](packet_mass_validation_2026_10_10.json)
saves source and log hashes for the full 3,541-job build and 25 theorem-axiom
audits. The shortcut scan covered 104 project Lean files. Both checkouts retain
all 14 manuscript seed files unchanged.

## Subsequent algebraic same-form mass realization

The [fixed algebraic jet construction](ALGEBRAIC_JET_MASS.md) now supplies a
checked all-multiplicity realization of the cross-pairing and packet masses
inside the existing coefficient domain. Its one fixed Hermitian form uses
Hermitianized mixed derivatives of the Xi kernel on all complex parameters and
all jet orders. Unique finite coordinates make it a form on actual coefficient
states. The coherent-to-jet entries, nonzero partner at every Xi zero, explicit
mass lower and upper bounds, normalization and exact residual identity are
checked in Lean for that same form and restricted arithmetic action.

This algebraic result does not formally identify the full Fock-space pairing
with those entries. It also supplies neither action symmetry for its form nor
the independent paired residual estimate. The analytic arguments above retain
their written-proof status.

The subsequent [explicit jet Fock norms](EXPLICIT_JET_FOCK_NORMS.md) replace
the infinite norm series above by `p! exp(|s|^2) L_p(-|s|^2)` and give finite
constants for the all-multiplicity ordinary residual bound. That derivation
and its adjacent-jet pairing formula remain written mathematics. Exact finite
coefficient and symbolic checks are recorded separately; no normed-space or
form-compatibility formalization is inferred from them.

## Independent finite algebra check

[check_packet_polynomials.py](check_packet_polynomials.py) independently
assembles the derivative Gram matrix and the differentiation/Jordan matrix
for six synthetic reflection-symmetric polynomials. The exact rational and
algebraic checks cover critical and off-critical roots with multiplicities
one, two and three. They verify Hermitian symmetry, operator-form symmetry,
the factor `1/m` and phase in (1), the lower bound in (2), absolute mass one,
and the paired residual identity in (4).
The saved [diagnostic record](packet_polynomial_diagnostics.json) concerns
those polynomial examples only. It does not formalize the general proof,
certify a Xi zero or support an RH claim.
