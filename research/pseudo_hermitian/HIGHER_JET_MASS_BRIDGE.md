# Higher jets and the mass bridge at every Xi zero

Arithmetic coefficient-domain and kernel-derivative milestone, 2026-10-10.
The new Lean modules establish the all-multiplicity ingredients below. The
full Fock-space pairing identification and independent paired residual estimate
remain open as formal obligations. No RH proof or simplicity claim is supplied.

## Actual-domain jets of arbitrary order

[XiHigherJetDomain.lean](../../Reinmann/XiHigherJetDomain.lean) defines the
creation action C on raw coefficient sequences by

```text
(Cc)_0=0,                    (Cc)_(n+1)=c_n,
v_s(z)=exp(sz),               J_(s,p)=C^p v_s=z^p exp(sz).
```

The checked coefficient identities are

```text
(J_(s,p))_n=0 if n<p,
(J_(s,p))_(n+p)=s^n/n!,
A Cc=C Ac+c,
A J_(s,p+1)=s J_(s,p+1)+(p+1)J_(s,p).
```

Every jet is nonzero, since its coefficient at index p is one. The order-one
jet agrees with the previously checked `coherentJet`.

For each j, let `b_(j,k)=ξ⁽ᵏ⁺ʲ⁾(0)/k!`, equivalently the Taylor coefficients
of `iteratedDeriv j xiCompleted`. The implementation uses the latter
expression, and proves the convergent entire Taylor series and the recurrence
`b_(j+1,k)=(k+1)b_(j,k+1)`. Define the derivative rows

```text
R_(j,n)(c)=Σ_(k≥0) b_(j,k) (A^(k+n)c)_0.
```

The creation commutator gives

```text
R_(j,0)(Cc)=R_(j+1,0)(c),
R_(j,n+1)(Cc)=(n+1)R_(j,n)(c)+R_(j+1,n+1)(c).
```

The checked proof establishes summability and zero sums when the rows on the
right converge to zero. It does not interchange an infinite sum with an
unproved derivative operation. Starting from the convergent coherent rows
`R_(j,n)(v_s)=s^n ξ⁽ʲ⁾(s)`, induction yields

```text
ξ⁽ʲ⁾(s)=0 for 0≤j≤p  implies  J_(s,p)∈D_ξ.
```

Here `D_ξ` is the independently defined arithmetic coefficient domain from
`XiAnnihilator`; creation is not asserted to preserve all of `D_ξ`.
Only the stated derivative vanishing conditions supply the extra rows
required by the induction.

[XiHigherJetCoupling.lean](../../Reinmann/XiHigherJetCoupling.lean) checks the
restricted operator action as well:

```text
T_ξ J_(s,p+1)=λ(s)J_(s,p+1)-i(p+1)J_(s,p),
λ(s)=-i(s-1/2).
```

Each state and lower jet appearing in that identity belongs to the actual
coefficient domain under the stated vanishing conditions. This is an
all-order Jordan-chain calculation for the existing arithmetic operator.
It does not assert Hilbert-space closure or density.

## Finite multiplicity and a nonzero kernel derivative

The same module checks that at every point s some derivative of ξ is nonzero.
Otherwise the entire Taylor series centered at s would vanish at zero,
contradicting `ξ(0)=1/2`. Taking the least such derivative index gives, at
any Xi zero ρ, a finite integer `m≥1` with

```text
ξ⁽ʲ⁾(ρ)=0 for j<m,                 ξ⁽ᵐ⁾(ρ)≠0.
```

No numerical zero list or simplicity premise enters this argument.
All-order Xi reflection and conjugation are checked, so the reflected partner
`σ=1-conjugate ρ` has the required derivative vanishing conditions too.
Consequently `J_(ρ,m-1)` and `J_(σ,m-1)` are in `D_ξ`.

For the previously defined Xi kernel H, introduce its holomorphic second
coordinate

```text
P(s,u)=H(s,conjugate u)=i dslope(ξ,1-u,s).
```

The implementation checks the alternative expression, including the removable
node,

```text
P(s,u)=-i dslope(ξ,1-s,u).
```

Uniqueness of analytic power-series coefficients gives the general identity

```text
(∂^p dslope(f,a,·))(a)=f⁽ᵖ⁺¹⁾(a)/(p+1).
```

It follows from the shifted Taylor series of the removable divided difference,
not from evaluating a quotient with a zero denominator. Combining this with
Xi reflection gives the checked formula

```text
B_(s,p)=(∂_u^p P(s,u)) at u=1-s
       =i(-1)^p ξ⁽ᵖ⁺¹⁾(s)/(p+1).
```

At `p=m-1`, this is `i(-1)^(m+1)ξ⁽ᵐ⁾(ρ)/m≠0`, agreeing with the factor and
phase in [APPROXIMATE_PACKET_MASS.md](APPROXIMATE_PACKET_MASS.md).
`zero_has_domain_jet_and_nonzero_coupling` assembles these ingredients for
**every** Xi zero. Its coupling is a derivative of the actual Xi kernel; it
is not yet a formal equality with a full Fock-space form value.

## What this closes, and what remains

The arithmetic derivative vanishing conditions, all-order coefficient jet
domain membership, Jordan action, finite multiplicity and nonzero kernel
derivative are now checked. The generic packet mass theorem was checked in
the preceding milestone:

```text
η(v,v)=0, B=η(v,w)≠0, C=η(w,w) real,
x_h=v+hBw,               0<h≤1/(1+|C|),
h|B|² ≤ η(x_h,x_h) ≤ 3h|B|².
```

To combine them formally in the full arithmetic Hilbert realization, the
remaining bridge is

```text
η_G(v_ρ,J_(σ,m-1))=B_(ρ,m-1).
```

The written proof uses boundedness of G and locally uniform Fock-norm
parameter differentiation of coherent states. The Fock construction, those
norm estimates and this compatibility identity have not been formalized or
independently reviewed. The coefficient-domain theorem does not substitute
for them.

Even after that bridge, the paired residual estimate remains necessary. At
unit absolute mass and form symmetry, the paired residual has norm exactly
`2|Re(ρ)-1/2|`. The mass construction and small ordinary residuals alone do
not make it small independently of RH.

## Preserve the weaker paired target

The norm-product sufficient criterion is optional. It must not become a new
acceptance requirement that strengthens the original objective.
[PseudoHermitianNormProductObstruction](../../Reinmann/PseudoHermitianNormProductObstruction.lean)
checks a real Jordan example with swap form η and `N(a,b)=(b,0)`:

```text
η(Nx,y)=η(x,Ny),
η(x,x)=1 with ||Nx|| arbitrarily small is possible,
d_η(x,Nx)=0 for every x,
|η(x,x)|=1 implies ||x|| ||Nx||≥1/2.
```

The checked example uses the standard coordinate product norm on `ℂ×ℂ`.
Thus a vanishing paired defect need not come from a vanishing norm product.
This synthetic example asserts nothing about actual Xi zero multiplicities.
It keeps the all-multiplicity paired reduction as the research target.

## A subsequent fixed algebraic realization

The [algebraic jet mass milestone](ALGEBRAIC_JET_MASS.md) now assembles the
previously proposed route in Lean. The all-parameter, all-order jet family is
linearly independent inside the actual coefficient space, so every finite
expansion has unique coordinates. Its arithmetic domain is the intersection
with the existing Xi row domain, invariant under coefficient differentiation.

A single Hermitianized mixed-kernel Gram form is defined on the whole span.
Its coherent-to-jet entries are checked to agree with the already verified
kernel derivatives, turning the all-zero nonzero derivative into an actual
same-form cross-pairing. The algebraic construction therefore has explicit
positive packet mass bounds in the isotropic case and unit absolute mass at
every Xi zero, including multiple zeros.

This closes a mass compatibility bridge for the algebraic model. The stronger
full Fock-space identification, norm and operator-domain claims remain written
mathematics with their separate proof obligations. Operator-form symmetry and
the required relative paired budget for the algebraic form are still unproved.
No form defined separately per zero is used, and the original paired target is
retained.

## Reproduction

```sh
lake build Reinmann.XiHigherJetCoupling Reinmann.PseudoHermitianNormProductObstruction
bash scripts/safe-verify.sh research/pseudo_hermitian/higher_jet_axiom_audit.lean
lake build
```

The separate [validation record](higher_jet_validation_2026_10_10.json) saves
source and verification-log hashes for the successful 3,544-job full build,
107-file shortcut scan and 42 theorem audits using only standard Lean axioms.
All 14 manuscript seed files match in both checkouts. Earlier records remain historical
snapshots. The manuscript seed is preserved; its PDF does not incorporate
these later operator extensions.
