# A fixed algebraic Xi jet space and its packet masses

Status: Lean checked, 2026-10-10. This construction
addresses same-form mass compatibility on an algebraic coefficient domain.
It does not yet establish operator-form symmetry or the relative paired budget
needed for RH. The separate full Fock-space arguments remain written proofs
without formalization or independent review.

## Space, action and arithmetic domain

Let `J(s,p)` be the coefficient sequence of `z^p exp(sz)`. Take the ambient
complex vector space

```text
E = span { J(s,p) : s in C, p in N } inside C^N.
```

The parameters range over all complex numbers, independently of the Xi zero
set. Jets at a fixed parameter are linearly independent by their triangular
coefficient matrix: `J(s,p)_n=0` for `n<p` and `J(s,p)_p=1`. Jets at distinct
parameters belong to independent maximal generalized eigenspaces of coefficient
differentiation `A`. Consequently the full jet family is linearly independent,
and each state of `E` has unique finite coordinates.

The action is the restriction of the previously defined coefficient operator
`(Ac)_n=(n+1)c_(n+1)`, with

```text
A J(s,p+1) = s J(s,p+1) + (p+1) J(s,p).
```

The arithmetic domain is `D = E intersect D_Xi`, where `D_Xi` is the existing
independently defined domain of summable, vanishing Xi Taylor rows. In particular,
the restriction to `E` does not change the arithmetic row equations. This domain
is invariant under `A`; use `T=-i(A-1/2)` on `D`. Its coherent state `v_s=J(s,0)`
is a nonzero exact eigenstate with eigenvalue `lambda(s)=-i(s-1/2)` when `Xi(s)=0`.

See [XiAlgebraicJetSpace.lean](../../Reinmann/XiAlgebraicJetSpace.lean).

## One fixed Hermitian form

Use the polarized Xi divided difference

```text
P(s,u) = i dslope(Xi,1-u)(s),
H(s,t) = P(s,conjugate(t)).
```

The divided difference includes its removable diagonal value. On every pair of
jet labels, define

```text
R((s,p),(t,q)) = d_s^p d_u^q P(s,u) at (s,conjugate(t)),
K(a,b) = (R(a,b) + conjugate(R(b,a))) / 2.
eta(c,d) = sum_(a,b) c_a conjugate(d_b) K(a,b).
```

Both sums are finite. Hermitian symmetry is built into `K` once on all labels;
there is no per-zero choice of form. Unique finite coordinates transport this
additive sesquilinear form to the actual coefficient space and then to `D`.
This construction does not require a norm, a completion or a bounded operator
representing the form.

Hermitianization preserves the coherent-to-jet entries. Conjugation of
holomorphic derivatives, together with Hermitian symmetry of `H`, gives

```text
K((s,0),(t,p)) = d_u^p P(s,u) at u=conjugate(t).
```

The previous all-order kernel calculation therefore becomes an actual value
of this single form, rather than only a parameter-derivative identity:

```text
eta(v_s,J(1-conjugate(s),p))
  = i (-1)^p Xi^(p+1)(s)/(p+1).
```

At a zero of finite multiplicity `m`, put `p=m-1`. All derivatives through
order `p` vanish at the reflected partner, so that jet belongs to the same
arithmetic domain `D`; the displayed cross pairing is nonzero. The previous
entire-function argument proves finite multiplicity at every Xi zero using
`Xi(0)=1/2`. No RH, simple-zero assumption or finite zero sample enters this
construction.

See [XiAlgebraicJetForm.lean](../../Reinmann/XiAlgebraicJetForm.lean).

## Explicit masses and residuals

Write `v=v_s`, choose the partner `w` above, and let `B=eta(v,w) != 0`.
If `eta(v,v)=0`, Hermitian symmetry makes `C=eta(w,w)` real. For
`0<h<=1/(1+abs(C))`, the same form gives

```text
x_h = v + h B w,
q_h = eta(x_h,x_h) = abs(B)^2 (2h+h^2 C),
h abs(B)^2 <= q_h <= 3h abs(B)^2,
psi_h = x_h/sqrt(q_h),
eta(psi_h,psi_h) = 1.
```

All states remain in `D`. The exact residual identity also uses the same action:

```text
(T-lambda(s))psi_h = h B/sqrt(q_h) (T-lambda(s))w.
```

No residual norm estimate on this algebraic space is asserted. If `eta(v,v)`
is nonzero, normalizing `v` by `sqrt(abs(eta(v,v)))` gives absolute mass one
directly. Thus every Xi zero supplies a nonzero actual-domain state of absolute
mass one, with the isotropic case accompanied by the explicit packet lower
bound and residual formula.

See [XiAlgebraicMass.lean](../../Reinmann/XiAlgebraicMass.lean).

## Remaining proof obligation

`ArithmeticUnitMassPairedBudget` names the unresolved condition on this fixed
form and action: at each critical-strip zeta zero and every positive `epsilon`,
there is a state of absolute mass one with

```text
abs(d(psi,Tpsi)) + abs(d(psi,(T-lambda(s))psi)) <= 2 epsilon,
d(x,y) = eta(y,x)-eta(x,y).
```

The conditional theorem
`riemannHypothesis_of_arithmetic_unit_mass_paired_budget` plugs that premise
into the existing local reduction. It does not prove the premise, and the mass
witnesses above have not been shown to meet it.

Hermitian symmetry of a form is distinct from symmetry of the action relative
to that form. The construction above has not yet proved
`eta(Tx,y)=eta(x,Ty)` on `D`, nor an estimate on its defect. The analytic Fock
symmetry argument cannot simply be assigned to the new form without a bridge.

The required RH reduction still asks, at each critical-strip zero and each
positive tolerance, for a state with nonzero mass and a relative paired budget
for the action defect and residual defect. Unit absolute mass and the residual
identity alone do not provide that budget. No norm-product requirement is
substituted for the weaker paired condition, and multiple zeros remain in scope.

The next algebraic target is a Green identity for the jet Gram entries and the
Xi row functionals. On the arithmetic domain its boundary term would vanish.
Even after action symmetry is checked, the independent relative residual bound
would remain an RH-strength obligation.

For labels `(s,p)` and `(t,q)`, the proposed Green identity is

```text
-i(s+conjugate(t)-1) K_(p,q)
  - i p K_(p-1,q) - i q K_(p,q-1)
= [q=0] Xi^(p)(s) - [p=0] conjugate(Xi^(q)(t)).
```

Terms with a zero prefactor are omitted. For the raw mixed-derivative Gram
matrix, this is the differentiated divided-difference identity. At reflected
parameters `t=1-conjugate(s)`, the expected confluent value is

```text
R_(p,q) = i (-1)^q p! q! Xi^(p+q+1)(s)/(p+q+1)!.
```

The last formula agrees with the already checked coherent-to-jet entries, but
its full mixed-order version is not yet a Lean theorem here. One can approach
the Green calculation by proving these mixed derivatives, or construct a
separate universal Gram matrix by the Green recurrence away from the reflected
locus and the confluent formula on that locus. The latter would require its own
fixed-form mass compatibility checks; it must not inherit them merely by name.

After finite expansion, the proposed boundary term is
`R_0(c) conjugate(d_0) - c_0 conjugate(R_0(d))`, where `R_0` is the zeroth Xi
row. Hermitianization preserves this term because it is skew Hermitian under
exchange of `c,d`. Vanishing arithmetic rows would therefore remove it on `D`.
These are written derivations and next proof targets, not checked action-symmetry
claims for the current module.

## Reproduction

```sh
lake build Reinmann.XiAlgebraicMass
bash scripts/safe-verify.sh research/pseudo_hermitian/algebraic_mass_axiom_audit.lean
lake build
```

The manuscript seed files remain separate from this research extension. The
copied manuscript PDF does not incorporate these new algebraic modules.

The [validation record](algebraic_mass_validation_2026_10_10.json) records the
full project build, 110-file shortcut scan, 35 standard-axiom theorem audits
and source/log hashes. All 14 manuscript seed files match in both checkouts.
Earlier validation records remain historical snapshots.
