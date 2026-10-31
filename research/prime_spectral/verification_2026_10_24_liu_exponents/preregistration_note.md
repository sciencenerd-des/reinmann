# Liu exponent system: direction 2, 24 October 2026

Status at start: scalar reconstruction and sensitivity audit, not a new
Hecke-family estimate or zero-free theorem. The DH register was updated
before development. The parked row-density route is not restarted.

## Source and intended checks

Use [Liu v2](https://arxiv.org/html/2610.12234v2), including Parts IV and
section 34, rather than identifying v1's fixed-moment endpoint with v2's
variable-moment fixed point. Source archive downloaded from
`https://arxiv.org/src/2610.12234v2`, SHA-256
`da1db207bb54437245c4fff75f33cfb29088f32f57e6364a6b3b955bc3372204`.
The source is held in temporary storage, not vendored into this repository.

Reconstruct the supplied count by optimizing the separate moment bounds
on the SAME detector class, not by treating their upper exponents as lower
bounds on actual character counts. Reproduce 7/8, the fixed-kappa algebraic
bound, and the variable-moment endpoint. Exact rational/symbolic identities
and real-algebraic root isolation should support the reconstruction;
floating parameter optimization alone is insufficient.

The arithmetic uses ideal norms in Q(sqrt(-3)), an inverse polynomial with
ideal Mobius coefficients and an unweighted polynomial, both twisted by one
common sextic/ray character. Normalized sums of length U^r and U^m have
simultaneous squared large values U^(delta*r) and U^(delta*m).
Selected prime products of total length U^z contribute squared amplitude
U^(2*delta*x*z), where delta=2a-1 and 0<=x<=1/2. Keep conductor, deleted
Euler factors, coefficient and common-character restrictions explicit.

The original inverse moment has constraints r+2z<=1 and 2r+8z<=3;
the unweighted fourth moment has 2m+6*kappa*z<=1. These are closure
inequalities of strict analytic ranges, not permission to apply the
analytic estimates exactly at equality. The amplified long inverse count
has exponent 1-alpha+(alpha-delta)*r, alpha=5/6. Parameter changes are
hypotheses for sensitivity calculations, not newly proved estimates.

Before any conjectural substitution, retain the full direct majorant in
Liu (22.4)-(22.6), not just B=11/12-ell/4. In particular the support
conditions l_x,l_y>ell already exclude the formal ell=5/3 RH substitution.
Check the exact direct-side minimization even after **deleting all
nonprincipal-count inequalities**, a relaxation stronger than improving
those counts by any large-value conjecture. Do not call the relaxed
optimum an achieved conditional zero-free bound.

The candidate inequality for arithmetic development is a genuinely smaller
uniform exponent for the same simultaneous detector/prime-product class,
with the original ideal coefficients, supports, coprimality and height
dependence. The DH global half-plane analogue is false by the retained
classical theorem; b_91-b_7*b_13=-1-kappa_DH^2 refutes the needed reciprocal
multiplicativity transfer. A corresponding new DH moment implementation
is absent, so the route remains uninstantiated as an analytic strategy.

## Large-values transport audit

Use the [published Guth–Maynard theorem](https://annals.math.princeton.edu/2026/203-2/p06)
and [Chen–Gupta–Li v2](https://arxiv.org/html/2507.08296v2) as primary
sources. Their ordinary integer Dirichlet-polynomial/Dirichlet-character
families must not be identified with Liu's varying-conductor ideal sextic
family. A statement about a varying real height is not a count over u.
Record both raw-amplitude normalization and conductor/range compatibility.

A dedicated prior-art search has already located public discussion of the
direct-side 13/15 LP floor. That is a lead against novelty, not a technical
premise. The mathematical ledger will be derived from Liu's primary
equations, and no novelty claim is made for a resulting barrier.

Results, verification commands and explicit remaining gaps will be appended
after the reconstruction runs.
