# Explicit Fock norms and residual constants for every jet order

Written derivation, 2026-10-10. These formulas refine the infinite-series norm
argument in [APPROXIMATE_PACKET_MASS.md](APPROXIMATE_PACKET_MASS.md). They have
not been formalized in Lean or independently reviewed. The accompanying exact
checks cover finitely many orders and coefficients; they do not certify Xi
zeros or the remaining relative paired budget.

For `J(s,p)(z)=z^p exp(sz)`, put `r=|s|^2` and define the positive polynomial

```text
P_p(r) = sum_(j=0)^p binom(p,j) r^j/j!.
```

The exact Fock norm is

```text
M_p(s) := ||J(s,p)||_Fock^2 = p! exp(r) P_p(r).          (1)
```

Thus `M_0=exp(r)`, `M_1=exp(r)(1+r)` and
`M_2=exp(r)(2+4r+r^2)`. In particular every jet has finite, strictly positive
Fock norm, for every complex parameter and every natural order. The ordinary
Laguerre notation is `P_p(r)=L_p(-r)`; this is the alpha-zero specialization of
[NIST DLMF 18.5.12](https://dlmf.nist.gov/18.5.E12). No novelty is claimed.

## Derivation from actual coefficients

The coefficient at `k+p` is `s^k/k!`, while lower coefficients vanish. Hence

```text
||J(s,p)||^2 = sum_(k>=0) (k+p)! r^k/(k!)^2.
```

Vandermonde's finite identity gives

```text
(k+p)!/(k!)^2
  = p!/k! * binom(k+p,p)
  = p! sum_(j=0)^min(p,k) binom(p,j)/(j!(k-j)!).          (2)
```

Substitute (2) into the series and interchange the finite sum in j with the
nonnegative sum in k. For each j, the remaining shifted exponential series is
`r^j exp(r)/j!`. This proves (1), including convergence, with no approximation
and no assumption about zeros. It also avoids using a ratio test at `s=0`.

Equivalently, the same series is the p-th derivative of `r^p exp(r)`; Leibniz's
rule produces the finite polynomial in (1). That second derivation is used as
an independent symbolic diagnostic.

For any finite actual coefficient expansion `c=sum_a c_a J(s_a,p_a)`, the
triangle inequality supplies

```text
||c||_Fock <= sum_a |c_a| sqrt(M_(p_a)(s_a)).            (3)
```

The already checked injective realization prevents a nonzero finite expansion
from representing the zero coefficient sequence. These written estimates do
not yet install a normed-space instance on the Lean algebraic domain or prove
its identification with a completed Hilbert subspace.

## Adjacent-jet pairing and derivative domain

For `p>=1`, define

```text
H_p(r) = (p-1)! exp(r)
           sum_(j=0)^(p-1) binom(p,j+1) r^j/j!.
```

The Fock pairing is linear in its first argument. Direct coefficient summation
and the same Vandermonde argument give

```text
< J(s,p), J(s,p-1) > = conjugate(s) H_p(r).             (4)
```

In detail, the scalar series after removing `conjugate(s)` is
`sum_(k>=0) (k+p)! r^k/(k!(k+1)!)`; use
`(k+p)!/(k+1)!=(p-1)! binom(k+p,p-1)` and
`binom(k+p,p-1)=sum_j binom(p,j+1)binom(k,j)`.
The result remains valid at `s=0`. One can also obtain this series by dividing
the `(p-1)`-st derivative of `r^p exp(r)` by r and removing its factor r.

The actual coefficient differentiation formula is

```text
A J(s,p) = s J(s,p) + p J(s,p-1),
||A J(s,p)|| <= |s| sqrt(M_p(s)) + p sqrt(M_(p-1)(s)).   (5)
```

At p=0 the second term is omitted. Formula (1) therefore proves maximal
Fock derivative-domain membership for every finite jet expansion. Membership
in the Xi row domain still uses the separate vanishing-derivative conditions;
finite Fock norm does not imply those conditions.

## Explicit constants for all-multiplicity packets

At a Xi zero rho of multiplicity m, set `sigma=1-conjugate(rho)`, `p=m-1`,
`v=J(rho,0)` and `w=J(sigma,p)`. The checked arithmetic coefficient action
`T=-i(A-1/2)` gives

```text
R := (T-lambda(rho))w
   = -i [a J(sigma,p) + p J(sigma,p-1)],
a := sigma-rho = 1-2Re(rho),    r := |sigma|^2.
```

Thus a completely explicit finite upper bound is

```text
||R|| <= D := |a| sqrt(M_p(sigma))
                 + p sqrt(M_(p-1)(sigma)),             (6)
```

with the second term omitted at p=0. For p>=1, (1) and (4) also give the exact
squared residual norm

```text
||R||^2 = a^2 M_p(sigma) + p^2 M_(p-1)(sigma)
            + 2p a Re(sigma) H_p(r).                  (7)
```

The cross term may have either sign. Positivity follows from the norm on the
left, not from treating each displayed term as nonnegative. At p=0 the formula
is simply `||R||^2=a^2 exp(r)`.

For the same-form isotropic packet in the existing construction,
`B=eta(v,w) != 0`, `C=eta(w,w)` is real, `y_h=v+h B w`, and
`q_h=eta(y_h,y_h)`, the checked generic mass lower bound and residual identity
combine with (6) to give

```text
h |B|^2 <= q_h <= 3h |B|^2,
|| (T-lambda(rho)) (y_h/sqrt(q_h)) ||_Fock <= sqrt(h) D.
```

Given `tau>0`, any positive h satisfying

```text
h <= 1/(1+|C|),       h < (tau/(D+1))^2
```

therefore gives an ordinary residual below tau, at every multiplicity. This
refines the previously written Fock argument by replacing its unspecified
finite residual norm with finite-polynomial constants. It does not transfer
masses between different forms or assert an unverified form-compatibility
bridge. The Green recurrence implementation must pass its own checks.

The required paired residual has the independent identity
`|d(psi,(T-lambda(rho))psi)|=2|Re(rho)-1/2|` at unit absolute form mass for a
symmetric form. Equations (1)-(7) do not make this quantity arbitrarily small.
The original full objective, including that bound at every zero, remains open.

## Exact packet conditioning

For all complex s,t and all p, direct summation of the shifted coefficient
series gives the separate ordinary Fock identity

```text
< exp(sz), J(t,p) >_Fock = s^p exp(s conjugate(t)).      (8)
```

The first p summands vanish. The term at k+p is
`s^p (s conjugate(t))^k/k!`, so the remaining series is the exponential.
`HasSum` and pairing proofs are included in `XiGreenModel.lean` as
`fock_coherent_jet_hasSum` and `fock_coherent_jet_pairing`. They passed the combined
incremental Lean check with standard axioms; separate module/full-build
verification remains pending. These are Fock identities, not values of the
Green metric. The norm formulas and conditioning limits themselves remain
written mathematics.

For `y_h=v+h B w`, (8) makes its Fock norm completely explicit:

```text
||y_h||^2 = ||v||^2 + 2h Re(conjugate(B) <v,w>_Fock)
                        + h^2 |B|^2 ||w||^2.
```

Combine this with `q_h=|B|^2 h(2+h C)` and
`r_h=h B R/sqrt(q_h)`. As h decreases to zero through positive values,

```text
h ||psi_h||^2 -> ||v||^2/(2|B|^2),
||r_h||^2/h   -> ||R||^2/2,
||psi_h|| ||r_h|| -> ||v|| ||R||/(2|B|).                (9)
```

These limits follow by substituting the displayed exact formulas into the
quotients; their denominators tend to nonzero values because B is nonzero.
For a hypothetical multiple critical-line zero, p>=1 and
`R=-i p J(rho,p-1) != 0`, so the last limit is strictly positive even though
the paired residual is zero. No such multiple zero is asserted to exist.
Thus shrinking h is not an argument for the stronger norm-product criterion.
It remains useful for the ordinary residual estimate, and the full original
paired requirement remains the research target. The conditioning limits are
written derivations, not results of the finite diagnostic script or Lean checks.

## Reproduction and diagnostic scope

```sh
python3 research/pseudo_hermitian/check_jet_fock_norms.py
```

The script compares the finite polynomial formulas with independently
symbolically differentiated exponentials and checks their coefficient
convolutions using exact rational arithmetic. Its saved record states the
finite orders tested. It is neither a general formal proof nor a verification
of the Green-form implementation.

## Unchecked summability implementation

`FockJetSummability.lean.draft` implements five candidate lemmas for the actual
factorial-weighted coefficient series at every complex parameter and jet order.
It is excluded from the verified module tree and has not been compiled. For
`W_k=(k+p)! r^k/(k!)^2`, it uses the exact recurrence
`W_(k+1)=((k+p+1)r/(k+1)^2)W_k`. Taking an integer N greater than 4r gives a
ratio at most one half for every `k>=max(p,N)`. This domination remains valid
at r=0 and does not divide by W_k. A shifted-coefficient identity then transfers
summability to the actual `higherJet` sequence.

After that draft passes its checks, the intended next bridge is the injective
weighted coefficient map `c_n -> sqrt(n!) c_n` into ordinary square-summable
sequences. The existing arithmetic action and the same Green form must be
transported through that map, preserving all parameters and jet orders. This
does not by itself prove closedness on the full Hilbert domain, boundedness of
the Green form, or the arbitrarily small paired budget. Those requirements are
not replaced by a norm-product condition.
