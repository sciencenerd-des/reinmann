# Positive atomic representation in the corank-one Toeplitz case

`Reinmann/ToeplitzSimpleRoots.lean` and `Reinmann/ToeplitzAtomic.lean`
continue the finite kernel-root theorem. They prove simple roots and a
positive atomic representation for every complex PSD Toeplitz matrix of
size n+1 and rank n. The representation is constructed, not assumed.
This is a formalization of a known special case of Carathéodory–Fejér;
no mathematical novelty or arithmetic positivity is claimed.

The earlier kernel theorem and its CI integration were committed as
`0f073e0`. This follow-up preserves those proof and verification files.

## Exact result

`Reinmann.ToeplitzAtomic.exists_atomic_representation` assumes only:

- `T.PosSemidef`, including Hermitian symmetry;
- the original simultaneous-shift Toeplitz convention;
- `T.rank = n` for a matrix indexed by `Fin (n+1)`.

It proves `HasAtomicRepresentation T n`: there are a finite set S of
exactly n complex numbers and real weights w such that every z in S has
norm one, every w(z) is strictly positive, and

\[
T_{ij}=\sum_{z\in S} w(z)\,\overline{z^i}\,z^j
\qquad(0\le i,j\le n).
\]

The finite set ensures distinct nodes. No kernel vector, root list,
separability, moment representation or positive weights are additional
hypotheses. Rank-nullity supplies a nonzero kernel vector internally.
The n=0 case is included with the empty support and the zero matrix.

The original coefficient convention remains ordinary ascending complex
coefficients, padded to n+1. These are Hermitian two-sided Toeplitz
matrices, not one-sided Taylor-coefficient/Pólya-frequency matrices.

## Proof chain

1. Any nonzero polynomial of degree below n has strictly positive Toeplitz
   energy. Zero energy would put it in the kernel, contradicting the
   previously proved full-degree theorem.
2. Kernel roots are simple. Suppose p=(X-z)q and q=(X-z)r. The mixed
   shift identity B(Xr,Xq)=B(r,q), the kernel relation T(Xq)=zTq,
   and |z|=1 imply z Q(q)=0. This contradicts positive short energy.
   Lean states the result as nonzero derivative at every root, then
   separability and exactly n distinct unit-circle roots.
3. Let S be that root set and let L_z be its Lagrange basis polynomials.
   Each L_z has degree below n and is nonzero. The polynomial
   (X-z)L_z vanishes at every point of S and has degree at most n,
   so it is a scalar multiple of p and lies in the kernel.
4. Toeplitz mixed-shift invariance makes L_z and L_u orthogonal for
   distinct nodes. The factor is conjugate(z)*u, which differs from one
   for distinct unit-circle nodes.
5. For a polynomial a of degree at most n, its Lagrange interpolant I(a)
   differs from a by a kernel polynomial. Hence
   B(a,b)=sum_z conjugate(a(z))*b(z)*Q(L_z).
6. Q(L_z) is real and strictly positive. Define w(z)=Re Q(L_z), and
   specialize the preceding identity to a=X^i and b=X^j.

The mixed-pairing argument and the Lagrange expansion are proved in Lean.
No numerical root computation or sampled positivity is used.

## Scope

This completes the positive atomic representation for the corank-one
case. The theorem for arbitrary rank r in a matrix of size n+1,
including the full-rank case, is still unformalized here. No uniqueness
of the representation is claimed in this follow-up.

It remains shared finite linear algebra, valid for any DH-derived matrix
satisfying the same hypotheses. It provides no zeta/DH-specific PSD
estimate, no arithmetic discriminator and no active RH strategy.

## Build and audit integration

Both modules are imported by `Reinmann.lean` and `Reinmann/AxiomAudit.lean`.
Eight explicit axiom checks cover the five simple-root/energy theorems
and the three atomic-weight/representation theorems. All project audit
imports remain root imports.

The default `lake build` succeeds (3,997 jobs). The axiom-clean script
passes with 2,655 audited theorem reports, zero sorry and zero custom
axioms. These are local checks on dirty sources over `0f073e0`; no remote
CI job is claimed. The exact statements, standard-axiom probe, historical
replays and source hashes are recorded in
`verification_2026_11_01_toeplitz_simple_roots`.

```sh
lake build
bash scripts/verify_axiom_clean.sh
python3 experiments/prime_spectral/check_dh_research_gate.py
python3 research/prime_spectral/verification_2026_11_01_toeplitz_simple_roots/validate.py
```

The new packet replays the seven earlier packets against their historical
source bytes and preserves all 1,883 earlier verification files unchanged.
Fresh-kernel replay passed with 5,555 modules and
22,214 compiled/metadata files bound and
unchanged. It uses Lean's own checker, not an independent verifier. Its compiled-input receipt reuses the original immutable baseline
and records only additions, avoiding duplicate copies of those hash lists.
