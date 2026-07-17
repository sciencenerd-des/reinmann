# New Mathematics Frontier for RH

**Date:** 2026-07-17
**Status:** research hypotheses and proof targets, not proved mathematics.

The committed Lean surface now has two exact-ready routes:

1. **Kernel/PF route:**
   `riemannHypothesis_of_effectiveCertificates`.
   The remaining input is `KernelEffectiveCertificates M`: a strict finite
   prefix plus an explicit remainder bound for every order.
2. **Jensen/HPSS route:**
   `riemannHypothesis_of_hpss_route`.
   The remaining inputs are `HermitePoulainSchurSzegoTheorem`,
   `XiJensenCoeffHyperbolic`, and the classical `PolyaJensenBridge`.

No route contains an axiom or a hidden RH-equivalent field.

## What the papers actually add

### 1. Saddle-point asymptotics are more explicit than the current interface

O'Sullivan's [Jensen-polynomial asymptotics](https://arxiv.org/abs/2007.13582)
gives explicit Lambert-\`W\` expansions and an exponentially small secondary
term for the Xi coefficients.  In particular, the paper records a full
expansion of the form

```text
b_(2n) = main(n) * (1 + sum_{k<K} tau_k(W(...))/n^k
                    + O(W(...)^(3K)/n^K)).
```

The new Lean mathematics needed is not another limit theorem.  It is a
remainder compiler:

```text
XiMomentExpansion K n
  -> XiOrder3ScaledLowerBound N L
  -> KernelMinorTailStrict M 3 (N + 2)
```

The first target should be `K = 2` or `K = 3`, with all constants represented
as rational intervals and the Lambert-\`W\` inequalities isolated in reusable
lemmas.

### 2. The continuous-kernel PF route has a hard obstruction

The recent certified computation
[Michałowski, PF order of the de Bruijn--Newman kernel](https://arxiv.org/abs/2602.20313)
finds a negative order-5 Toeplitz minor while orders 2--4 remain positive at
the same configuration.  This does not disprove positivity of the discrete
Xi moment sequence, but it rules out the tempting shortcut

```text
continuous de Bruijn--Newman kernel is PF_infinity
  -> all discrete Xi minors are positive.
```

The viable replacement is a **discrete transfer theorem**: prove total
positivity directly for the factorial-weighted moment sequence, or identify a
different transform that preserves the required minors without inheriting the
continuous PF5 obstruction.

### 3. Jensen asymptotics suggest a Hermite-cone criterion

GORZ and the effective Xi paper establish eventual fixed-degree hyperbolicity
through Hermite models ([GORZ](https://arxiv.org/abs/1902.07321),
[Xi-effective](https://arxiv.org/abs/1910.01227)).  O'Sullivan also gives a
criterion in terms of linear combinations of Hermite polynomials.  This points
to a route weaker than the full HPSS theorem:

```text
explicit Hermite-basis coefficients + a root-separation margin
  -> hyperbolicity of the finite Jensen window.
```

The exact proposition to investigate is a certified perturbation theorem for
the Hermite basis.  If `H_d` has separated real roots and the coefficient
perturbation is bounded below the corresponding discriminant/root-separation
margin, then the perturbed Jensen window remains hyperbolic.  The open Xi input
would then be an explicit uniform perturbation bound, rather than an assertion
that every coefficient window is hyperbolic by definition.

### 4. Heat-flow reformulation gives a third diagnostic, not a shortcut

Rodgers--Tao prove the de Bruijn--Newman constant is nonnegative
([paper](https://www.cambridge.org/core/journals/forum-of-mathematics-pi/article/de-bruijnnewman-constant-is-nonnegative/D4B85BA067E2D5A71D87E4FFB0D21E46)).
Since RH is equivalent to the opposite inequality `Lambda <= 0`, a new proof
would need a strict heat-flow rigidity principle forcing `Lambda = 0`.  A
promising exact target is a quantitative implication of the form

```text
finite Xi zero-spacing/energy inequality
  -> no positive heat-flow time can be the first real-rooted time.
```

This is independent of the PF/Jensen routes and should be used as a
falsification cross-check, not silently substituted for either open input.

## Prioritized research program

1. Translate O'Sullivan's coefficient expansion into interval-valued Lean
   bounds for `XiCoeff`; close the normalized order-3 tail first.
2. Prove the Hermite root-separation perturbation lemma and test whether the
   effective Xi error terms satisfy it uniformly on a growing `(d,n)` window.
3. Search for a discrete moment transform or planar-network representation that
   bypasses the continuous-kernel PF5 obstruction.
4. Formalize a heat-flow rigidity proposition and compare its hypotheses with
   the existing zero-spacing and energy targets.

These are genuine mathematical subproblems. Numerical positivity, fixed-degree
asymptotics, or a proposition that is merely equivalent to RH cannot be promoted
as a proof.
