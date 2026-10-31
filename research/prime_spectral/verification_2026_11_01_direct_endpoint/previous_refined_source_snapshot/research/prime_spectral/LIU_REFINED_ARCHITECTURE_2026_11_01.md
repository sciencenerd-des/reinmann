# Refined numerator comparison: retained direct-side floor (1 November 2026)

**Outcome:** the Xu–Sang/Liu averaged-numerator refinement retains the direct
comparison whose count-free floor is **13/15 > 1/2**. The 1 November review's
suggestion that this floor may disappear with the numerator change was
incorrect: the change concerns the high-side reflected numerator. This is
an exact scalar reconstruction and a correction to our review, with no new
analytic theorem, RH claim, or novelty claim.

## Sources and reproduction scope

- [Xu–Sang, 2610.15291v2](https://arxiv.org/html/2610.15291v2): Section 3
  (low bound, its normalization and rescaled-subset decay), Section 6
  (high-side exponent and admissibility), Section 7 and Appendix D (two
  rational stages).
- [Liu, 2610.26835v2](https://arxiv.org/html/2610.26835v2): Section 2.4
  (free-length direct majorant), Section 14.1 (refined exponents), Section
  14.7 (critical class and quartic), Section 14.8 (the specified comparison
  system explicitly retains balanced lengths and ell <= 1/5), and the
  appendix headed “These certificates check the scalar inequalities only;
  they do not verify the analytic estimates.”
- A dedicated prior-art lookup found the same Xu–Sang 13/15 floor in the
  discussion of the [17 October rStation post](https://rstation.ai/r/riemann_hypothesis/posts/15).
  We use the preprints for the mathematical reconstruction; the discussion
  establishes that the observation has already been stated publicly. Its
  other numerical experiments are not validated here.
- Liu's bibliography identifies Newton as *Prime Errors and the
  Quasi-Riemann Frontier: A Certified Conditional Boundary and Its
  Parameter-Optimization Barrier*, 16 October 2026,
  [DOI 10.5281/zenodo.23414581](https://doi.org/10.5281/zenodo.23414581).
  The DOI was located through that bibliography; its full text was not
  retrieved. No independent Newton regression or exhaustive novelty search
  is claimed.

The versioned source archives were downloaded and fingerprinted. See
`verification_2026_11_01_refined_architecture/source_provenance.json`.
Analytic moment estimates, field descent, Liu's full tangent-family and
global optimality proofs, and Lean proofs are not independently replayed.

## The precise relaxation

The DH register and accompanying note were clarified before development;
the clarification is preserved in the new verification packet.

Delete **every high-side constraint**, including counts, numerator moments,
small-row and detector-floor bounds, principal-assembly restrictions, and
bootstrap licensing. Retain the direct comparison and its signal
normalization. This contains every model obtained by changing only those
high-side inputs while retaining the same direct majorant. It does not
assert R=0, a new Lindelof estimate, or an optimum for a full idealized
analytic system. The retained low-side Gram and reflected-energy estimates
are substantive inputs, not merely support geometry.

The minimum of this relaxation is 13/15. Consequently any more constrained
idealization retaining that direct side has boundary at least 13/15.
Its exact full optimum may be larger and has not been computed. The
lower bound already settles the question of reaching 1/2 in this scope.

## Two exact certificates

For balanced lengths,

\[
l_x=(1-b-\ell)/2,\quad l_y=(1+b-\ell)/2,\quad
B(\ell)=11/12-\ell/4.
\]

Both refined sources retain ell <= 1/5. Thus

\[
B(\ell)-13/15=(1/5-\ell)/4\ge0.
\]

Even formally removing that cap does not justify extrapolating B(ell):
the existing balanced full direct majorant includes
`(5*ell-1)_+/8` (and a nonnegative Gram penalty). For ell >= 1/5,

\[
11/12-\ell/4+(5\ell-1)/8
=13/15+(3/8)(\ell-1/5)\ge13/15.
\]

An independent certificate allows free total length M = l_x+l_y. The
retained maximum is

\[
k(M,\ell)=\max\{0,(1+3\ell-2M)/4,M+\ell-1,(3\ell-1)/2\},
\]

\[
B_{\rm low}=5/6+l_x/6-\ell/6
 +\max\{0,b/12,b-l_y/2\}+k(M,\ell)/2.
\]

Since the Gram maximum is at least b/12 and b=l_y-l_x, define

\[
L_0=5/6+M/12-\ell/6,\quad
L_1=L_0+(1+3\ell-2M)/8,\quad
L_2=L_0+(M+\ell-1)/2.
\]

Each L_i is at most B_low, and the positive rational dual is

\[
\frac{17}{30}L_0+\frac25L_1+\frac1{30}L_2=\frac{13}{15}.
\]

The weights sum to 1. The primal `(lx,ly,ell)=(7/20,9/20,1/5)` satisfies
the direct geometry and gives exactly 13/15. It is a witness for the
**direct-only relaxation**, with no claim that it satisfies the discarded
high-side or assembly conditions. The gap to 1/2 is 11/30. Finite chains
and limits of their boundaries retain this lower bound.

## Refined endpoint regressions

We reconstruct the full-capacity endpoint using **c=1/(3*kappa)**. The
older ledger uses twice this c in its count notation; confusing them
changes the endpoint. With delta in [0,5/6], x in [0,1/2],

\[
D=3-(1+2c)x,\quad P=(2-2cx)(1-x),\quad
J=(5/6-\delta)D+\delta P,
\]

\[
R=1-\delta+\frac{(5/6-\delta)\delta P}{2J},\quad
C_0=-1/4+b/6+5\ell/4,
\]

\[
E=C_0+\delta/2+\delta x\{\ell+c(h/4-l_y/2)\}
 -(3h/4)(1-R).
\]

The independently written full row-scale exponent reduces symbolically to
this expression at d=h. For each published rational stage the code
regenerates `2*J*(-E-margin)=A(y)*delta^2+B(y)*delta+C(y)`, y=1/2-x,
and verifies positive coefficients of A and 4AC-B^2. Completing the square
certifies the entire rectangle. All remaining stated scalar reserves are
positive; the code also constructs a positive row-extension margin.

| Stage | Licensed by previous boundary | New boundary |
| --- | --- | --- |
| 0 | 7/8 | 69991/80000 = 0.8748875 |
| 1 | 69991/80000 | 8748867/10000000 = 0.8748867 |
| 2 | 8748867/10000000 | 87488664725/100000000000 |
| 3 | 87488664725/100000000000 | 874886647041/1000000000000 |

The first two regenerated polynomial triples agree coefficient by
coefficient with Xu–Sang Appendix D, including its scale factors. Every
stage uses kappa=2*B_previous-1, rather than assuming its own conclusion.

For the algebraic endpoint, we verify Liu's critical-class derivative
identity, eliminate delta at ell=5/3-2*kappa, and derive

\[
16686\kappa^4-27405\kappa^3+9936\kappa^2+1290\kappa-275=0.
\]

Substitution kappa=2B-1 gives twice

\[
133488B^4-376596B^3+384534B^2-167541B+26231=0.
\]

Exact root isolation gives
`B = 0.8748866470399641309446140005301806494988849618898974...`.
A subresultant recovers the common critical delta and bounds it strictly
between 23/50 and 12/25; this rejects confusing the relevant solution with
the quartic's other root in the broad kappa range. This is an algebraic
regression, **not a reproduction of Liu's full optimality theorem**.

## DH status and next work

No positivity inequality or new arithmetic estimate is proposed. This
scalar method barrier needs no DH moment implementation. It excludes RH
through high-side family-input improvements **with the retained direct
side**; it does not exclude a different direct estimate, normalization, or
future cubic-theta method. Those would require a fresh, precise target and
the existing DH gate before arithmetic development.

The endpoint branch is closed within that frozen scope. The broader
register entry stays `uninstantiated`, since its conditional arithmetic
targets and replacement DH moment family are still unproved/unimplemented.
Directions B and C remain optional finite-strengthening work. No stopped
row-density scan was restarted, and no specialist correspondence was sent.

## Reproduce

From the repository root:

```sh
python3 experiments/prime_spectral/liu_refined_architecture.py
python3 -m unittest discover -s experiments/prime_spectral -p 'test_liu*.py' -v
python3 experiments/prime_spectral/check_dh_research_gate.py
python3 research/prime_spectral/verification_2026_11_01_refined_architecture/validate.py
```

The JSON receipt records scalar identities, polynomial coefficients,
positive margins, and exact root brackets. Validation is local against the
recorded dirty working tree; no CI or committed proof-chain receipt is
claimed. Earlier verification packets are fingerprinted and checked for
changes; their manifests are not edited.
