# A smaller prime-form allowance from finite translation chains

The prime-form bound can retain support geometry before summing over
prime powers. The resulting written estimate is uniform in Fourier rank
and in `17<=C<=19`, and reduces the earlier high-mode starts from
`18,612,929` to `117,259` in the even sector and from `60,879,750` to
`383,530` in the full sector. The finite Hilbert-space chain inequalities
and their integrated L² counterparts are Lean-proved. The support-to-fiber
decomposition, complex autocorrelation normalization, complete prime-power
enumeration and uniform prime integral estimate are also now Lean-proved in
[SupportTranslation.lean](../../Reinmann/SupportTranslation.lean) and
[SupportPrimeForm.lean](../../Reinmann/SupportPrimeForm.lean). The archimedean
coercivity specialization remains a written proof. Numerical endpoints are
evaluated with Arb; the Lean allowance is an exact expression in logarithms
and square roots, without a decimal enclosure imported as a hypothesis.

This does not give positivity of the intermediate block, a constrained
inverse bound, convergence to Xi, or order-three Xi positivity.

## 1. Three chain inequalities proved in Lean

For vectors in any real inner-product space, the following hold:

```
2 |<x0,x1>| <= ||x0||²+||x1||²;
2 (|<x0,x1>|+|<x1,x2>|) <= sqrt(2) sum_(j=0)^2 ||xj||²;
2 sum_(j=0)^3 |<xj,x(j+1)>| <= sqrt(3) sum_(j=0)^4 ||xj||².
```

These are `chain_two`, `chain_three`, and `chain_five` in
[FiniteShiftChains.lean](../../Reinmann/FiniteShiftChains.lean).
Zero padding covers shorter chains. The underlying weighted edge inequality
is also proved there:

```
2t |<x,y>| <= t²||x||²+||y||²,  t>=0.
```

The same module now proves `l2_energy` and `integrated_chain_two`,
`integrated_chain_three`, `integrated_chain_five` for arbitrary L² families
and arbitrary measures. These are genuine Bochner integral estimates:
the inner product in L² equals the integral of the pointwise inner product,
and its squared norm equals the integral of the pointwise squared norm.
Integrability comes from L² membership. This closes the integrated-family
step. The interval translation is now identified with its fibers by the
Lean decomposition in Section 2.

For length three, apply it with `t=sqrt(2)` at both ends and add. For
length five, use `t=sqrt(3)` at the outer edges and `t=sqrt(3)/2` from
the middle coordinate toward both neighbors. Doubling the latter two
inequalities allocates exactly the same total energy to all five
coordinates. This retains the shared middle coordinate instead of
estimating each translation using a separate full norm.

The constants are the path adjacency constants
`2 cos(pi/(m+1))` for `m=2,3,5`. This is classical finite-chain geometry,
not a claim of a new numerical-radius theorem. The general nilpotent
contraction theorem is Haagerup–de la Harpe, *The numerical radius of a
nilpotent operator on a Hilbert space*, Proc. Amer. Math. Soc. 115 (1992),
371–379; consult the
[original article in the author's institutional archive](https://access.archive-ouverte.unige.ch/access/metadata/2e3d55fc-f7d2-42af-95ae-6c06df864dbb/download)
for the general result and bibliographic identifier. Our three cases are
proved directly in Lean without importing that theorem.

## 2. Translation disintegration: Lean proof

Let `f` be square-integrable on `[0,L]` and zero outside it. Let `t>0`
and assume `L<=m*t`. Define the autocorrelation

```
F(t) = integral_R conjugate(f(x-t))*f(x) dx.
```

Partition the real line into translates of `[0,t)`. For almost every
`s in [0,t)`, the sequence `f(s+k*t)` has nonzero entries only at
`k=0,...,m-1`. The upper endpoint, when `L=m*t`, is a null set and adds
no extra coordinate. Thus

```
||f||² = integral_0^t sum_(k=0)^(m-1) |f(s+k*t)|² ds,
F(t)  = integral_0^t sum_(k=0)^(m-2)
            conjugate(f(s+k*t))*f(s+(k+1)*t) ds.
```

The integrals exist by Cauchy–Schwarz. Apply the chain inequality to
the fibers, then integrate. For complex fibers use their real Hilbert
structure, whose inner product is `Re(conjugate(x)*y)`. Taking the
absolute value of the real sum and then using the triangle inequality
gives, for `m=2,3,5`,

```
|F(t)+F(-t)| = |2 Re F(t)| <= k_m ||f||²,
k_2=1, k_3=sqrt(2), k_5=sqrt(3).
```

If `L<=t`, the overlap is null and the constant is zero. This argument
applies to every supported `L2` function, not just finite Fourier vectors.
It therefore gives a rank-independent form estimate. `energy_disintegration`
and `correlation_disintegration` prove the exact partitions using Mathlib's
Lebesgue translation invariance and adjacent interval-integral identities.
`translation_bound` proves the integral estimate; `translation_disjoint`
covers the no-overlap case. The assumptions are L² membership and support
almost everywhere in the closed interval. The endpoint values are never set
to zero, and these theorems do not provide a bound for endpoint traces.

`complexCorrelation_translate`, `complexCorrelation_neg`, and
`paired_complexCorrelation` prove the original complex normalization:
`F(t)+F(-t)=2 Re F(t)`, as an equality in the complex numbers. Commuting real
part with the integral uses proved integrability of the L² product, rather
than relying on the totalized integral of a possibly nonintegrable function.

## 3. Application to every prime power in the support cell

The prime form is

```
<f,S f> = sum_(q=p^a<C) (log p)/sqrt(q) * (F(log q)+F(-log q)).
```

For `L=log C<=log 19`, the chain lengths follow from integer inequalities:

| Prime power | Guaranteed chain length | Form allowance |
|---|---|---|
| `q=2` | `5`, since `19<2^5` | `sqrt(3)` |
| `q=3` | `3`, since `19<3^3` | `sqrt(2)` |
| `q=4` | `3`, since `19<4^3` | `sqrt(2)` |
| `q>=5` and `q<=17` | `2`, since `19<5^2<=q^2` | `1` |

All active powers are
`2,3,4,5,7,8,9,11,13,16,17`. The power 19 contributes zero at
the endpoint `C=19`; it is absent below it. The power 17 also contributes
zero at `C=17`, and including its positive allowance is safe. There is
no deletion of prime powers such as 8 or 9.

Define the exact constant

```
A_chain = sqrt(3)*log(2)/sqrt(2)
        + sqrt(2)*(log(3)/sqrt(3)+log(2)/2)
        + sum_(5<=q=p^a<=17) log(p)/sqrt(q).
```

Then, throughout the cell and at both boundaries,

```
|<f,S f>| <= A_chain ||f||²,   A_chain < 6.597411.
```

The previous estimate uses `2P`, approximately `11.664652724944267`.
This is an analytic replacement for that allowance, not cancellation
inferred from a sampled Fourier matrix. In Lean, `powers_complete` uses
kernel reduction of the decidable prime-power proposition for all natural
numbers below 20. `mem_active_iff` identifies the varying active set with
**all** prime powers below `C`, rather than a selected list.
`allowance_eq` verifies the displayed exact constant. `primeForm_bound` and
`complexPrimeForm_bound` give its bound for every supported L² function and
every `0<C<=19`, which includes the entire 17–19 cell and every Fourier rank.
`correlation_zero_of_cutoff_le` proves the boundary and inactive-shift cases.
The separate numerical assertion `A_chain<6.597411` is Arb-verified, not
Lean-verified.

## 4. Improved high-mode coercivity

Keep the already derived archimedean diagonal lower envelope `delta(n)`
and off-diagonal norm allowance. Replace `2P` by `A_chain`:

```
beta_even_chain(n) = delta(n) - 2*pi*B_arch - A_chain;
beta_full_chain(n) = beta_even_chain(n) - (2*sinh(Lmax/2)-Lmax).
```

The same form decomposition as in the
[infinite-tail note](WEIL_INFINITE_RANK_TAIL_2026_10_06.md) gives the
corresponding lower bounds for supported finite Fourier vectors and
their form closures. The bounds are independent of the retained rank.
Arb evaluation at 1024 bits gives:

| Envelope | Index | Enclosed comparison, conservatively displayed |
|---|---:|---|
| even | `117259` | `beta > 1.000005825` |
| even | `117258` | `beta < 0.999997298` |
| full | `383530` | `beta > 1.000001306` |
| full | `383529` | `beta < 0.999998699` |

The two-sided comparisons were checked by evaluating the envelope as a
ball and extracting the appropriate endpoint. A lower bound below one
alone would not prove that this particular envelope fails to exceed one.
These are starts for the stated conservative envelopes, not the smallest
indices at which the actual operator becomes coercive.

For the origin-constrained even block at a shifted ground parameter
below one, min–max now bounds the number of eigenvalues below the
far-block floor by `117258`, instead of `18612928`. This improves the
size of the remaining problem by about a factor of 159. It still does
not lower-bound those eigenvalues or control the source projections onto
them, so it does not finish the intermediate inverse estimate.

## 5. Replay and proof boundary

The [evaluation script](../../experiments/prime_spectral/finite_shift_chain_coercivity.py)
and [saved rational endpoints](finite_shift_chain_coercivity_17_19.json)
record the exact integer support guards and source hashes. Replay with:

```sh
uv run --with python-flint==0.8.0 --python 3.12 python \
  experiments/prime_spectral/finite_shift_chain_coercivity.py
lake build Reinmann.SupportTranslation Reinmann.SupportPrimeForm
```

The script evaluates the Lean-proved exact prime allowance and the written
coercivity envelope, checking both sides of its thresholds. The Lean modules
prove the support-dependent integral theorem uniformly in the cutoff and
the function. Neither the numerical script nor these modules proves the
complete analytic Weil coercivity theorem.
The original paper was preserved during its review; this refinement is a
possible revised result with its own partial formalization ledger.
