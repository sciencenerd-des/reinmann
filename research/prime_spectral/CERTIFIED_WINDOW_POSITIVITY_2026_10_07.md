# Certified Weil positivity on windows containing 2 and 3 (2026-10-07)

**Result.** For each window below, every test function supported in
`[C^{-1/2}, C^{1/2}]` (window log-length `L = log C`) satisfies
`Q(f) ≥ c‖f‖²`, where `Q` is the semilocal Weil quadratic form. This holds for
all `f ∈ L²[0, L]` with `∫|F(t)|² log(2+|t|) dt < ∞`. The certificates use
FLINT/Arb ball arithmetic throughout. They are computer-assisted proofs,
**not** Lean proofs.

| L = log C | C | prime powers in window | certified c | reduced λ_min (even / odd) | T, N | time |
|---|---|---|---|---|---|---|
| 1.16 | 3.190 | 2, 3 | 3.901e-9 | 4.33e-9 / 1.53e-6 | 100, 140 | 32 s |
| 1.6 | 4.953 | 2, 3, 4 | **9.279e-18** | 1.031e-17 / 1.142e-14 | 200, 300 | 638 s |
| 1.6094 | 4.9976 | 2, 3, 4 | **6.921e-18** | 7.69e-18 / 6.84e-15 | 300, 420 | 2553 s |

The certificates are `window_positivity_L1.16.json`, `window_positivity_L1.6.json`
and `window_positivity_L1.6094.json` in this directory. All three were made by
`experiments/prime_spectral/window_positivity_certificate.py` (SHA-256 `88a08abf10e6…`).
Each keeps 90% of the reduced-form minimum as certified margin. Since
`1.6094 < log 5`, the last row covers **every window that does not contain the
prime 5**. Run time is dominated by direct Bessel evaluation, and a segmented
recurrence would cut it about 10×.

Positivity on one window implies it on every shorter window. The Weil
functional depends only on `f* * f`, which is invariant under dilation, so
any multiplicative interval of length `≤ C` is covered.

## Status against the literature — not a new frontier

| source | window | status |
|---|---|---|
| Yoshida 1992; Connes–Consani 2021 | `C = 2` | refereed |
| Zhu, [arXiv:2608.24827v2](https://arxiv.org/abs/2608.24827) | `C = e^{1.6} ≈ 4.95` | certified (mpmath), unrefereed |
| V. Liu, [alphaXiv](https://www.alphaxiv.org/abs/2609.weil-positivity-riemann-zeta-bounds) | `C = e² ≈ 7.39` (`2^-151`); `C ≈ 8.37` (`2^-49162`) | claimed; under review |
| **this note** | `C ≈ 4.9976`, i.e. every window not containing 5 | Arb certificates |

What this adds:

1. **An independent replication of Zhu's window**, with different software
   (Arb instead of mpmath), rigorous quadrature nodes, a verified Cholesky
   step and a separately written proof chain. Our reduced-form minimum at
   `L = 1.6`, `1.031e-17`, lies inside Zhu's certified enclosure
   `[8.9e-18, 2.27e-17]`. Our certified constant `9.28e-18` is slightly
   sharper than his `8.9e-18`. Independent replay of this certificate has been
   requested publicly (murillo128/mathia issue #152).
2. **The normalization check.** The frequency form below reproduces the
   repository's exact Weil matrix `A(C)` (`closed_weil.py`) to about `4e-10`.
   That is the only error in our tail approximation of the check; the
   certificate itself does not use it.
3. **A reusable fast generator.** A window of the same difficulty as Zhu's
   flagship certifies in about a minute.

## Proof chain

`F(t) = ∫_0^L f(x)e^{-itx}dx`, `α_s = ∫_0^L f e^{sx}`, `w_n = Λ(n)n^{-1/2}`,
`A_L = Σ_{n<C} 2w_n`.

1. **Frequency form.** `Q(f) = 2Re(α_{1/2} ᾱ_{-1/2}) + (1/2π)∫|F|²Ψ`, where
   `Ψ(t) = Re ψ(1/4+it/2) − log π − Σ_{n<C} 2w_n cos(t log n)`. This is Weil's
   explicit-formula distribution in frequency form, the same normalization as
   Zhu's `Q` and the repository's `Dist`.
2. **Discard.** `Re ψ(x+iy)` increases in `|y|`, from the series
   `Σ(1/(k+1) − (k+x)/((k+x)²+y²))`. Hence for `|t| ≥ T`,
   `Ψ(t) ≥ β := Ψ_R(T) − A_L`, and `Q ≥ R`, where
   `R(f) = Pole + (1/2π)∫_{|t|<T}|F|²(Ψ−β) + β‖f‖²`.
3. **Basis.** Normalized Legendre polynomials on `[0, L]`, with transforms
   `p̂_n(t) = √((2n+1)L) e^{-itL/2}(−i)^n j_n(tL/2)`. Even and odd degrees
   decouple, and the pole vectors are `√((2n+1)L) e^{±L/4} i_n(±L/4)`.
4. **Finite block.** Panel Gauss–Legendre quadrature uses Arb's rigorous
   nodes and weights. The Bernstein-ellipse error bound (Trefethen) needs
   `|Ψ|` on rectangles. It is enclosed on sub-boxes with the shifted digamma
   `ψ(z) = ψ(z+12) − Σ_{k<12} 1/(z+k)`, and added to every entry as a radius.
   The spherical Bessel values come from Arb or a guarded power series. Ball
   recurrences are avoided: they amplify radii exponentially in the
   oscillatory range.
5. **Verified positive definiteness (Rump).** Factor `mid(R) − sI ≈ L̃L̃ᵀ`, then
   check `‖R − sI − L̃L̃ᵀ‖_F < s` in balls, with exact per-entry dot products.
   Naive interval Cholesky and Arb's blocked matrix product both give loose
   enclosures here, because the entries span a huge dynamic range.
6. **Tails.** From `|j_n(x)| ≤ x^n/(2n+1)!!` and
   `|i_n(x)| ≤ x^n/(2n+1)!! e^{x²/(2(2n+3))}`, both the high-mode deviation
   `ε_D` and the coupling `ε_B` are tiny. The two-block bound then gives
   `R ≥ (min(λ₀, β−ε_D) − ε_B)‖f‖²`.

## Why we stop near C ≈ 5, and what would move the frontier

**The comb barrier.** Step 2 needs `Ψ_R(T) > A_L`, so `T ≈ 2π e^{A_L}`, and
the Legendre block size grows like `e·L·T/4`. Some values:
- `C < 5`: `A_L = 2.94`, so `T ≈ 200`.
- Past 5: `A_L = 4.38`, so `T ≈ 840` and `N ≈ 1100+`.
- At `C ≈ 7.4`: `A_L = 5.85`, so `T ≈ 3600` and `N ≈ 8000`.

This is the doubly exponential cost that Zhu reports. It also explains why
Liu's constant at `C ≈ 8.37` is `2^-49162`.

**Observed subtlety.** At `L = 1.6094` with `T = 200`, the *odd* block of the
reduced form `R` is negative (`−1.5e-15`), while at `L = 1.6` it is
`+1.1e-14`. `R` is only a lower bound for `Q`: the discarded high-frequency
excess is about `|edge jump|²/T`. Raising the cut to `T = 300` restores
positivity in the even block (`7.69e-18` vs `5.32e-18`). Margins near the
ground state are sensitive to `T`.

**The window shift-graph bound (new observation, not yet usable).** For `f`
supported in the window, the prime part is `⟨f, Sf⟩`, where `S` is a
compressed sum of shifts. Grouping by prime, the shifts by powers of one
prime act on finite orbits, which are weighted path graphs. This gives
`‖S‖ ≤ Σ_p λ_max(W_p)`, which is much smaller than the comb supremum `A_L`:

| C | A_L | per-prime bound | resulting T reduction |
|---|---|---|---|
| 4.95 | 2.94 | 1.52 | 4× |
| 8.37 | 6.34 | 3.30 | 21× |
| 10.8 | 7.08 | 3.77 | 27× |
| 19 | 11.67 | 6.16 | 250× |

(Floating diagnostic: `experiments/prime_spectral/window_shift_graph_bound.py`.)

**Obstacle.** Zhu's reduction works because, apart from a discarded
nonnegative form, every operator is band-limited, and band-limited couplings
in the Legendre basis are super-exponentially small. A window shift is not
band-limited. Applied to a near-ground state with nonzero edge values, it
creates jumps whose Legendre tail decays only like `N^{-1/2}`. The
Schur-complement loss is then about `|v(0)|² w² / (N(β−σ))`, far above the
`10^{-20…-40}` margins. Making the window bound compatible with a
super-exponential tail estimate is the concrete open problem. Two ideas to
test:
- a basis adapted to the shift breakpoints;
- a discard of the form `⟨f,(σ−S)f⟩ ≥ 0` restricted to a high-frequency
  subspace defined through the window, not the line.

Solving it would bring `C ≈ 10–19` within reach of the same machinery, past
every current claim. Without it, pushing past `C ≈ 8.4` needs dense certified
blocks of size `10³–10⁴`.

## Reproduce

```bash
pip install python-flint==0.8.0
cd experiments/prime_spectral
python window_positivity_certificate.py --L 1.6 --T 200 --N 300 --lambda-fraction 9/10 --out cert.json
```
