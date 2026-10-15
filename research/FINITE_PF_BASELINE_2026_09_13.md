# Finite-order positivity baseline — 2026-09-13

**Research baseline:** use PF43 conservatively. **Lean status:** algebraic
transport is proved; the analytic Xi baseline remains an explicit hypothesis.
A named proposition is not an import of an external theorem into Lean.

Katkova's [Multiple positivity and the Riemann zeta-function](https://arxiv.org/html/math/0505174)
uses `xi_1(z)=xi(1/2+sqrt(z))=sum b_k z^k`. These `b_k` are precisely this
repository's ordinary folded coefficients `XiMomentCoeff k`: this identity
is now Lean-proved as `Reinmann.foldedXi_taylor` in `XiTaylorIdentification.lean`.
Their positive signs and finite-PF property remain classical analytic inputs,
not yet Lean-proved. They are not `k! b_k`.

The paper states PF44 in Theorem 1, but its printed proof gives a zero-free
sector `|arg z|<43 pi/44`. Theorem B, as printed there, requires
`|arg z|<m pi/(m+1)` to conclude PF_m. Substituting this sector gives m=43.
Accordingly we retain PF43 as the conservative consequence of that argument;
we do not silently claim to have verified the stated PF44 proof. The source's
height-14 zero-free input, canonical product, and locally uniform limit are
analytic ingredients, not results replayed by our numerical sweep.

This already covers **all arbitrary minors of ranks 3 and 4**, at every index,
with nonnegativity. It does not prove strict positivity of every allowed minor,
a quantitative lower bound, or an unbounded-rank statement. Low-rank numerical
scans are therefore calibration and margin measurements, not discoveries of
previously unknown positivity.

The [2026-10-06 strictness deduction](STRICT_FINITE_PF_FROM_REAL_ZEROS_2026_10_06.md)
adds Hardy's infinitely many negative folded zeros and applies the sector
argument to each quotient after finite zero extraction. It yields a positive
witness for every contiguous minor through rank 43 at every shift. The
determinant transport is developed in `FinitePFStrict.lean`; the actual folded
Xi and Taylor identification are proved in `XiTaylorIdentification.lean`.
The positive center value, sector theorem, canonical product, Hardy infinitude
and extraction remain unformalized. This does not establish strictness of every arbitrary minor
or positivity at unbounded rank.

`Reinmann/FinitePFBaseline.lean` implements:

- A zero-extended Toeplitz sequence and `FinitePF a r` over arbitrary ordered
  row/column selections and all ranks at most r.
- Monotonicity in r and preservation under nonnegative overall scaling.
- Equivalence of upper/lower transpose conventions.
- Exact transport to the repository's Xi Toeplitz entries and contiguous minors.
- Full PF iff finite PF holds at every rank.
- Rank 4 from rank 43, with the analytic rank-43 premise explicit.

The unbounded-degree analytic limit and actual folded Taylor identification
are now proved. Remaining formalization: construct the canonical product and
its real approximants, prove the positive center value, sector-to-PF theorem
and required zero-free input, and extract the real factors for strictness.
The separate theta moment-kernel representation remains unformalized. None
is smuggled in as a custom axiom.

The distinct eventual fixed-degree classical Jensen baseline uses
`gamma_n=n! mu_n`; see [Griffin, Ono, Rolen and Zagier](https://arxiv.org/html/1910.01227v3).
Its quantifier shape is fixed degree followed by sufficiently large shift.
It supplies no single uniform threshold for all degrees. Finite PF, eventual
Jensen hyperbolicity, and a continuous theta kernel's total positivity must
not be interchanged.
