# Normalized rank recurrence and a failed sufficient condition

The new finite transport laboratory checks 4,230 interior windows. The full
transported curvature is positive in every one. However, its multiplicative
correction factor fails log-concavity at 13 windows, ranks 34 through 46 at
shift 4. Thus a proof requiring that factor to be log-concave everywhere cannot
work for this normalization. This conclusion is conditional on the same
FLINT coefficient and interval trust boundary as the existing laboratory.
It is not a failure of the stronger determinant inequality itself.

## Exact normalization

Let D_r(m) denote the contiguous Toeplitz determinant from a_n=mu_n/mu_0, and

```
P_r(m) = product_(j=0)^(r-1) j!/(m+j)!,    A_r(m)=D_r(m)/P_r(m).
```

The empty product P_0 is one. Cancelling factorials gives, for r,m>=1,

```
P_(r+1)(m) P_(r-1)(m) / P_r(m)^2 = r/(m+r)
P_r(m-1) P_r(m+1) / P_r(m)^2 = m/(m+r).
```

Substitution in the classical condensation identity gives

```
r A_(r+1)(m) A_(r-1)(m)
  = (m+r) A_r(m)^2 - m A_r(m-1) A_r(m+1).
```

Where the relevant A values are strictly positive, define

```
t_r(m) = A_r(m-1) A_r(m+1) / A_r(m)^2
B_r(m) = 1 + (m/r)(1-t_r(m)).
```

Then the normalized recurrence becomes the factorization

```
A_(r+1)(m) = A_r(m)^2 B_r(m) / A_(r-1)(m).
```

This is exact algebra, not a representation of Xi by positive spectral data.
The factorial identities are checked over exact rational numbers in tests;
fresh determinant evaluations provide a separate numerical consistency check.
The general all-size condensation identity still needs its existing Lean
formalization; this pass adds no claim that it has been formally proved here.

## Curvature transport, including compensation

For positive B and A, put delta_r(m)=-log t_r(m). At interior shifts m>=2,

```
t_(r+1)(m) = t_r(m)^2/t_(r-1)(m)
             * B_r(m-1) B_r(m+1)/B_r(m)^2

delta_(r+1)(m) = 2 delta_r(m) - delta_(r-1)(m) + C_r(m)
C_r(m) = 2 log B_r(m) - log B_r(m-1) - log B_r(m+1).
```

Thus the exact required inequality is

```
C_r(m) >= delta_(r-1)(m) - 2 delta_r(m).
```

It would be stronger to demand separately that C_r>=0 and
2 delta_r>=delta_(r-1). The first of those demands is false in the certified
Xi data. This is why the next proof target must allow compensation.
The boundary m=1 is separate: the neighboring shift-zero values do not admit
the same m-based ratio formula without additional boundary definitions.

The existing quantitative conjecture
`eta_r(m)>=r/(m+r)` is exactly t_r(m)<=1, or delta_r(m)>=0.
Consequently, the displayed transport inequality is an exact reformulation
of propagation, not an independently established all-rank invariant.
A useful new theorem must derive it from theta/arithmetic information or a
preserved family of bounds, rather than assuming the desired next-rank sign.

## Certified finite results and obstruction

`normalized_recurrence.py` reads the existing laboratory's outward rational
margin enclosures. If s=eta_r-r/(m+r) is its candidate slack, it reconstructs
`t_r=1-(m+r)s/m`. It checks this against the separately serialized raw margin,
rejects duplicates and invalid or nonpositive inputs, and requires the
laboratory's coefficient hash to match the coefficient file supplied.
Every reconstructed next-rank ratio must overlap the directly computed ratio
already recorded in the determinant laboratory. Overlap is a consistency
check; it is never treated as a proof of a symbolic identity.

The eligible windows are exactly
`2<=r<=46`, `2<=m<=119-r`, a total of 4,230. There are 4,217 positive
correction curvatures and 13 negative ones, with no unresolved corrections.
All 4,230 full transported curvatures are positive.

The first failure is at r=34,m=4:

```
C_34(4)                         approximately -0.00007878756681222289
2 delta_34(4) - delta_33(4)     approximately  3.8166753276889174
delta_35(4)                    approximately  3.816596540122105.
```

The implementation recomputes this negative correction from fresh rank-34
determinants at neighboring shifts using the original coefficient balls.
Its strict negative sign agrees with the margin-table result. This is an
independent computation path, not an independent numerical library: both use
FLINT and the same certified coefficient input. The JSON stores rational
bounds, input/source hashes, all windows and the fresh determinant check.
No all-rank assertion or claim of literature novelty is made.

## Replay

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/normalized_recurrence.py --laboratory research/certified_xi/laboratory_120.json --coefficients research/certified_xi/coefficients_120.json --output research/certified_xi/normalized_recurrence_120.json
uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/certified_xi -v
```

The suite has 25 passing tests, including exact reference prefactors,
exponential saturation, a nontrivial fresh determinant transport check,
inconsistent/duplicate input rejection and unresolved denominator handling.
The output is a finite certificate under the documented numerical trust
boundary, not a Lean certificate. Source hashes identify replay inputs;
they cannot authenticate arbitrary third-party numerical claims.

## Next analytic target

Find lower bounds for the inherited curvature and the possibly negative
correction curvature that remain compatible under the recurrence. The observed
failure near high rank and small shift cautions against relying only on
large-shift asymptotics at fixed rank. A successful argument must cover that
regime, rank and shift growing together, and the shift-one boundary. The
rank-two theta estimate supplies a possible base mechanism; its unbounded
version remains open and does not by itself control C_r at higher ranks.
