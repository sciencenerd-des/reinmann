# Mixed analytic-remainder rows in the split-pair extension

This is a mathematical proof draft for the remaining determinant estimate in
formal target A. It is not yet a Lean theorem or a complete entire-function
extension. The existing RH equivalences and their classical bridges are
unchanged. Simple poles and one isolated equal-modulus pair are restrictions of
this standalone model, not extra hypotheses silently added to PF implies RH.

## The estimate

Let s>=1 and m>=s. Suppose the ordinary coefficients satisfy

    h_n = sum_(l=1)^m c_l lambda_l^n + e_n,
    |e_n| <= A R^(-n),     A>=0, R>0.

Order alpha_l=|lambda_l| decreasingly, with alpha_s>0, and set

    D = product_(l=1)^s alpha_l,
    q = 1/(R alpha_s) < 1.

Let H_n(i,j)=h_(n+i+s-1-j), for 0<=i,j<s. Let M_n be the same
matrix with e replaced by zero. Define

    B = max(1, R^(-1), max_l alpha_l),
    K = max(A, max_l |c_l|) B^(2s-2).

Then, for every integer n>=0,

    |det(H_n)-det(M_n)| / D^n
        <= s! (m+1)^s K^s q^n.                         (1)

The constant is deliberately coarse. Its finiteness and its independence of n
are what the sign-oscillation argument needs.

## Proof, including the cancellation a crude entry estimate misses

Expand the determinant by multilinearity in its s rows. A row is selected from
one of m pole rows, or from its analytic-error row. The terms with no error row
sum to det(M_n), so the difference consists of terms with k>=1 error rows.

For a pole choice l in row i, the row equals

    c_l lambda_l^(n+i) (lambda_l^(s-1-j))_(j=0)^(s-1).

If two pole rows choose the same l, they are scalar multiples of the same row
vector and their determinant vanishes. This remains true in the presence of
other error rows. Thus only distinct pole choices survive.

The integer i+s-1-j lies between 0 and 2s-2. Every entry in a pole row has
absolute value at most K alpha_l^n. Every entry in an error row has absolute
value at most K R^(-n). The Leibniz formula therefore bounds a term with k error
rows and distinct pole-index set I of size s-k by

    s! K^s (R^(-k) product_(l in I) alpha_l)^n.

The decreasing order gives

    product_(l in I) alpha_l
       <= product_(l=1)^(s-k) alpha_l
       <= D alpha_s^(-k).

The last inequality holds because each of the k omitted factors among the first
s is at least alpha_s. After division by D^n, the bound is s! K^s q^(kn),
which is at most s! K^s q^n. There are at most (m+1)^s row choices. Summing the
bounds proves (1), including n=0. Zero residues cause no difficulty for this
bound; nonzero residues are needed separately for the leading constant.

A naive determinant perturbation estimate instead repeats the largest pole
modulus s-1 times. Its exponential rate can exceed 1 even when the true rate is
q<1. Alternation and distinct pole choices are essential here.

## What this supplies to the analytic extension

For an entire F with F(0)!=0, assume its zeros in the closed disk |z|<=R
are exactly the distinct simple zeros a_l, all strictly inside the disk.
Subtract their principal parts from 1/F. After removal at
every a_l, the resulting common analytic function g has a finite circle bound
|g|<=A. Its ordinary coefficients satisfy |e_n|<=A R^(-n) by Cauchy's estimate.
The pole expansion is

    1/(F'(a_l)(z-a_l))
       = sum_(n>=0) [-1/(a_l F'(a_l))] (1/a_l)^n z^n

near 0. Hence lambda_l=1/a_l and c_l=-1/(a_l F'(a_l)). This is an identity of
actual Taylor coefficients, not an assumed determinant asymptotic. If the pair
at the shift boundary has modulus |a_*|<R, then q=|a_*|/R<1.

The finite moment determinant already has a proved subset expansion, computed
nonzero Vandermonde/residue constants, and a finite pole-subset gap. Combining
that finite tail with (1) gives a remainder decaying at the larger of the two
rates. The elementary geometric-sum oscillation argument can then transfer
both signs to H_n. The signed Jacobi bridge transfers those signs to the original coefficient
minors after matching its z -> -z convention: apply this reciprocal argument to
F(-z) when F denotes the original generating function.

This argument only uses meromorphic reciprocals on one disk. A genus-zero
canonical product is one application, not a substitute for checking its
analytic hypotheses. It also does not handle arbitrary multiplicities or
additional modulus ties; those require a more general argument.

## Formal obligations still open

1. Patch the already constructed single-pole analytic germs into one common
   remainder and prove analyticity through all selected poles.
2. Derive the Taylor coefficient identity from that function identity, including
   the exact residue sign above, rather than assuming coefficient decomposition.
3. Formalize the mixed-row expansion, repeated-pole cancellation, ordered subset
   product bound and estimate (1). The existing `SplitPairDeterminant` expansion
   is the nearest precedent, but error rows depend on their row index.
4. Combine the proved analytic and determinant errors with the existing
   oscillation and Jacobi modules. Until then, the entire-function extension is
   incomplete in Lean.

No novelty is claimed for multilinearity, Cauchy's estimate or this classical
pole-dominance strategy. This note makes the required decay mechanism explicit;
it is not an RH proof or a new detection-law forecast.
