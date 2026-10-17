# Density obstructs exact annihilation, but does not prove a logarithmic cost

This is an exploratory consequence of classical Jensen theory, not a new detection law.
Forecasting remains closed following the held-out failures on 17 October.

Let F be a nonzero entire function with

    |F(z)| <= A (1+|z|)^m exp(L |z|),

where A,L,m are fixed. This includes Fourier transforms of compactly supported
smooth witnesses and compactly supported distributions. Choose a center c with
F(c) != 0. Jensen's formula at radius 2R gives

    n_F(c,R) log 2 <= log max_{|z-c|=2R} |F(z)| - log |F(c)|
                   <= 2 L R + O(log R).

Boundary zeros can be avoided by an arbitrarily small enlargement of the outer
circle; the same bound follows by a limit. Counts include multiplicity. Thus
n_F(c,R)=O(R). An exact witness cannot vanish at a node set whose count divided
by R is unbounded. Finite deletions or a fixed polynomial filter do not change
this obstruction.

The lattice counterexample has O(R) real nodes and admits a fixed exponential
type annihilator. A real node set with count comparable to R log R does not.
This distinguishes the *exact annihilation mechanism* used by the lattice model.
For an arithmetic form this observation applies only after proving such growth
for the particular nodes the witness must annihilate; counting all complex
zeros is not automatically counting critical-line nodes.

This argument supplies no lower bound on how small the values at those nodes
can be. A logarithmic detection cost in b needs quantitative sampling or
interpolation estimates, uniform control of the off-line derivative term,
and a normalization of the witness. Global counts alone supply none of those
constants. They therefore do not justify another forecast or turn the empirical
logarithmic fit into a theorem.

Classical source: Jensen's formula; the project pins Mathlib v4.30.0, whose
`Mathlib/Analysis/Complex/JensenFormula.lean` develops the corresponding
complex-analytic infrastructure. The conclusion here is a written argument,
not an additional Lean theorem.
