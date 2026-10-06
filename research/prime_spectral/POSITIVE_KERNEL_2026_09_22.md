# Positive prime kernels and a measure-convergence criterion

Follow-up: the [certified eigenpair method](ISOLATED_KERNEL_2026_09_22.md)
extends the finite positive-kernel certificates to modes 12 and 16 at
the same cutoff. It resolves failures of the prior LDL-based procedure,
without altering the matrix definition or proving sequence-wide uniformity.

## Finite result and the remaining uniform problem

The stored cutoff-13 mode-4 and mode-8 quotients have spatial Fourier
kernels that are strictly positive on their entire support, including
both endpoints. After normalization these give even probability densities.
Their certified variances are respectively near

    0.090235001895483916326037228590,
    0.06212604639725704.

This is an additional finite gate. Positivity of arbitrary later kernels,
a sequence-wide variance bound, and convergence to the Xi theta measure
are not proved. The finite gate and the conditional theorem below do
not prove RH.

## 1. The exact spatial kernel and its normalization

For L=log(cutoff), let c_-n=c_n be the existing quotient eigenvector
normalized by c_0+2 sum_(n=1)^N c_n=1. Define, for |t|<=L/2,

    g(t)=c_0+2 sum_(n=1)^N (-1)^n c_n cos(2pi*n*t/L).

Then g(-L/2)=g(L/2)=1 exactly. All nonconstant Fourier terms integrate
to zero, giving integral g(t)dt=L*c_0. When g>0, necessarily c_0>0,
and

    dnu(t)=g(t)/(L*c_0) dt on [-L/2,L/2]

is an even probability measure. Direct integration gives

    integral exp(-izt) dnu(t)
      =sum_(n=-N)^N c_n*(-1)^n*sinc(pi*n-zL/2)/c_0
      =P_(N,L)(z),                                  (1)

the actual previously constructed Fourier profile. Positivity is not
inferred from P having real zeros; it is checked separately below.

## 2. Whole-interval Bernstein certificate

Put u=(1+cos(2pi*t/L))/2 in [0,1]. Since
T_n(1-2u)=(-1)^n cos(2pi*n*t/L), the exact boundary normalization gives

    g(t)=p(u), p(u)=1+2 sum_(n=1)^N c_n*(T_n(1-2u)-1). (2)

This form enforces p(0)=1 without subtracting large interval quantities.
If p(u)=sum_j a_j u^j, its degree-N Bernstein coefficients are

    b_k=sum_(j=0)^k a_j*binomial(k,j)/binomial(N,j),
    p(u)=sum_(k=0)^N b_k*binomial(N,k)*u^k*(1-u)^(N-k).

The Bernstein basis functions are nonnegative and sum to one. Thus
strictly positive lower bounds on every b_k prove p(u)>0 throughout
[0,1]. This includes the support endpoints u=0 and midpoint u=1;
there is no point-sampling or subdivision gap.

All 5 coefficients for N=4 and all 9 for N=8 are certified positive
using the unchanged prime matrix inputs. The first equals one exactly.
The implementation fails if any coefficient's positivity is unresolved.
The test control c_1=2/5, c_0=1/5 has positive mass but g(0)=-3/5,
showing why the extra gate must not be assumed automatically.

## 3. Variance and the earlier spectral sum

Integrating each cosine term against t^2 gives exactly

    V=integral t^2 dnu(t)
      =L^2/12+(L^2/pi^2)*sum_(n=1)^N c_n/(c_0*n^2).  (3)

The common denominator is retained in the implementation. Combining
with the direct eigenvector formula for the quotient spectral sum S,

    V/2=S+(L^2/(4pi^2))*sum_(k>N) k^(-2).             (4)

Consequently, along a path where L^2/N tends to zero, uniform boundedness
of these variances is equivalent to boundedness of S. Equation (3)
rewrites the Fourier cancellation as spatial concentration. It does not
prove such concentration from the prime-defined eigenvalue equation.

## 4. Why bounded variance is unusually strong for these gated kernels

Assume both the positive-kernel gate and the earlier real-zero quotient
gates. The exact factorization P=R*G gives

    |P(z)|<=exp[(S+(L^2/(4pi^2))*sum_(k>N)k^(-2))*|z|^2]
           =exp(V*|z|^2/2).                          (5)

Each paired quotient zero and each paired exterior grid zero contributes
a factor 1-z^2/lambda^2; use |1-w|<=exp(|w|) and sum inverse squares.
Thus a uniform variance bound V<=M gives a uniform entire-function
bound. This implication does not hold for arbitrary probability measures;
the finite real-zero factorization is essential here.

Also P(iy) is the moment-generating function of nu. Markov's inequality
and (5), minimized at y=a/M, give for M>0

    nu({|t|>=a})<=2 exp(-a^2/(2M)), a>0.              (6)

Thus a uniform variance bound supplies uniform Gaussian probability
tails in this particular family. This is a conditional sequence-wide
consequence, not a statement that the two finite variance measurements
prove such a bound for all later inputs.

## 5. Weak kernel convergence would suffice for entire convergence

Suppose a sequence passes both finite gates, its variances are uniformly
bounded, and its probability measures nu_j converge weakly to a measure nu.
For real x, the bounded continuous test function exp(-ixt) shows

    P_j(x)->integral exp(-ixt) dnu(t).

The disk bound (5) and Cauchy's formula bound every Taylor coefficient.
A diagonal subsequence extraction, with uniform Cauchy tail bounds on
larger disks, therefore yields locally uniform entire subsequential
limits. Each has the displayed characteristic function on the real
axis. The identity theorem makes all subsequential limits identical,
so the entire sequence converges locally uniformly to that entire
extension. Its value at zero is one. A Rouche argument on a disk about
a hypothetical nonreal zero would contradict the real-zero property
of P_j; hence the limit has only real zeros.

If the weak limit nu is the normalized symmetric measure from Xi's
positive theta Fourier representation, then the real-axis limit is
Xi(x)/Xi(0), and the identity theorem identifies the entire limit with
normalized Xi. This would establish RH. The required weak convergence
has not been established. The prime-defined kernels here are constructed
without inserting Xi coefficients, theta samples, or zero locations.
The theta measure enters only as the still-unproved identification target.

This offers a concrete alternative to separately proving convergence of
every Taylor coefficient: derive spatial kernel convergence from the
arithmetic eigenvalue problem, together with the uniform variance bound
and gates. Neither normalization nor finite positivity identifies the
weak limit. Taking a subsequence whose measures merely converge, without
identifying their limit, cannot complete the argument.

## Validation and reproduction

`positive_kernel.py` produces finite Bernstein coefficients, the
normalizing mass, variance, and input/source hashes. Four tests check
full coefficient positivity; the Bernstein/Fourier identity across the
support; independent FLINT integration of the variance and complex
Fourier transform; and a sign-changing control.

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/positive_kernel.py --certificate research/prime_spectral/certified_weil_13_4.json --output research/prime_spectral/positive_kernel_13_4.json
uv run --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/positive_kernel.py --certificate research/prime_spectral/certified_weil_13_8.json --output research/prime_spectral/positive_kernel_13_8.json
uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/prime_spectral -v
```

The polynomial positivity proof is analytic with interval-certified
coefficients. The convergence theorem is conditional written analysis.
Neither is Lean formalized. RH remains unproved.
