# A fixed-bandwidth obstruction to the proposed sine-type log-cost theorem

17 October 2026. Written mathematical note; not a Lean formalization or a novelty claim.

The proposed hypotheses do **not** imply that the support needed for a negative zero form diverges like log(1/b). A finite modification of the cosine lattice admits a single fixed-bandwidth witness that is negative for every b>0. This does not refute the measured DH calibration: its zero density, arithmetic form and restricted finite families differ from this model.

## Primary-source check

The targeted check included [Lyubarskii–Seip, Complete interpolating sequences for Paley–Wiener spaces and Muckenhoupt's (A_p) condition](https://arxiv.org/pdf/math/9511212) and [Semmler, Complete interpolating sequences, the discrete Muckenhoupt condition, and conformal mapping](https://arxiv.org/pdf/0708.2787). The first formulates complete interpolation for complex nodes in fixed-type Paley–Wiener spaces and identifies the integer lattice as the classical example; the second develops generating functions and sine-type interpolation (§2, Theorem 3). [Levin–Ostrovskii, On small perturbations of the set of zeros of functions of sine type](https://www.mathnet.ru/php/archive.phtml?jrnid=im&option_lang=eng&paperid=1676&wshow=paper) supplies the standard growth definition. The targeted searches covered sine-type zero perturbations, Paley–Wiener sampling and positivity of zero forms. They did not establish the requested logarithmic lower bound, and this is not evidence of novelty. These are classical sampling/interpolation tools, not prior art establishing the requested logarithmic support lower bound. The elementary example below is derived directly. No claim that it or the conditional balance lemma is novel is made.

## An explicit counterexample

Use the transform convention F(z)=integral f(t) exp(i z t) dt, and let PW_L consist of transforms of L2 functions supported in [-L,L]. For 0<b<=1/4 define the even real entire function

    A_b(z) = ((z^2+b^2)/(z^2-1/4)) cos(pi*z),

with the two removable singularities filled in. Its zero set is

    Lambda_b = ((Z+1/2) minus {-1/2,1/2}) union {-i*b,i*b}.

All zeros are simple for b>0. The generating function has exponential type pi. It satisfies the usual two-sided sine-type growth bounds outside a horizontal strip, uniformly for 0<b<=1/4. Indeed, for |Im z|>=1,

    | (z^2+b^2)/(z^2-1/4) - 1 |
      = |(b^2+1/4)/((z-1/2)(z+1/2))| <= 5/16.

Thus this rational factor has modulus between 11/16 and 21/16. Also

    (1-exp(-2*pi))/2 * exp(pi*|Im z|)
      <= |cos(pi*z)|
      <= (1+exp(-2*pi))/2 * exp(pi*|Im z|).

This proves the claimed uniform growth. The pair separation 2b shrinks in the collision limit, as the proposed b-to-zero problem requires. For each fixed b>0 the zero set is separated, with minimum spacing 2b; this separation constant is not uniform in b. A hypothesis of uniform separation of the colliding pair would exclude the collision regime itself. If a definition reserves “sine-type zero set” for real zeros only, the real background is the sine-type cosine lattice and Lambda_b is its indicated finite nonreal perturbation.

Define its Hermitian zero form by

    Q_b(F) = sum_{r in (Z+1/2) minus {-1/2,1/2}} |F(r)|^2
             + 2 Re( F(i*b) conjugate(F(-i*b)) ).

**Proposition.** There is a fixed nonzero F in PW_pi with Q_b(F)<0 for every b>0. For every epsilon>0 there is also a single fixed smooth compactly supported real test function, supported in [-pi-epsilon,pi+epsilon], whose transform has negative Q_b for every b>0.

**Proof.** Fill the removable values in

    F(z) = z cos(pi*z)/(z^2-1/4).

This is an odd real entire function. Its cardinal-sine identity is

    F(z) = (pi/2) [ sinc(pi*(z+1/2)) - sinc(pi*(z-1/2)) ]
         = integral_{-pi}^{pi} (i/2) sin(t/2) exp(i*z*t) dt.

Hence F belongs to PW_pi; it is nonzero and square integrable on the real line. It vanishes at every real node of Lambda_b. At the remaining pair,

    F(i*b) = -i*b*cosh(pi*b)/(b^2+1/4),
    F(-i*b) = conjugate(F(i*b)).

Consequently,

    Q_b(F) = -2*b^2*cosh(pi*b)^2/(b^2+1/4)^2 < 0.

The time-domain L2 norm squared is pi/4, independent of b. Normalization therefore leaves the sign and fixed support unchanged. Multiplication of F by -i leaves Q_b unchanged and makes its time-domain function real and odd.

For smooth admissibility, convolve this real odd function with any fixed nonzero, even, nonnegative smooth bump g supported in [-epsilon,epsilon]. Its transform G is even and real-entire, and

    G(i*b)=G(-i*b)=integral g(t) cosh(b*t) dt > 0.

The new transform is (-i F)G. It still vanishes at every real node; the off-line contribution is G(i*b)^2 Q_b(F)<0. The convolution is smooth and supported in [-pi-epsilon,pi+epsilon], and is a single fixed nonzero function for all b. This proves the proposition. End of proof.

The center height is not essential: replacing A_b(z) and F(z) by A_b(z−gamma_0) and F(z−gamma_0) gives the same calculation for the single pair gamma_0±i*b, at any fixed real gamma_0. Translation preserves exponential type and L2 membership. The centered example has the additional even-generator symmetry; a translated example is not asserted to have that symmetry or a real time-domain function.

Fixed pole-removal constraints do not repair the centered example. After smoothing, multiply the transform by the fixed polynomial z²+1/4. In time space this applies −d²/dt²+1/4 to a smooth compactly supported real function, so the support remains fixed. The new transform vanishes at ±i/2 and still at every real node. At the moving pair its form is multiplied by (1/4−b²)², which is strictly positive for 0<b<=1/4. The negative sign therefore persists while those two constraints hold.

Thus the infimum negative support half-width is bounded above by pi for every b>0. In the repository convention C=exp(2L), the cutoff infimum is bounded above by exp(2*pi), independently of b. A positive multiple of log(1/b) cannot be a universal asymptotic lower bound on this support cost. The negative margin is O(b^2); an increasing precision cost is a different question and must not be identified with increasing support.

## An even example with a positive-height quartet

The obstruction also survives the symmetry of a positive-height off-line pair and its reflected pair. For 0<b<=1/4 set

    B_b(z) = [((z−1)²+b²)((z+1)²+b²)/((z²−1/4)(z²−9/4))] cos(pi*z),
    W(z) = [(z²−1)/((z²−1/4)(z²−9/4))] cos(pi*z).

Fill the removable singularities. B_b is even and real entire, with off-line zeros ±1±i*b; its other zeros are the half-integer lattice with ±1/2,±3/2 deleted. Its type is pi and it is sine-type for each b>0. Uniform growth outside |Im z|>=2 follows by pairing the four numerator roots with the four real denominator roots: each paired displacement is at most sqrt(5)/4, while each distance to a denominator root is at least 2. The four modulus ratios therefore lie between 1−sqrt(5)/8 and 1+sqrt(5)/8. Separation is again positive for each fixed b, not uniform in the collision limit.

The fixed real even time function

    w(t) = −(3/8) cos(t/2) + (5/24) cos(3*t/2),  |t|<=pi,
           0 otherwise,

has transform W. To verify this, use the partial fractions 3/[8(z²−1/4)]+5/[8(z²−9/4)] and the two shifted-sinc sums. W vanishes at all remaining real nodes and at ±1. Write a=15/4−b². Direct substitution gives

    W(1+i*b) = cosh(pi*b)/(b²+1/4)
                * [ b²(17/4+b²) + 2*i*b(15/4+b²) ]/(a²+16*b²).

Its imaginary part strictly exceeds its nonnegative real part for 0<b<=1/4: after canceling b it suffices that

    2(15/4+b²) > b(17/4+b²),

whose left side is at least 15/2 and whose right side is at most 69/64. Thus Re(W(1+i*b)²)<0. The four off-line nodes contribute exactly 4 Re(W(1+i*b)²), while every real-node contribution vanishes. This gives a fixed real even witness with a strictly negative full zero form at positive height, for every offset in the stated collision range.

Fixed smoothing also preserves this quartet's sign. Choose an even nonnegative smooth bump g supported in [-1/200,1/200], with integral 1, and let G be its transform. For |z|<=2,

    |G(z)−1| <= (1/100) exp(1/100) <= 1/99 < 1/50.

The middle inequality follows from exp(x)<=1/(1−x) for 0<=x<1. At z=1+i*b write W=X+i*Y and G=u+i*v. The bounds above give 0<=X<=Y/4, 49/50<=u<=51/50 and |v|<=1/50. Consequently

    |Re(W*G)| <= (55/200) Y,
     Im(W*G)  >= (195/200) Y > 0.

Thus Re((W*G)²)<0 throughout 0<b<=1/4. The convolution is a single fixed smooth real even witness supported in [-pi−1/200,pi+1/200], annihilates all remaining real nodes, and has negative quartet contribution for every such b.

The positive-height example can satisfy the same two pole-removal constraints as well. Multiply W*G by P(z)=z²+1/4, corresponding to applying −d²/dt²+1/4 after smoothing. At z=1+i*b write P=R+i*I. Then R>=19/16, 0<=I<=1/2, and I/R<=8/19. Since 0<=X/Y<=1/4, the product W*P has positive imaginary part and absolute real part at most half its imaginary part: |X*R−Y*I|<=max(X*R,Y*I)<=(8/19)Y*R, whereas Y*R+X*I>=Y*R. Multiplication by the same G leaves the absolute real part at most (53/100) times that imaginary part and the imaginary part at least (97/100) times it. Its square still has strictly negative real part. Thus a single fixed smooth real even witness with transform W*P*G vanishes at ±i/2 and at every real node, and has negative positive-height quartet form throughout the collision range.

## The actual cutoff in the centered lattice model

There is also a precise replacement theorem for the centered example's **unconstrained** zero form. Let L_*(b) be the infimum L admitting a real L2 witness supported in [-L,L] with Q_b<0. The same infimum results if the witness must be smooth. As b tends to 0 through positive values,

    L_*(b) = pi − (32/pi) b² + O(b⁴),
    C_*(b) = exp(2*pi) [1 − (64/pi) b² + O(b⁴)].

Thus this model has a finite limiting cutoff, approached quadratically. This is an elementary sampling calculation, not a claimed novel theorem. The expansion is for the unconstrained form; the explicit pole-filtered witnesses above establish a fixed upper bound but not this same expansion under additional constraints.

**Proof.** For 0<L<=pi extend f by zero to [-pi,pi]. Parseval in the orthogonal basis exp(i(n+1/2)t) gives

    sum_{n in Z} |F(n+1/2)|² = 2*pi*||f||².

Split a real f into its even and odd parts. On the even part the form is

    2*pi*||f_even||² − 2<f_even,cos(t/2)>²
       + 2<f_even,cosh(b*t)>² >= 0,

because ||cos(t/2)||²=L+sin L<=pi. On the odd part it is

    2 [pi*||f_odd||² − <f_odd,u>² − <f_odd,v>²],
    u(t)=sin(t/2),  v(t)=sinh(b*t).

The inner products and norms are over [-L,L]. Consequently the odd form is nonnegative exactly when the largest eigenvalue of the two-by-two Gram matrix M is at most pi, where

    M = [[A,B],[B,D]],
    A = L−sin L,
    D = sinh(2*b*L)/(2*b)−L,
    B = 2[b*sin(L/2)*cosh(b*L)−(1/2)*cos(L/2)*sinh(b*L)]/(b²+1/4).

At b=0 take the removable value D=0. These formulas follow by elementary integration. M increases in the positive-semidefinite order as L increases: its derivative is twice the outer product of (u(L),v(L)) with itself. At L=pi and b>0 its largest eigenvalue exceeds pi, since A=pi and B>0; for b=0 and every L<pi it is strictly less than pi.

Near (L,b)=(pi,0), the smaller eigenvalue remains below pi. The crossing equation is therefore

    g(L,b)=(pi−A)(pi−D)−B²=0.

Here g(pi,0)=0, its L derivative is −2*pi, and

    g(pi,b)=−64*b²+O(b⁴),

because B(pi,b)=8*b+O(b³). The implicit function theorem gives one crossing L_*(b) near pi. Monotonicity makes it the first negative cutoff; no earlier negative interval can precede it. Since g is even and analytic in b near 0, Taylor expansion gives L_*(b)=pi−32*b²/pi+O(b⁴). Exponentiation proves the stated formula for C_*.

The form is continuous in the L2 norm for each L<=pi by Parseval and its four additional bounded evaluation functionals. A strictly negative odd L2 witness can therefore be approximated by smooth odd functions with the same support bound. This proves equality of the two cutoff infima. Negative witnesses at L<=pi also remain admissible for larger support, so considering all L does not change this first cutoff. End of proof.

## What a genuine logarithmic balance theorem would require

A correct elementary conditional statement is available. Suppose a family of normalized test classes has an exact idealized form

    Q_{b,C}(v) = P_C(v) - b^2 D_C(v),

and fixed positive constants a,A,d_plus,d_minus and kappa>kappa_prime satisfy:

1. For every unit v, P_C(v)>=a exp(-kappa*C) and D_C(v)<=d_plus exp(-kappa_prime*C).
2. For every C there exists a unit v_C with P_C(v_C)<=A exp(-kappa*C) and D_C(v_C)>=d_minus exp(-kappa_prime*C).

Then all forms are nonnegative when

    C <= [2 log(1/b)+log(a/d_plus)]/(kappa-kappa_prime),

and the supplied witness is negative when

    C > [2 log(1/b)+log(A/d_minus)]/(kappa-kappa_prime).

Subtract the two exponential bounds in each case and divide by the positive exp(-kappa*C) to prove both statements. Subject to an initial C range, this sandwiches the detection cutoff between those two expressions, with only an O(1) difference. It is an elementary spectral-balance lemma, not a result derived from sine-type hypotheses. The fixed-bandwidth example has an exact null direction in its real-node form, so the required uniform positive lower bound fails. The parameter C in this conditional lemma must itself be specified; exponential decay in C is an additional assumption and cannot be deduced by silently changing from bandwidth L to the multiplicative cutoff C=exp(2L).

The genuine zero form also has a Taylor issue. For real-entire F, writing a=F(gamma), d=F'(gamma), e=F''(gamma),

    2 Re F(gamma+i*b)^2
      = 2 a^2 - 2 b^2 (d^2+a*e) + O(b^4).

The approximation -2 b^2 |F'(gamma)|^2 needs a vanishing or quantitatively controlled center value and a uniform higher-derivative remainder. It is not a general estimate for arbitrary witnesses. An interpolation witness, matched spectral subspace, positive-frame lower bound and controlled Taylor/zero tail would have to be proved in a more restrictive model before the conditional logarithmic balance could become the desired theorem.
