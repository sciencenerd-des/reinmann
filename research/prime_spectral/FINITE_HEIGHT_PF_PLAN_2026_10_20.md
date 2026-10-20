# Finite-height strengthening: the exact remaining certificate

The new standalone module `Reinmann/FiniteHeightPFCalibration.lean` proves

    ZetaNoLowStripZero(14.1)
      and (every strip zero at |gamma|<=32 has |beta-1/2|<=9/40)
        => FinitePF XiMomentCoeff 97.

It uses the proved actual-Xi sector bridge and a two-band angle estimate.
Below height 32, the desired half-width 9/40 is less than
14.1*pi/196. Above height 32, the classical half-width 1/2 is less than
32*pi/196. The theorem uses rational comparisons with Mathlib's pi bound;
the trigonometric estimate is the existing theta<=tan(theta).

This is a conditional calibration theorem, not a new zero certificate.
The first-zero input is already proved by Target B; the height-32 half-width
input is not. The latter asks for zero exclusion on the two outer portions
of the strip, with boundaries at beta=11/40 and beta=29/40. It permits zeros
on the critical line. A completely zero-free rectangle to height 32 would
be false because it includes the first several critical-line zeros.

The existing evaluator can plan adaptive tiles for the closed right outer
rectangle [29/40,1] x [0,32], then use the existing symmetries. A successful
certificate there is slightly stronger than the width input (it excludes
the boundary too). Before generating tile tables, measure cost near height
32 and check all evaluator/remainder constants on that new domain. Constants
proved only through height 14.1 must not be extrapolated. No tile generation
or new height certificate is included in this round.

This shared finite-height implication also holds in analogous DH geometry.
It is finite calibration, not an arithmetic discriminator or an RH strategy.
Keep Target B's finished height fixed at 14.1 in its CI closeout. No all-rank
statement follows by varying the rank without proving each new analytic input.
