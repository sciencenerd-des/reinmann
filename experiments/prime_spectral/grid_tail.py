"""Bounds for the forced exterior grid factor in prime Fourier profiles.

No Xi data enter these estimates. The all-support limit theorem is in
research/prime_spectral/GRID_TAIL_SCALING_2026_09_20.md.
"""
from flint import arb, acb, acb_mat


def quotient_polynomial_profile(quotient, z):
    """det(zI-B)/det(-B); uses only the prime-defined quotient matrix.

    Real-zero status still requires the separate quotient metric gates.
    """
    size = len(quotient)
    if not size or any(len(row) != size for row in quotient):
        raise ValueError('nonempty square quotient matrix required')
    denominator = acb_mat([[-acb(x) for x in row] for row in quotient]).det()
    if denominator.contains(0):
        raise ArithmeticError('nonzero characteristic polynomial at origin unresolved')
    numerator = acb_mat([[(acb(z) if i == j else 0)-acb(quotient[i][j])
                          for j in range(size)] for i in range(size)]).det()
    return numerator/denominator


def _parameters(length, modes, argument):
    if type(modes) is not int or modes < 1:
        raise ValueError('positive integer mode count required')
    length, argument = arb(length), arb(argument)
    if not length.is_finite() or not argument.is_finite() or not length > 0 or not argument >= 0:
        raise ValueError('finite positive length and nonnegative argument required')
    return length, argument


def disk_error_bound(length, modes, radius):
    """Uniform bound |G(z)-1|<=expm1(R^2 L^2/(4 pi^2 N)), |z|<=R."""
    length, radius = _parameters(length, modes, radius)
    return ((radius*length/(2*arb.pi()))**2/modes).expm1()


def imaginary_log_lower(length, modes, height):
    """Lower bound for log G(i*y), also for log P(i*y) under quotient gates."""
    length, height = _parameters(length, modes, height)
    x = height*length/(2*arb.pi())
    return x*x/((modes+1)*(1+(x/(modes+1))**2))
