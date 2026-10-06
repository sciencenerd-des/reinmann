"""Exact polynomial modes of the repeated-root rank linearization.

This is a control-family sensitivity calculation, not a Xi error bound.
"""
from flint import fmpq_poly


def second_difference(p):
    x = fmpq_poly([0, 1])
    return p(x+1)-2*p+p(x-1)


def _monic_eigenpoly(degree, eigenvalue, diagonal, operator):
    x = fmpq_poly([0, 1])
    p = x**degree
    for k in range(degree-1, -1, -1):
        residual = operator(p)-eigenvalue*p
        p += residual[k]/(eigenvalue-diagonal(k))*x**k
    if operator(p) != eigenvalue*p:
        raise ArithmeticError('exact eigenpolynomial identity failed')
    return p


def mode(degree, order):
    """Return angular p(m), radial y(r), with y(0)=0, y(1)=1.

2<=order<=degree; eigenvalue=order*(order-1). Equalities hold as
rational polynomial identities, not just at sampled arguments.
"""
    if type(degree) is not int or type(order) is not int or not 2 <= order <= degree:
        raise ValueError('integers 2<=order<=degree required')
    x = fmpq_poly([0, 1])
    eigenvalue = order*(order-1)
    angular = _monic_eigenpoly(order-2, eigenvalue, lambda k: (k+1)*(k+2),
                              lambda p: -second_difference(x*(degree-x)*p))
    radial = _monic_eigenpoly(order, eigenvalue, lambda k: k*(k-1),
                             lambda p: x*(x+degree)*second_difference(p))
    if radial(0) != 0 or radial(-degree) != 0 or radial(1) <= 0:
        raise ArithmeticError('radial endpoint or normalization identity failed')
    return angular, radial/radial(1)


def coefficient_log_tangent(degree, angular):
    """b_0=b_1=0, -Delta_m^2 b=angular, for a_m(eps)=a_m exp(eps b_m)."""
    if type(degree) is not int or degree < 2 or not isinstance(angular, fmpq_poly):
        raise ValueError('integer degree>=2 and rational angular polynomial required')
    b = [angular(0)*0, angular(0)*0]
    for m in range(1, degree):
        b.append(2*b[-1]-b[-2]-angular(m))
    return b
