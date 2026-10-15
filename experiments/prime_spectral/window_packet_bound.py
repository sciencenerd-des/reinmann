"""Packet-dependent window/zero bound, with an explicit infinite zeta tail.

This is a calculator for the theorem in WINDOW_PACKET_THEOREM_2026_10_12.md.
It does not certify a supplied zero list is complete, instantiate window
positivity, or eliminate the packet's separation constants.
"""
from flint import acb, acb_mat, arb


def spline_transform(z, half_width, order):
    if type(order) is not int or order < 2 or not arb(half_width) > 0:
        raise ValueError('positive half-width and integer order >=2 required')
    w = acb(z)*arb(half_width)/order
    # sinh(w)/w = sinc(i*w), including its removable value at zero.
    return (acb(0, 1)*w).sinc()**order


def zeta_zero_tail(half_width, order, height, translation):
    """All |gamma|>T, using 2N(u)<=10*u*log(10*u), u>=e."""
    a, T, t = map(arb, (half_width, height, translation))
    if type(order) is not int or order < 2 or not a > 0 or not T >= arb(1).exp() or not t >= 0:
        raise ValueError('a>0, q>=2, T>=e, t>=0 required')
    p = 2*order
    moment = 10*p*T**(1-p)*((10*T).log()/(p-1)+arb(1)/(p-1)**2)
    return (arb(order)/a)**p*(a+t/2).exp()*moment


def packet_bound(nodes, weights, step, initial, q0_upper, tail_upper):
    """delta_i <= log(R_i*(Q+tail)/|weight_i|)/(initial*step).

    nodes are centered zeros rho-1/2, including all distinct zeros in the
    chosen complete packet; weights include multiplicity. The caller must
    justify completeness and the tail. Near collisions fail closed.
    """
    h, Q, tail = map(arb, (step, q0_upper, tail_upper))
    if (type(initial) is not int or initial < 1 or not h > 0 or not Q >= 0
            or not tail >= 0 or not nodes or len(nodes) != len(weights)):
        raise ValueError('consistent packet and nonnegative bounds required')
    z = [(acb(r)*h).exp() for r in nodes]
    V = acb_mat([[w**j for w in z] for j in range(len(z))])
    try:
        inverse = V.inv()
    except (ZeroDivisionError, ValueError) as exc:
        raise ArithmeticError('packet nodes collide or inverse is unresolved') from exc
    out = []
    for i, weight in enumerate(weights):
        w = abs(acb(weight))
        if not w > 0:
            raise ArithmeticError('nonzero packet weight required')
        R = sum((abs(inverse[i, j]) for j in range(len(z))), arb(0))
        if not R.is_finite() or not Q+tail > 0:
            raise ArithmeticError('packet inverse or positive total bound unresolved')
        out.append((R*(Q+tail)/w).log()/(initial*h))
    return out
