"""Modulated Turan packet calculator with every remaining hypothesis exposed."""
from flint import arb


def local_count_upper(gamma, radius):
    gamma, radius = abs(arb(gamma)), arb(radius)
    if not gamma >= arb(1).exp() or not radius >= 1:
        raise ValueError('ordinate >= e and radius >= 1 required')
    return 100*radius*(10*(gamma+radius+2)).log()


def localized_tail(a, q, gamma, radius, t):
    a, gamma, radius, t = map(arb, (a, gamma, radius, t))
    if not a > 0 or type(q) is not int or q < 2 or not t >= 0:
        raise ValueError('positive half support, q>=2 and nonnegative translation required')
    local_count_upper(gamma, radius)
    p = 2*q
    return ((q/a)**p*(a+t/2).exp()*100*p*radius**(1-p)
            *((10*(abs(gamma)+radius+2)).log()/(p-1)+1/arb(p-1)**2))


def turan_bound(m, M, h, Q, tail, partial_sum_lower, support_span, a):
    h, Q, tail, A, span, a = map(arb, (h, Q, tail, partial_sum_lower, support_span, a))
    if type(m) is not int or m < 1 or type(M) is not int or M < 0:
        raise ValueError('positive packet size and nonnegative power start required')
    if not h > 0 or not Q >= 0 or not tail >= 0 or not A > 0 or not a > 0:
        raise ValueError('positive step and partial-sum lower bound required')
    if not 2*a+(M+m)*h <= span or not Q+tail > 0:
        raise ValueError('all test translations must fit and numerator be positive')
    return (((Q+tail)/(2*A)).log()+m*(8*arb(1).exp()*(M+m)/m).log())/((M+1)*h)
