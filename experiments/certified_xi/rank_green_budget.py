"""Exact growing-mode balance and bounded forcing for the N=2 control.

All-rank result is conditional on this scalar control equation, not Xi.
The finite prefix is followed by F_r=-2*tail/[r*(r+2)].
"""
from fractions import Fraction


def solve_prefix(initial, forcing):
    """Solve e_0=0, e_1=initial with exact rational forcing at ranks 1,... ."""
    values = [Fraction(0), Fraction(initial)]
    for r, source in enumerate(forcing, 1):
        values.append(2*values[-1]-values[-2]
                      +Fraction(2, r*(r+2))*values[-1]+Fraction(source))
    return values


def green_value(rank, initial, forcing):
    if type(rank) is not int or rank < 1 or len(forcing) < rank-1:
        raise ValueError('positive integer rank and complete forcing prefix required')
    y = Fraction(rank*(rank+2), 3)
    d = Fraction(1, rank+1)
    return y*Fraction(initial)+sum(
        ((y/Fraction(k+1)-d*Fraction(k*(k+2), 3))*Fraction(forcing[k-1])
         for k in range(1, rank)), Fraction(0))


def budget(initial, prefix, tail, bound):
    """Exact infinite moment using a finite prefix and a specified analytic tail.

The caller's actual residual identification is a separate hypothesis.
An imbalanced result proves growth for the specified scalar model only.
"""
    initial, tail, bound = map(Fraction, (initial, tail, bound))
    prefix = list(map(Fraction, prefix))
    if bound <= 0 or abs(tail) > bound:
        raise ValueError('positive forcing bound and |tail|<=bound required')
    if any(abs(f) > Fraction(2, r*(r+2))*bound for r, f in enumerate(prefix, 1)):
        raise ValueError('prefix violates the forcing envelope')
    start = len(prefix)+1
    amplitude = initial+sum((f/Fraction(r+1) for r, f in enumerate(prefix, 1)), Fraction(0))
    amplitude -= tail/Fraction(start*(start+1))
    return {'status': ('conditional_all_rank_bounded_scalar_response' if amplitude == 0
                       else 'nonzero_growing_mode_in_scalar_control'),
            'tail_start': start, 'growing_amplitude': str(amplitude),
            'forcing_bound': str(bound),
            'claim': ('|e_r|<=bound*r/(r+1) for every r>=0' if amplitude == 0
                      else 'e_r/[r*(r+2)/3] tends to growing_amplitude'),
            'scope': 'Specified N=2 scalar equation and analytic forcing tail only; not a Xi certificate.'}
