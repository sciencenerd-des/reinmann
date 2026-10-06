"""Exact obstruction to nontrivial bounded-width rectangular rank tubes.

This diagnoses the sufficient comparison, not Xi positivity or RH.
See research/RH_RANK_TUBE_WIDTH_2026_09_20.md for the all-rank proof.
"""
from fractions import Fraction

from two_sided_rank_tube import Envelope


def width_forcing_ratio(rank, shift, lower, upper):
    """exp of the necessary width acceleration, using exact ratio endpoints.

lower and upper list L<=t<=U at shifts m-1,m,m+1. A result >1
forces positive width acceleration. No array identification is assumed.
"""
    if type(rank) is not int or type(shift) is not int or rank < 1 or shift < 2:
        raise ValueError('integer rank>=1 and interior shift>=2 required')
    if len(lower) != 3 or len(upper) != 3:
        raise ValueError('three neighboring ratio bounds required')
    result = Fraction(1)
    for j, exponent, lo, hi in zip((shift-1, shift, shift+1), (1, 2, 1), lower, upper):
        lo, hi = Fraction(lo), Fraction(hi)
        if not 0 < lo <= hi <= 1:
            raise ValueError('ordered ratio bounds 0<L<=U<=1 required')
        result *= ((rank+j-j*lo)/(rank+j-j*hi))**exponent
    return result


def rational_width_obstruction(head, shift, lower, upper):
    """Prove incompatibility when globally ordered rational tubes have width.

The head+1 check detects a strict gap even if two envelopes touch at
head. Differences after clearing denominators are affine polynomials.
An equal triple has no width obstruction; it is not certified a tube.
"""
    if type(head) is not int or type(shift) is not int or head < 1 or shift < 2:
        raise ValueError('integer head>=1 and interior shift>=2 required')
    if len(lower) != 3 or len(upper) != 3 or not all(isinstance(e, Envelope) for e in (*lower, *upper)):
        raise ValueError('three lower and three upper Envelope objects required')
    for lo, hi in zip(lower, upper):
        if head+min(lo.offset, hi.offset) <= 1:
            raise ValueError('positive neighboring-rank denominators required')
        if hi.amplitude < lo.amplitude or hi.value(head) < lo.value(head) or hi.value(head) >= 1:
            raise ValueError('globally ordered positive envelopes below one required')
        if hi.offset < lo.offset:
            raise ValueError('ordered backward slopes required')
    witness = head+1
    forcing = width_forcing_ratio(witness, shift,
                                 [e.value(witness) for e in lower],
                                 [e.value(witness) for e in upper])
    return {'status': ('incompatible_bounded_width_comparison' if forcing > 1
                       else 'no_width_obstruction_not_a_tube_certificate'),
            'witness_rank': witness, 'width_acceleration_exp_lower': str(forcing),
            'scope': 'Necessary consequence of both rectangular comparison inequalities; no Xi or RH conclusion.'}
