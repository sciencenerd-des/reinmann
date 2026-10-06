"""Uniform quadratic saddle moment error; no uniform curvature sign claim."""
from __future__ import annotations
import argparse
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path
from flint import arb, ctx
from laboratory import endpoints


def uniform_quadratic_bound(threshold, radius=8):
    """Bound |J_k/Q_k-1| for all real x>=threshold, k=0,1,2.

    Q_k is the truncated quadratic phase model defined in the research note.
    Constants include amplitude error and both infinite spatial tails.
    """
    X, L = Fraction(threshold), Fraction(radius)
    if X < 256 or L < 2:
        raise ValueError('threshold >=256 and standardized radius >=2 required')
    with ctx.workprec(512):
        x, ell = arb(str(X)), arb(str(L))
        u = (2*x/arb.pi()).lambertw()/2
        if not u > 1:
            raise ArithmeticError('center lower bound unresolved')
        a_lower = x*(1+2*u)
        h = ell/a_lower.sqrt()
        z = 1/(a_lower.sqrt()*u.log())
        if not ell*z < 1:
            raise ArithmeticError('positive central logarithmic weights unresolved')
        displacement = (2/arb.pi()).sqrt()*ell*(-u).exp()*h.exp()
        cubic = 3*(3*h+displacement).exp()*((2+1/u)/arb.pi()).sqrt()*(-u).exp()
        cubic += arb(9)/4*h.exp()/x**arb('1.5')
        tilt = arb(11)/2/(2*arb.pi()).sqrt()*(-u).exp()
        remainder = cubic*ell**3/6
        decay = ell-tilt-cubic*ell**2/2
        if not decay > 0:
            raise ArithmeticError('uniform tangent decay unresolved; increase threshold or reduce radius')
        amplitude = 3/(2*arb.pi())*(-2*u*(-h).exp()).exp()
        central = remainder.exp()-1+amplitude
        tail_exponent = tilt*ell-ell**2/2+remainder
        rows = []
        for k in range(3):
            polynomial = sum((arb(math.factorial(k)//math.factorial(k-j)) *
                              (1+ell*z)**(k-j)*z**j/decay**(j+1)
                              for j in range(k+1)), arb(0))
            lower = 2*(-tilt-arb('0.5')).exp()*(1-z)**k
            tails = 2*tail_exponent.exp()*polynomial/lower
            error = central+tails
            rows.append({'order': k, 'relative_error_upper': str(error.upper().fmpq()),
                         'tail_relative_upper': str(tails.upper().fmpq())})
        return {'threshold': str(X), 'standardized_radius': str(L),
                'scope': 'Every real x>=threshold; first-summand logarithmic moments k=0,1,2 relative to the truncated quadratic model Q_k.',
                'constants': {name: endpoints(value) for name,value in
                              (('u_lower',u), ('window_half_width_upper',h),
                               ('inverse_center_scale_upper',z), ('tilt_upper',tilt),
                               ('standardized_third_derivative_upper',cubic),
                               ('phase_remainder_upper',remainder), ('tangent_decay_lower',decay),
                               ('amplitude_defect_upper',amplitude), ('central_relative_upper',central))},
                'moments': rows}


def run():
    with ctx.workprec(512):
        return {'schema_version': 1,
                'status': 'uniform_quadratic_moment_error_not_curvature_certificate',
                'source_hashes': {name: hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
                                  for name in ('uniform_saddle.py','laboratory.py','coefficients.py')},
                'bounds': [uniform_quadratic_bound(x) for x in (65536,10**8,10**12)],
                'trust_boundary': 'FLINT constants plus analytic uniform inequalities in RH_UNIFORM_QUADRATIC_SADDLE_2026_09_15.md; not Lean formalized.',
                'remaining': 'The quadratic relative error is too coarse to establish uniform curvature negativity or an interior rank budget.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    result=run()
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    for row in result['bounds']:
        print(row['threshold'],arb(row['moments'][2]['relative_error_upper']))


if __name__=='__main__':
    main()
