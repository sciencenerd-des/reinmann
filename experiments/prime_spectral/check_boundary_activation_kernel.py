"""Check the proposed comparison-kernel Fourier normalization with Arb.

This checks four frequencies, not the semigroup/PDE proof or Weil positivity.
The analytic tail allowance is 5 exp(-R/2), from the written global kernel bound.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from flint import acb, arb, ctx

from certified_weil import endpoints


def remainder_kernel(z):
    """Analytic near zero, with its removable singularity explicitly removed."""
    if abs(z) < 1:
        sinhc = (z*z/4).hypgeom_0f1(arb(3)/2)
        divided_sinhc = z/6 * (z*z/4).hypgeom([1], [2, arb(5)/2])
        return ((-z).hypgeom_1f1(1, 2)*(-1)
                + (divided_sinhc - (z/2).hypgeom_1f1(1, 2)/2)/sinhc)/2
    return (-z).exp()/(2*z) - (z/2).exp()/(2*z.sinh())


def check():
    records = []
    with ctx.workprec(160):
        cutoff = 128
        tail = 5 * (-arb(cutoff)/2).exp()
        assert remainder_kernel(acb(0)).real.contains(-arb(3)/4)
        for frequency in ('0', '1/2', '2', '7'):
            t = arb(frequency)

            def integrand(z, analytic):
                return 2*remainder_kernel(z)*(t*z).cos()

            tol = arb(2)**-100
            value = sum((acb.integral(integrand, j, j+4,
                                     abs_tol=tol, rel_tol=tol,
                                     eval_limit=200000)
                         for j in range(0, cutoff, 4)), acb(0))
            if (not value.is_finite() or not value.imag.contains(0)
                    or not value.real.rad() < arb('1e-28')):
                raise ArithmeticError('kernel integral unresolved: '+frequency)
            enclosure = value.real + arb(0, tail.upper())
            expected = (acb(arb(1)/4, t/2).digamma().real - arb.pi().log()
                        - (1+t*t).log()/2 + (2*arb.pi()).log())
            if not enclosure.contains(expected):
                raise ArithmeticError('comparison-kernel normalization failed: '+frequency)
            records.append({'frequency': frequency, 'transform_enclosure': endpoints(enclosure),
                            'symbol_enclosure': endpoints(expected)})
            print('kernel transform checked at', frequency, flush=True)
        return {'status': 'four_kernel_normalizations_checked',
                'bits': 160, 'spatial_cutoff': cutoff,
                'absolute_tail_allowance': endpoints(tail), 'checks': records,
                'scope': 'Finite normalization checks; not a proof of the semigroup bound, boundary theorem, RH, or novelty.',
                'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = check()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
