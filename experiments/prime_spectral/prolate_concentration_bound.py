"""Evaluate established nonasymptotic PSWF concentration bounds with Arb.

These bounds concern the compressed Fourier operator, not the Weil form.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from flint import arb, ctx

from certified_weil import endpoints


def run(cutoff: int) -> dict:
    if type(cutoff) is not int or cutoff < 2:
        raise ValueError('integer cutoff at least 2 required')
    with ctx.workprec(256):
        c = 2 * arb.pi() * cutoff
        if not 4 < 2 * c / (arb(27) / 10):
            raise ArithmeticError('PSWF bound index range unresolved')
        exponential = (-c).exp()
        b0 = 7 * exponential / c.sqrt()
        b4 = arb(14) / 3 * c**3 * c.sqrt() * exponential
        if not b0 < 1 or not b4 < 1:
            raise ArithmeticError('positive compressed-Fourier lower bound unresolved')
        theta0_lower = (1 - b0).sqrt()
        theta4_lower = (1 - b4).sqrt()
        origin_factor = (b0 + b4) / theta0_lower
        fourier_base = 2 * b4
        fourier_ratio_coefficient = 2 * b0 / (1 - b0)
        return {
            'schema_version': 1,
            'status': 'analytic_prolate_compression_bounds_not_weil_transfer',
            'cutoff': cutoff,
            'working_bits': 256,
            'bandwidth_c': endpoints(c),
            'concentration_deficit_0_upper': str(b0.upper().fmpq()),
            'concentration_deficit_4_upper': str(b4.upper().fmpq()),
            'compressed_fourier_theta_0_lower': str(theta0_lower.lower().fmpq()),
            'compressed_fourier_theta_4_lower': str(theta4_lower.lower().fmpq()),
            'origin_defect_per_abs_a4_upper': str(origin_factor.upper().fmpq()),
            'fourier_defect_squared_base_upper': str(fourier_base.upper().fmpq()),
            'fourier_defect_squared_ratio_coefficient_upper': str(
                fourier_ratio_coefficient.upper().fmpq()),
            'source': 'https://arxiv.org/html/2006.00427, section 3.2',
            'generator_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'scope': ('For exact prolate modes 0 and 4: |h_I(0)|/|a_4| and '
                      '||Fh_I-h_I||^2 <= base + coefficient*|a_4/a_0|^2. '
                      'The literature PSWF inequality is an analytic input.'),
            'remaining': ('The asymptotic map E leakage bound has no effective '
                          'finite-cutoff constant. No Weil residual-over-gap '
                          'bound or all-support RH proof is supplied.'),
        }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cutoff', type=int, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = run(args.cutoff)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(result['status'])


if __name__ == '__main__':
    main()
