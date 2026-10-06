"""Certify the rank-one Weil-matrix derivative kick at a prime power.

The universal endpoint derivative is proved algebraically in the research
note. This script certifies its finite lowest-eigenvalue consequence.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from flint import acb, arb, arb_mat, ctx

from certified_weil import certified_matrix, endpoints, inertia
from eigenvalue_response import _fourier_functional
from isolated_kernel import isolated_spectrum, run as isolated_run
from support_schur_recurrence import _spectral_solve
from weil_matrix import prime_powers


def _prime_power_exponent(cutoff: int) -> tuple[int, int]:
    for power, prime in prime_powers(cutoff):
        if power == cutoff:
            exponent, value = 0, 1
            while value < cutoff:
                exponent += 1
                value *= prime
            if value == cutoff:
                return prime, exponent
    raise ValueError('support threshold must be a prime power')


def certify(isolated: dict) -> dict:
    if isolated.get('status') != 'certified_finite_isolated_prime_kernel_not_uniform':
        raise ValueError('isolated finite Weil certificate required')
    cutoff, modes = isolated['cutoff'], isolated['modes']
    prime, exponent = _prime_power_exponent(cutoff)
    with ctx.workprec(512):
        _, even, _ = certified_matrix(cutoff, modes)
        values, raw = isolated_spectrum(even)
        if [endpoints(value) for value in values] != isolated['even_spectrum']:
            raise ValueError('isolated even spectrum disagrees with matrix replay')
        root_two = arb(2).sqrt()
        boundary = raw[0] + root_two * sum(raw[1:], arb(0))
        norm_squared = sum((value**2 for value in raw), arb(0))
        if boundary.contains(0) or not norm_squared > 0:
            raise ArithmeticError('nonzero boundary ground state unresolved')
        coefficient = arb(2) / (arb(exponent) * arb(cutoff).sqrt())
        unit_boundary_squared = boundary**2 / norm_squared
        jump = -coefficient * unit_boundary_squared
        if not coefficient > 0 or not unit_boundary_squared > 0 or not jump < 0:
            raise ArithmeticError('strict negative eigenvalue derivative kick unresolved')
        h = [value / raw[0] for value in raw[1:]]
        origin_boundary = arb(1) + root_two * sum(h, arb(0))
        origin_norm_squared = arb(1) + sum((value**2 for value in h), arb(0))
        if origin_boundary.contains(0) or not origin_norm_squared > 0:
            raise ArithmeticError('origin-normalized boundary unresolved')
        if not (jump + coefficient * origin_boundary**2
                / origin_norm_squared).contains(0):
            raise ArithmeticError('unit and origin-normalized boundary jumps disagree')
        constrained = [[even[i][j] - (values[0] if i == j else 0)
                        for j in range(1, modes + 1)] for i in range(1, modes + 1)]
        if inertia(constrained)[0] != 0:
            raise ArithmeticError('positive origin-constrained block unresolved')
        source = [root_two - origin_boundary * value / origin_norm_squared
                  for value in h]
        response, constrained_lowest = _spectral_solve(arb_mat(constrained), source)
        h_derivative_jump = [coefficient * origin_boundary * value for value in response]
        length = arb(cutoff).log()
        profile_jumps = {}
        for name, argument in (('real_4', acb(4)), ('real_8', acb(8)),
                               ('imag_1', acb(0, 1))):
            functional = _fourier_functional(modes, length, argument)
            profile_jumps[name] = endpoints(sum(
                (value * change for value, change in
                 zip(functional[1:], h_derivative_jump)), arb(0)))
        return {
            'status': 'certified_finite_negative_prime_threshold_derivative_jump',
            'cutoff': cutoff, 'modes': modes, 'prime': prime, 'exponent': exponent,
            'working_bits': 512,
            'full_matrix_entry_derivative_jump': endpoints(-coefficient),
            'unit_ground_boundary_squared': endpoints(unit_boundary_squared),
            'lowest_even_eigenvalue_derivative_jump': endpoints(jump),
            'origin_normalized_boundary_evaluation': endpoints(origin_boundary),
            'new_origin_constrained_lowest_eigenvalue': endpoints(constrained_lowest),
            'ground_coefficient_derivative_jump': [endpoints(x) for x in h_derivative_jump],
            'ground_profile_derivative_jump': profile_jumps,
            'formula': ('At C=p^k, dA_even/dlog(C)|right - dA_even/dlog(C)|left '
                        '= -2/(k*sqrt(C))*u*u^T, u=(1,sqrt(2),...,sqrt(2)); '
                        'the simple lowest eigenvalue derivative jump is '
                        '-2/(k*sqrt(C))*(u.v)^2/(v.v).'),
            'scope': ('One-sided eigenvalue and ground-profile derivative jumps '
                      'at one finite prime-power support threshold, assuming '
                      'the certified simple-even and nonzero-origin gates.'),
            'remaining': ('No sign control between thresholds, cumulative '
                          'support variation, growing-rank gate, or RH proof.'),
        }


def run(isolated_path: Path) -> dict:
    raw = isolated_path.read_bytes()
    isolated = json.loads(raw)
    source_dir = Path(__file__).parent
    for name, digest in isolated['source_hashes'].items():
        if hashlib.sha256((source_dir / name).read_bytes()).hexdigest() != digest:
            raise ValueError('stale isolated Weil source: ' + name)
    if isolated_run(isolated['cutoff'], isolated['modes']) != isolated:
        raise ValueError('isolated Weil certificate replay disagrees')
    result = certify(isolated)
    result['input_sha256'] = hashlib.sha256(raw).hexdigest()
    result['source_hashes'] = {
        name: hashlib.sha256((source_dir / name).read_bytes()).hexdigest()
        for name in ('prime_threshold_jump.py', 'certified_weil.py',
                     'isolated_kernel.py', 'weil_matrix.py',
                     'support_schur_recurrence.py', 'eigenvalue_response.py')}
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--isolated', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = run(args.isolated)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(result['status'], result['cutoff'], result['modes'])


if __name__ == '__main__':
    main()
