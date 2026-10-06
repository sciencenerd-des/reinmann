"""Quantitative spectral-to-Fourier-profile bounds on horizontal strips.

This is a conditional finite-dimensional transfer tool. It neither proves a
uniform Weil-form spectral gap nor identifies a candidate with Xi.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction
from pathlib import Path

from flint import arb

from certified_weil import endpoints


def strip_functional_norm(length, height):
    """L2 operator norm of the centered Fourier functional for |Im z|<=height."""
    length, height = arb(length), arb(height)
    if not length.is_finite() or not height.is_finite() or not length > 0 or not height >= 0:
        raise ValueError('positive finite support length and nonnegative finite strip height required')
    if height == 0:
        return arb(1)
    t = length*height
    if not t > 0:
        raise ArithmeticError('positive strip product unresolved')
    return (t.sinh()/t).sqrt()


def residual_distance_upper(rayleigh, residual_upper, second_eigen_lower):
    """Distance to the oriented lowest unit eigenvector from residual/gap data.

    Requires the candidate Rayleigh quotient to lie below the second
    eigenvalue. The supplied residual bound must enclose ||(A-mu I)w||.
    """
    rayleigh, residual, second = (arb(rayleigh), arb(residual_upper),
                                  arb(second_eigen_lower))
    if not all(x.is_finite() for x in (rayleigh, residual, second)) or not residual >= 0:
        raise ValueError('finite Rayleigh, nonnegative residual and eigenvalue inputs required')
    clearance = second.lower()-rayleigh.upper()
    if not clearance > 0:
        raise ArithmeticError('candidate Rayleigh quotient is not below the second eigenvalue')
    return (arb(2).sqrt()*residual.upper()/clearance).upper()


def rayleigh_distance_upper(rayleigh, lowest_eigen, second_eigen):
    """Distance to the oriented ground state from Rayleigh excess/gap.

    For a unit vector, the orthogonal mass is at most
    (Rayleigh-lowest)/(second-lowest). This form-level bound avoids an
    operator residual but needs enclosures of both eigenvalues.
    """
    mu, lowest, second = arb(rayleigh), arb(lowest_eigen), arb(second_eigen)
    if not all(value.is_finite() for value in (mu, lowest, second)):
        raise ValueError('finite spectral interval inputs required')
    gap = second.lower() - lowest.upper()
    excess = mu.upper() - lowest.lower()
    if not gap > 0 or not second.lower() - mu.upper() > 0 or not excess >= 0:
        raise ArithmeticError('Rayleigh-below-second or positive-gap gate unresolved')
    return (arb(2) * excess / gap).sqrt().upper()


def normalized_profile_upper(length, height, candidate_central_lower, distance_upper):
    """Uniform profile difference bound on the full closed horizontal strip.

    The two even Fourier coefficient vectors are unit vectors, oriented so
    their distance is at most distance_upper. The candidate's zeroth
    orthonormal coordinate has absolute value at least candidate_central_lower.
    """
    central, distance = arb(candidate_central_lower), arb(distance_upper)
    if not central.is_finite() or not distance.is_finite() or not central > 0 or not distance >= 0:
        raise ValueError('positive finite central lower bound and nonnegative distance required')
    c = central.lower()
    e = distance.upper()
    if not c-e > 0:
        raise ArithmeticError('origin normalization not protected by vector error')
    weight = strip_functional_norm(length, height)
    return (weight*e/(c-e)*(1+1/c)).upper()


def finite_comparison(comparison_path: Path, height='2/5') -> dict:
    data = json.loads(comparison_path.read_text())
    if data.get('status') != 'certified_finite_nested_mode_comparison_not_convergence':
        raise ValueError('certified nested-mode comparison required')
    source = Path(__file__).with_name('certified_mode_comparison.py')
    if data.get('source_hash') != hashlib.sha256(source.read_bytes()).hexdigest():
        raise ValueError('stale nested-mode comparison')
    height_fraction = Fraction(height)
    if not 0 <= height_fraction < Fraction(1, 2):
        raise ValueError('strip height must lie in [0,1/2)')
    sigma = arb(str(height_fraction))
    distance = arb(data['origin_normalized_coefficient_distance']['lo']).union(
        arb(data['origin_normalized_coefficient_distance']['hi']))
    if not distance >= 0:
        raise ArithmeticError('nonnegative coefficient distance unresolved')
    length = arb(data['cutoff']).log()
    weight = strip_functional_norm(length, sigma)
    return {
        'schema_version': 1,
        'status': 'finite_strip_profile_comparison_not_convergence',
        'cutoff': data['cutoff'],
        'mode_pair': data['mode_pair'],
        'strip_height': str(height_fraction),
        'functional_norm': endpoints(weight),
        'profile_difference_upper': str((weight*distance).upper().fmpq()),
        'real_axis_difference_upper': str(distance.upper().fmpq()),
        'comparison_sha256': hashlib.sha256(comparison_path.read_bytes()).hexdigest(),
        'source_hashes': {
            name: hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
            for name in ('strip_transfer.py', 'certified_mode_comparison.py')
        },
        'scope': 'All complex z with |Im z|<=strip_height, for this one fixed-support pair.',
        'remaining': 'No candidate-to-Weil residual estimate along an infinite family and no Xi limit.',
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--comparison', required=True, type=Path)
    parser.add_argument('--height', default='2/5')
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    result = finite_comparison(args.comparison, args.height)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(result['status'], arb(result['profile_difference_upper']))


if __name__ == '__main__':
    main()
