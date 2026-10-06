"""Finite inverse-filter overlap bound for a rounded prolate candidate.

The filter estimate is exact spectral algebra.  Its finite overlap input uses
the already certified Weil eigenvector and proves no uniform overlap theorem.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from flint import arb, ctx

from certified_mode_comparison import box, normalized_vector
from certified_weil import endpoints
from quotient_operator import fourier_profile
from strip_transfer import normalized_profile_upper


def filter_distance_upper(alpha: arb, beta: arb,
                          lowest: arb, second: arb, tau: arb = arb(0)) -> arb:
    """Bound ||v - normalized((A+tau I)^-1 w)|| by the spectral theorem."""
    if not all(x.is_finite() for x in (alpha, beta, lowest, second, tau)):
        raise ValueError('finite filter inputs required')
    if not alpha > 0 or not beta >= 0 or not lowest > 0 or not second > lowest or not tau >= 0:
        raise ValueError('positive simple-lowest spectral filter inputs required')
    ratio = (lowest.upper() + tau.upper()) / (second.lower() + tau.lower())
    return (arb(2).sqrt() * ratio * beta.upper() / alpha.lower()).upper()


def run(certificate_path: Path, candidate_path: Path, height: str = '2/5') -> dict:
    sigma = Fraction(height)
    if sigma < 0 or sigma >= Fraction(1, 2):
        raise ValueError('strip height must lie in [0,1/2)')
    cert_raw = certificate_path.read_bytes()
    candidate_raw = candidate_path.read_bytes()
    certificate = json.loads(cert_raw)
    candidate = json.loads(candidate_raw)
    if candidate.get('status') != 'rounded_finite_prolate_candidate_above_second_eigenvalue':
        raise ValueError('rounded prolate failure diagnostic required')
    if candidate['input_sha256'] != hashlib.sha256(cert_raw).hexdigest():
        raise ValueError('candidate and Weil matrix inputs disagree')
    if ((candidate['cutoff'], candidate['modes']) !=
            (certificate['cutoff'], certificate['modes']) or
            len(candidate['rounded_candidate_coefficients']) != certificate['modes']+1):
        raise ValueError('candidate does not match the certified even Fourier space')
    source = Path(__file__).with_name('prolate_candidate_diagnostic.py')
    if candidate['generator_sha256'] != hashlib.sha256(source.read_bytes()).hexdigest():
        raise ValueError('stale candidate generator')
    for name, digest in certificate['source_hashes'].items():
        if hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest() != digest:
            raise ValueError('stale Weil certificate source')
    with ctx.workprec(512):
        _, v, _ = normalized_vector(certificate)
        w = [arb(value) for value in candidate['rounded_candidate_coefficients']]
        norm = sum((x*x for x in w), arb(0)).sqrt()
        if not norm > 0:
            raise ArithmeticError('candidate unit normalization unresolved')
        w = [x/norm for x in w]
        alpha = abs(sum((x*y for x, y in zip(w, v)), arb(0)))
        beta = (1-alpha*alpha).sqrt()
        lam0 = box(certificate['smallest_even_eigenvalue'])
        lam1 = box(certificate['second_even_eigenvalue'])
        distance = filter_distance_upper(alpha, beta, lam0, lam1)
        central = (abs(v[0]).lower()-distance).lower()
        if not central > distance:
            raise ArithmeticError('filtered Fourier origin not protected')
        length = arb(certificate['cutoff']).log()
        profile = normalized_profile_upper(length, arb(str(sigma)), central, distance)
        modes = certificate['modes']
        root_two = arb(2).sqrt()

        def even_full(vector):
            return [vector[abs(j)]/root_two if j else vector[0]
                    for j in range(-modes, modes+1)]

        distortion = {}
        for frequency in (4, 8):
            prolate_value = fourier_profile(even_full(w), length, frequency)
            ground_value = fourier_profile(even_full(v), length, frequency)
            if not prolate_value.imag.contains(0) or not ground_value.imag.contains(0):
                raise ArithmeticError('real even profile check unresolved')
            separation = abs(prolate_value.real-ground_value.real)
            lower = (separation.lower()-profile).lower()
            distortion[str(frequency)] = {
                'prolate_ground_separation': endpoints(separation),
                'prolate_filtered_difference_lower': str((lower if lower > 0 else arb(0)).fmpq()),
            }
        return {
            'schema_version': 1,
            'status': 'finite_inverse_filter_transfer_not_convergence',
            'cutoff': certificate['cutoff'], 'modes': certificate['modes'],
            'strip_height': str(sigma),
            'unfiltered_ground_overlap': endpoints(alpha),
            'unfiltered_orthogonal_norm': endpoints(beta),
            'lowest_over_second_upper': str((lam0.upper()/lam1.lower()).upper().fmpq()),
            'filtered_unit_distance_upper': str(distance.fmpq()),
            'filtered_central_lower': str(central.fmpq()),
            'filtered_profile_difference_upper': str(profile.fmpq()),
            'profile_distortion_at_real_frequency': distortion,
            'certificate_sha256': hashlib.sha256(cert_raw).hexdigest(),
            'candidate_sha256': hashlib.sha256(candidate_raw).hexdigest(),
            'source_hashes': {name: hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
                              for name in ('filtered_candidate_transfer.py', 'certified_mode_comparison.py',
                                           'strip_transfer.py', 'quotient_operator.py',
                                           'prolate_candidate_diagnostic.py')},
            'scope': ('The filtered vector is defined using the exact finite Weil matrix. '
                      'Its distance to that finite ground state, and lower bounds on '
                      'its profile distortion from the rounded prolate vector, are '
                      'certified from the finite overlap and gap.'),
            'remaining': ('No uniform overlap, gap ratio, filtered-candidate Xi limit, '
                          'or finite-to-continuous Weil comparison is proved.'),
        }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate', type=Path, required=True)
    parser.add_argument('--candidate', type=Path, required=True)
    parser.add_argument('--height', default='2/5')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = run(args.certificate, args.candidate, args.height)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(result['status'], result['filtered_unit_distance_upper'])


if __name__ == '__main__':
    main()
