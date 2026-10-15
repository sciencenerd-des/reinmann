"""Fixed-support Fourier bounds for the genuine Weil ground state.

The finite arithmetic is replayed in Arb. Its interpretation for the full
operator uses the written comparison/min-max and compact-resolvent proofs.
This extends the existing form-level strip transfer to full-operator inputs;
it is not a new abstract spectral theorem or a growing-support certificate.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from flint import arb, ctx

from certified_weil import certified_matrix, endpoints, inertia
from compact_window_certificate import bounds
from strip_transfer import normalized_profile_upper, strip_functional_norm
from threshold_ground_gap import box
from weil_matrix import prime_powers

OUTPUT = Path('research/prime_spectral/verification_2026_10_11_fourier_ground_state')
TRIALS = Path('research/prime_spectral/verification_2026_10_07_assembled_trial/assembled_trials.json')


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def require_replay(replay_path, certificate_path):
    replay = json.loads(Path(replay_path).read_text())
    if (replay.get('status') != 'verified_full_window_certificate'
            or replay.get('certificate_sha256') != sha256(certificate_path)
            or replay.get('verifier_sha256') != sha256(Path(__file__).with_name('verify_window_positivity.py'))
            or replay.get('independent_adaptive_integral_entries') != [[0,0],[0,2],[1,1],[1,3]]
            or replay.get('independent_geometric_constant_check') is not True):
        raise ValueError('current independently integrated comparison replay required')


def energy_distance(rayleigh_upper, ground_lower, second_lower):
    """Sharp phase distance from a lower form bound and a second-level bound.

    With unit trial f and ground vector u, the orthogonal mass t obeys
    t <= (mu-ell)/(b-ell). Then ||f-u||^2 = 2(1-sqrt(1-t)).
    Only lower bounds ell,b are needed; ell may be negative.
    """
    mu, ell, b = map(arb, (rayleigh_upper, ground_lower, second_lower))
    if not all(x.is_finite() for x in (mu, ell, b)):
        raise ValueError('finite spectral inputs required')
    # These exact outward endpoints are valid monotone inputs to the ratio.
    mu, ell, b = arb(mu.upper()), arb(ell.lower()), arb(b.lower())
    if not ell <= mu or not mu < b:
        raise ArithmeticError('ground lower <= trial upper < full second lower required')
    t = (mu-ell)/(b-ell)
    if not 0 <= t < 1:
        raise ArithmeticError('orthogonal-mass ratio unresolved')
    # Rationalized expression avoids cancellation for a nearly exact trial.
    distance = (2*t/(1+(1-t).sqrt())).sqrt()
    return t, distance


def comparison_spectrum(path, prime, finite_floor, second_shift):
    """Replay both parities and the entire polynomial-complement allowance.

    No quadrature entries are recomputed here. Their generation and analytic
    quadrature allowance are explicit dependencies, not an independent replay.
    """
    path = Path(path)
    data = json.loads(path.read_text())
    if data['status'] != 'certified_full_window_lower_bound':
        raise ValueError('full comparison certificate required')
    expected_sources = ('compact_window_certificate.py', 'certified_weil.py', 'weil_matrix.py')
    for name in expected_sources:
        if data['source_hashes'].get(name) != sha256(Path(__file__).with_name(name)):
            raise ValueError('comparison source mismatch: '+name)
    a = arb(data['half_width'])
    if prime not in (2, 3) or not 0 < a <= 1 or not 2*a > arb(prime).log():
        raise ValueError('comparison must contain the intended threshold support')
    c = (2*a).exp()
    powers = [(q, p) for q, p in prime_powers(int(c.ceil().fmpq()))
              if arb(q).log() < 2*a]
    if data['active_prime_powers'] != [list(p) for p in powers]:
        raise ValueError('prime content mismatch')
    count = data['polynomial_count']
    if type(count) is not int or count < 2 or count % 2:
        raise ValueError('positive even compression size required')
    beta, quad, coupling, tail, _ = bounds(
        a, data['cutoff'], count, data['gauss_order'], powers)
    for name, value in [('C', c), ('beta', beta), ('quadrature_operator_error', quad),
                        ('infinite_coupling_bound', coupling), ('infinite_tail_deviation', tail)]:
        if not box(data[name]).contains(value):
            raise ValueError('constant does not enclose recomputation: '+name)
    floor, shift = map(arb, (finite_floor, second_shift))
    if not floor.is_finite() or not shift.is_finite() or not floor < shift < beta:
        raise ValueError('finite floor < second shift < complement level required')
    if len(data['sectors']) != 2:
        raise ValueError('both parity sectors required')
    records = []
    for parity, sector in zip(('even', 'odd'), data['sectors'], strict=True):
        matrix = [[box(e) for e in row] for row in sector['quadrature_matrix']]
        if (sector['parity'] != parity or sector['dimension'] != count//2
                or len(matrix) != count//2 or any(len(row) != count//2 for row in matrix)):
            raise ValueError('parity or matrix dimension mismatch')
        if any(not matrix[i][j].overlaps(matrix[j][i])
               for i in range(len(matrix)) for j in range(i)):
            raise ValueError('matrix symmetry unresolved')
        low_count, low_pivots = inertia(matrix, floor+quad)
        second_count, second_pivots = inertia(matrix, shift+quad)
        if low_count != 0:
            raise ArithmeticError('proposed finite ground lower bound failed')
        records.append({'parity': parity, 'ground_shift_negative_count': low_count,
                        'second_shift_negative_count': second_count,
                        'ground_shift_pivots': [endpoints(x) for x in low_pivots],
                        'second_shift_pivots': [endpoints(x) for x in second_pivots]})
    if sum(row['second_shift_negative_count'] for row in records) != 1:
        raise ArithmeticError('exactly one eigenvalue below the second shift required')
    # R >= (G-quad) direct_sum beta - (coupling+tail)I, and A >= R.
    # Restricting support raises the eigenvalues by form min-max.
    return {'ground_lower': floor-coupling-tail,
            'second_lower': shift-coupling-tail,
            'sectors': records, 'half_width': data['half_width'],
            'finite_floor': finite_floor, 'second_shift': second_shift,
            'comparison_sha256': sha256(path)}


def certify_trial(prime, coefficients, ground_lower, second_lower, heights):
    """Exact decimal cosine trial in the full form domain, not a Ritz state."""
    if prime not in (2, 3) or len(coefficients) != 9:
        raise ValueError('supported threshold and nine exact cosine coefficients required')
    c = list(map(arb, coefficients))
    norm_sq = sum((x*x for x in c), arb(0))
    if not all(x.is_finite() for x in c) or not norm_sq > 0 or not c[0] > 0:
        raise ValueError('finite nonzero trial with positive mean required')
    _, matrix, _ = certified_matrix(prime, 8)
    mu = sum((c[i]*matrix[i][j]*c[j] for i in range(9) for j in range(9)), arb(0))/norm_sq
    mean = c[0]/norm_sq.sqrt()
    mass, distance = energy_distance(mu, ground_lower, second_lower)
    d = arb(distance.upper())
    mean_lower = arb(mean.lower())-d
    if not mean_lower > 0:
        raise ArithmeticError('ground Fourier value at zero not protected')
    length = arb(prime).log()
    strips = []
    for height in heights:
        y = arb(height)
        if not y.is_finite() or not 0 <= y < arb(1)/2:
            raise ValueError('strip heights must lie in [0,1/2)')
        # strip_functional_norm includes 1/sqrt(length). The raw Fourier
        # integral has norm sqrt(length)*W, with centered coordinate.
        W = strip_functional_norm(length, y)
        strips.append({'height': height,
                       'raw_fourier_error_upper': endpoints(length.sqrt()*W*d),
                       'origin_normalized_profile_error_upper': endpoints(
                           arb(normalized_profile_upper(length, y, mean, d)))})
    return {'threshold_prime': prime, 'support_length': endpoints(length),
            'exact_cosine_coefficients': coefficients,
            'trial_rayleigh_enclosure': endpoints(mu),
            'trial_mean_coefficient': endpoints(mean),
            'full_ground_lower': endpoints(ground_lower),
            'full_second_lower': endpoints(second_lower),
            'full_gap_lower': endpoints(arb(second_lower)-mu),
            'orthogonal_mass_upper': endpoints(mass),
            'oriented_unit_ground_distance_upper': endpoints(distance),
            'ground_mean_lower': endpoints(mean_lower),
            'ground_raw_fourier_at_zero_lower': endpoints(length.sqrt()*mean_lower),
            'strips': strips,
            'interpretation': 'Whole-operator ground-state enclosure conditional on the written comparison and form-realization proofs; not a finite eigenvector comparison.'}


def generate(directory=OUTPUT, band=128):
    directory = Path(directory)
    # Require the independently integrated baseline rather than manufacturing
    # a validation label from the existence of an old certificate.
    replay_path = directory/'baseline_replay.json'
    require_replay(replay_path, 'research/prime_spectral/window_positivity_exp_1p2.json')
    old = json.loads(TRIALS.read_text())
    for name, digest in old['source_hashes'].items():
        if sha256(name) != digest:
            raise ValueError('trial provenance source mismatch: '+name)
    rows = []
    if band == 64:
        comparisons = [(2, 'near_two_lower_operator.json', '11/10000', '57/1000'),
                       (3, 'near_three_lower_operator.json', '1/100000000', '103/25000000')]
    elif band == 128:
        comparisons = [(2, 'band128_two_lower_operator.json', '1/800', '57/1000'),
                       (3, 'band128_three_lower_operator.json', '1/25000000', '103/25000000')]
    else:
        raise ValueError('supported frequency bands are 64 and 128')
    with ctx.workprec(512):
        for prime, filename, floor, shift in comparisons:
            path = directory/filename
            comparison_replay = directory/filename.replace('_lower_operator', '_replay')
            require_replay(comparison_replay, path)
            spectrum = comparison_spectrum(path, prime, floor, shift)
            witness = next(row for row in old['results'] if row['threshold_prime'] == prime)
            row = certify_trial(prime, witness['cosine_coefficients'], spectrum['ground_lower'],
                                spectrum['second_lower'], ['0', '2/5', '49/100'])
            row['comparison'] = {k: v for k, v in spectrum.items()
                                 if k not in ('ground_lower', 'second_lower')}
            row['comparison']['independent_replay_sha256'] = sha256(comparison_replay)
            rows.append(row)
            print('full ground Fourier enclosure computed at prime', prime, flush=True)
    sources = [Path(__file__), *[Path(__file__).with_name(name) for name in
               ('strip_transfer.py', 'compact_window_certificate.py', 'certified_weil.py',
                'weil_matrix.py', 'threshold_ground_gap.py')]]
    return {'status': 'fixed_support_full_ground_fourier_enclosures', 'bits': 512, 'frequency_band': band,
            'results': rows, 'source_hashes': {str(p): sha256(p) for p in sources},
            'trial_input_sha256': sha256(TRIALS), 'baseline_replay_sha256': sha256(replay_path),
            'scope': 'Arb arithmetic plus written infinite-dimensional comparison, compactness and spectral decomposition. No new endpoint-trace theorem, all-support rate, Xi identification, novelty clearance, or RH proof.'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--directory', type=Path, default=OUTPUT)
    parser.add_argument('--band', type=int, choices=[64,128], default=128)
    args = parser.parse_args()
    output = generate(args.directory, args.band)
    encoded = json.dumps(output, indent=2)+'\n'
    (args.directory/f'full_ground_fourier_band{args.band}.json').write_text(encoded)
    if args.band == 128:
        (args.directory/'full_ground_fourier.json').write_text(encoded)
