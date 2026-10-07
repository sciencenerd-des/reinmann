"""Actual threshold complementary-resolvent bounds, conditional on written analysis.

Replays the saved full-operator gaps. No eigenvector profile or Fourier
matrix is substituted for the infinite-dimensional resolvent. The explicit
lower bound uses the previously enclosed universal actual-state L-infinity
bound. See LOCALIZED_RESOLVENT_RATE_2026_10_07.md for every analytic input.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from flint import arb, ctx

from certified_weil import endpoints
from threshold_ground_gap import box, minmax_second_bound


def localization_bounds(log_distance, gamma, bounded_remainder, state_bound):
    """Return lower/upper bounds for ||M Q(A-z)^-1 Q M||.

    E has two layers of width delta=exp(-X). gamma bounds Q(A-z)Q
    below; bounded_remainder bounds ||Dhat-B||, where Dhat equals gamma
    on the rank-one ground space. state_bound bounds the actual unit
    ground state's L-infinity norm. Inputs must already be justified.
    """
    X, g, remainder, M = map(arb, (log_distance, gamma, bounded_remainder, state_bound))
    if not X >= 32 or not g > 0 or not remainder >= 0 or not M >= 0:
        raise ValueError('X >= 32, gamma > 0 and nonnegative bounds required')
    if not all(x.is_finite() for x in (X, g, remainder, M)):
        raise ValueError('finite inputs required')
    # T=exp(X)/X^3. No exponentially large number need be constructed.
    denominator = 1+X-3*X.log()
    if not denominator > 0:
        raise ArithmeticError('positive high-frequency denominator unresolved')
    W = remainder+1
    C = W+W*W/g
    low = 2/(arb.pi()*X**3)
    upper_second = (1+C)*low+1/denominator+C/denominator**2
    # Direct energy split, with T=exp(X/2) and exp(-X/2) <= 8/X^2.
    K = remainder  # Dhat=B+bounded remainder, Dhat>=gamma on the whole space.
    upper_energy = (4/(arb.pi()*g).sqrt()/X+(2*(1+K/g)/X).sqrt())**2
    upper = min((1/g).upper(), upper_second.upper(), upper_energy.upper())
    # One sine trial in the LEFT layer, followed by ground-space removal.
    shape_energy = (1+arb.pi()**2).log()/2
    projection_cost = 8*M*M/(arb.pi()**2*g)*(-X).exp()
    lower = max(arb(0), (1/(X+shape_energy+remainder)-projection_cost).lower())
    if not upper > 0 or not lower <= upper:
        raise ArithmeticError('localized resolvent enclosure inconsistent')
    return {
        'log_inverse_layer_width': str(log_distance),
        'localized_resolvent': {'lo': str(lower.fmpq()), 'hi': str(upper.fmpq())},
        # Scale endpoints separately: constructing a single wide Arb ball
        # can inflate its radius and obscure a small positive lower bound.
        'scaled_by_log_inverse_width': {
            'lo': str((X*lower).lower().fmpq()),
            'hi': str((X*upper).upper().fmpq())},
        'second_resolvent_upper': endpoints(upper_second),
        'direct_energy_upper': endpoints(upper_energy),
        'inverse_gap_upper': endpoints(1/g),
        'second_resolvent_coefficient': endpoints(C),
    }


def generate():
    gap_source = Path('research/prime_spectral/verification_2026_10_07_trace_stability/threshold_ground_gaps.json')
    renewal_source = Path('research/prime_spectral/renewal_trace_enclosures_2026_10_07.json')
    gaps = json.loads(gap_source.read_text())
    renewal = json.loads(renewal_source.read_text())
    gap_generator = Path(__file__).with_name('threshold_ground_gap.py')
    renewal_generator = Path(__file__).with_name('renewal_trace_enclosures.py')
    for record, source in ((gaps,gap_generator),(renewal,renewal_generator)):
        if record['source_sha256'] != hashlib.sha256(source.read_bytes()).hexdigest():
            raise ArithmeticError('saved input generator hash mismatch')
    if [r['threshold_prime'] for r in gaps['results']] != [2,3]:
        raise ArithmeticError('the two expected threshold records are required')
    sources = [Path(__file__), gap_source, renewal_source,
               gap_generator,renewal_generator,Path(__file__).with_name('certified_weil.py'),
               Path('research/prime_spectral/LOCALIZED_RESOLVENT_RATE_2026_10_07.md'),
               Path('research/prime_spectral/LAYER_RESOLVENT_SCHUR_COEFFICIENT_2026_10_07.md')]
    results = []
    with ctx.workprec(256):
        constants = renewal['uniform_constants']
        E0 = (2*arb.pi()).log()+box(constants['K_operator_bound'])+box(constants['S_operator_bound'])
        state_bound = arb(3651)
        if not box(constants['unit_state_Linfty_bound']) < state_bound:
            raise ArithmeticError('saved universal eigenstate bound insufficient')
        for record in gaps['results']:
            prime = record['threshold_prime']
            input_path = Path(record['lower_operator_input'])
            if hashlib.sha256(input_path.read_bytes()).hexdigest() != record['lower_operator_sha256']:
                raise ArithmeticError('gap input hash mismatch')
            second, sectors = minmax_second_bound(json.loads(input_path.read_text()), record['shift'])
            if not second.overlaps(box(record['second_eigenvalue_lower'])):
                raise ArithmeticError('replayed second-eigenvalue bound disagrees')
            L2, U = (('999/100000','142/100000') if prime == 2 else
                     ('109/1000000000','103/1000000000'))
            L2, U = arb(L2), arb(U)
            if not second > L2 or not box(record['trial_ground_eigenvalue_upper']) < U:
                raise ArithmeticError('weakened threshold bounds fail')
            gap = L2-U
            z = U+gap/4
            gamma = L2-z
            # Dhat=A-z+(L2-lambda1)P, lambda1>=-E0.
            remainder = 2*E0+L2+z
            rows = [localization_bounds(X,gamma,remainder,state_bound)
                    for X in (32,128,512,2048,10000,1000000,100000000,10**16)]
            results.append({'threshold_prime': prime,
                            'ground_upper': endpoints(U), 'second_lower': endpoints(L2),
                            'resolvent_shift': endpoints(z), 'complement_coercivity': endpoints(gamma),
                            'bounded_lifted_remainder': endpoints(remainder),
                            'actual_ground_Linfty_bound': endpoints(state_bound), 'rows': rows})
            print('localized threshold resolvent enclosed at prime',prime,flush=True)
            sources.append(input_path)
        return {'status': 'actual_threshold_localized_resolvent_bounds_enclosed',
                'bits': 256, 'results': results,
                'analytic_scope': 'Written Dirichlet semigroup domination, second resolvent identity, inverse Jensen inequality, and the saved full-operator spectral and L-infinity bounds. Not an operator proof in Lean or an explicit moving-window gap neighborhood.',
                'source_hashes': {str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args = parser.parse_args()
    result = generate()
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
