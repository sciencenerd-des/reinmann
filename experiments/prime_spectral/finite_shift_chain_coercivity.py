"""Evaluate support-sensitive prime bounds from proved finite chain inequalities.

The Hilbert-space inequalities, translation disintegration and uniform prime
integral bound are Lean-proved. Arb evaluates their exact constant and the
written archimedean specialization; it does not certify the intermediate gap.
"""
from pathlib import Path
import hashlib
import json
from flint import arb, ctx
from weil_rank_tail_cell import global_constants, high_mode_lower, coercive_start

POWERS = [(2, 2), (3, 3), (4, 2), (5, 5), (7, 7), (8, 2),
          (9, 3), (11, 11), (13, 13), (16, 2), (17, 17)]


def envelope(constants, n, even):
    n, length = arb(n), constants['length_upper']
    diagonal = ((n / length).log() - length / (arb.pi() * n) - 1 / (4 * n)
                - length * (1 + constants['exponential_sum']) / (2 * arb.pi()**2 * n**2))
    return (diagonal - constants['arch_off_diagonal_norm'] - 2 * constants['prime_sum']
            - (arb(0) if even else constants['negative_pole_norm']))


def run():
    with ctx.workprec(1024):
        rows, total = [], arb(0)
        for power, prime in POWERS:
            length = 1
            while power ** length < 19:
                length += 1
            # Only these constants are needed and proved in FiniteShiftChains.
            factors = {1: arb(0), 2: arb(1), 3: arb(2).sqrt(), 5: arb(3).sqrt()}
            if length not in factors:
                raise ValueError('chain length outside the formalized cases')
            contribution = factors[length] * arb(prime).log() / arb(power).sqrt()
            total += contribution
            rows.append({'power': power, 'prime': prime, 'chain_length_at_most': length,
                         'integer_support_guard': 19 <= power ** length,
                         'contribution_upper': str(contribution.upper().fmpq())})
        old = global_constants(arb(17).log(), arb(19).log(), POWERS)
        improved = dict(old)
        # high_mode_lower subtracts twice this field.
        improved['prime_sum'] = total.upper() / 2
        even, full = coercive_start(improved, True), coercive_start(improved, False)
        if not (envelope(improved, even, True).lower() > 1
                and envelope(improved, even - 1, True).upper() < 1
                and envelope(improved, full, False).lower() > 1
                and envelope(improved, full - 1, False).upper() < 1):
            raise ValueError('failed outward checks on both sides of the thresholds')
        root = Path(__file__).resolve().parents[2]
        files = [Path(__file__), Path(__file__).with_name('weil_rank_tail_cell.py'),
                 root / 'Reinmann/FiniteShiftChains.lean',
                 root / 'Reinmann/SupportTranslation.lean', root / 'Reinmann/SupportPrimeForm.lean']
        return {'status': 'arb_evaluation_of_lean_prime_integral_bound_and_written_coercivity_envelope',
                'not_proved': ['Lean archimedean coercivity specialization', 'intermediate constrained gap',
                               'all-rank ground-profile budget', 'Xi identification'],
                'lower_support': 17, 'upper_support': 19, 'precision_bits': 1024,
                'rows': rows, 'prime_form_upper': str(total.upper().fmpq()),
                'old_prime_form_upper': str((2 * old['prime_sum']).upper().fmpq()),
                'even_high_mode_start': even, 'full_high_mode_start': full,
                'even_lower_at_start': str(high_mode_lower(improved, even, True).fmpq()),
                'even_upper_before_start': str(envelope(improved, even - 1, True).upper().fmpq()),
                'full_lower_at_start': str(high_mode_lower(improved, full, False).fmpq()),
                'full_upper_before_start': str(envelope(improved, full - 1, False).upper().fmpq()),
                'old_even_high_mode_start': coercive_start(old, True),
                'old_full_high_mode_start': coercive_start(old, False),
                'source_hashes': {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
                                  for p in files}}


if __name__ == '__main__':
    print(json.dumps(run(), indent=2))
