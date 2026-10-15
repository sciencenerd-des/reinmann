"""Arb solid Toeplitz minors by exact Desnanot--Jacobi condensation.

An unresolved divisor poisons its descendants; no guessed sign is accepted.
Only a finite grid is scanned. Positive results do not establish PF at that rank.
"""
import argparse
import hashlib
import json
from pathlib import Path
import time

from flint import arb, ctx

from certified_weil import endpoints
from dh_toeplitz_scan import coefficients, solid_minor
from full_ground_fourier import sha256

OUT = Path('research/prime_spectral/verification_2026_10_12_sector')


def condensate(mu, max_rank, max_shift, min_rank=1, progress=None):
    width = max_rank+max_shift
    if len(mu) <= width or not mu[0] == 1:
        raise ValueError('normalized coefficients through rank+shift required')
    older, previous = [arb(1)]*(width+1), list(mu[:width+1])
    rows, checks, first = [], [], None
    digest = hashlib.sha256()
    for rank in range(1, max_rank+1):
        if rank == 1:
            current = previous
        else:
            current = [arb(1)]
            for shift in range(1, width-rank+1):
                divisor = older[shift]
                if divisor is None or divisor.contains(0) or any(
                        previous[j] is None for j in [shift-1, shift, shift+1]):
                    current.append(None)
                else:
                    current.append((previous[shift]**2
                        -previous[shift-1]*previous[shift+1])/divisor)
        if rank >= min_rank:
            counts = {'positive': 0, 'negative': 0, 'unresolved': 0}
            for shift in range(max_shift+1):
                d = current[shift]
                sign = ('positive' if d is not None and d > 0 else
                        'negative' if d is not None and d < 0 else 'unresolved')
                counts[sign] += 1
                digest.update(f'{rank},{shift}:{sign}\n'.encode())
                if sign == 'negative' and first is None:
                    first = {'rank': rank, 'shift': shift, 'determinant': endpoints(d)}
            rows.append({'rank': rank, **counts})
        # Direct determinants independently check the recurrence on small cases.
        if rank in [2, 7, 16, 32]:
            for shift in [1, min(5, max_shift), max_shift]:
                direct = solid_minor(mu, rank, shift)
                d = current[shift]
                if d is not None and not (d-direct).contains(0):
                    raise ArithmeticError('condensation disagrees with direct determinant')
                checks.append({'rank': rank, 'shift': shift,
                               'direct': endpoints(direct),
                               'condensed': endpoints(d) if d is not None else None})
        if progress and (rank % 10 == 0 or rank == max_rank):
            progress(rank, rows[-1] if rows else None,
                     sum(x is None or x.contains(0) for x in current))
        if rank >= 2:
            older, previous = previous, current
    return {'per_rank': rows, 'first_negative_in_grid_order': first,
            'sign_digest_sha256': digest.hexdigest(), 'direct_checks': checks}


def run(max_rank, max_shift, min_rank, bits):
    OUT.mkdir(parents=True, exist_ok=True)
    stem = f'dh_rank{min_rank}-{max_rank}_shift0-{max_shift}_{bits}bits'
    start = time.monotonic()
    with ctx.workprec(bits):
        print('coefficient generation', max_rank+max_shift, bits, flush=True)
        mu = coefficients(max_rank+max_shift)
        # Algebraic normalization makes mu_0 exactly one, avoiding dependency loss.
        mu[0] = arb(1)
        coeff_path = OUT/f'{stem}_coefficients.json'
        coeff_path.write_text(json.dumps({'bits': bits,
            'coefficients': [endpoints(x) for x in mu]}, indent=2)+'\n')
        print('coefficients complete seconds', time.monotonic()-start, flush=True)
        scaled = [x*arb(100)**n for n, x in enumerate(mu)]
        result = condensate(scaled, max_rank, max_shift, min_rank,
            lambda rank, row, bad: print('rank', rank, row,
                'unresolved working cells', bad, 'seconds', time.monotonic()-start, flush=True))
        result.update({'status': 'certified_finite_grid_with_explicit_unresolved_cells',
            'bits': bits, 'min_rank': min_rank, 'max_rank': max_rank,
            'max_shift': max_shift, 'seconds': time.monotonic()-start,
            'ordinary_coefficient_convention': 'mu_n=[z^(2n)]Lambda(1/2+z)/Lambda(1/2)',
            'positive_rescaling': 'mu_n -> 100^n mu_n',
            'recurrence': 'D[r,s]=(D[r-1,s]^2-D[r-1,s-1]D[r-1,s+1])/D[r-2,s]; D[0,s]=D[r,0]=1',
            'coefficient_file': str(coeff_path), 'coefficient_sha256': sha256(coeff_path),
            'source_sha256': {n: sha256(Path(__file__).with_name(n)) for n in
                ['dh_high_rank_scan.py', 'dh_toeplitz_scan.py', 'davenport_heilbronn_control.py']},
            'scope': 'Finite solid-minor grid only. Unresolved entries are not positive. A negative is a certificate, not a globally first failure.'})
    (OUT/f'{stem}.json').write_text(json.dumps(result, indent=2)+'\n')
    print('result', result['first_negative_in_grid_order'], flush=True)
    return result


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--max-rank', type=int, default=520)
    p.add_argument('--max-shift', type=int, default=200)
    p.add_argument('--min-rank', type=int, default=430)
    p.add_argument('--bits', type=int, default=32768)
    a = p.parse_args()
    if not 1 <= a.min_rank <= a.max_rank <= 1000 or not 1 <= a.max_shift <= 1000 or not 512 <= a.bits <= 65536:
        p.error('bounded valid rank, shift and precision required')
    run(a.max_rank, a.max_shift, a.min_rank, a.bits)
