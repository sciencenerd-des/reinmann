"""Certified bounded solid-minor scan of ordinary DH completed coefficients.

mu_n=[z^(2n)] Lambda(1/2+z)/Lambda(1/2). No n! weighting.
The scan order is (rank, shift), NOT an enumeration of all Toeplitz minors.
No failure on this finite grid is an outcome, not a PF-infinity proof.
"""
import hashlib
import json
from pathlib import Path

from flint import acb_series, arb, arb_mat, ctx

from certified_weil import endpoints
from davenport_heilbronn_control import kappa
from full_ground_fourier import sha256

OUT = Path('research/prime_spectral/verification_2026_10_12_remaining')


def coefficients(count):
    if type(count) is not int or count < 1:
        raise ValueError('positive count required')
    previous_cap = ctx.cap
    try:
        ctx.cap = 2*count+1
        s = acb_series([arb(1)/2, 1])
        k = kappa()
        H = sum((a*s.zeta(arb(r)/5) for r, a in
                 [(1, 1), (2, k), (3, -k), (4, -1)]),
                acb_series([0]))*(-s*arb(5).log()).exp()
        F = (s*(5/arb.pi()).log()/2).exp()*((s+1)/2).gamma()*H
        if not F[0].real > 0 or any(not F[j].contains(0)
                                   for j in range(1, 2*count, 2)):
            raise ArithmeticError('DH center/functional equation jet gate failed')
        if any(not F[2*j].imag.contains(0) for j in range(count+1)):
            raise ArithmeticError('DH coefficient reality gate failed')
        return [F[2*j].real/F[0].real for j in range(count+1)]
    finally:
        ctx.cap = previous_cap


def solid_minor(mu, rank, shift):
    if (type(rank) is not int or rank < 1 or type(shift) is not int or shift < 0
            or shift+rank > len(mu)):
        raise ValueError('valid rank, shift and enough coefficients required')
    return arb_mat([[mu[shift+i-j] if shift+i-j >= 0 else arb(0)
                     for j in range(rank)] for i in range(rank)]).det()


def scan(max_rank=80, max_shift=80):
    if (type(max_rank) is not int or not 1 <= max_rank <= 80
            or type(max_shift) is not int or not 1 <= max_shift <= 80):
        raise ValueError('bounded rank/shift 1..80 required')
    with ctx.workprec(4096):
        mu = coefficients(max_rank+max_shift)
        # Positive geometric rescaling preserves every Toeplitz minor sign.
        scaled = [x*arb(100)**n for n, x in enumerate(mu)]
        digest = hashlib.sha256()
        rows, first, checked = [], None, 0
        for rank in range(1, max_rank+1):
            counts = {'positive': 0, 'negative': 0, 'unresolved': 0}
            for shift in range(1, max_shift+1):
                d = solid_minor(scaled, rank, shift)
                sign = 'positive' if d > 0 else 'negative' if d < 0 else 'unresolved'
                counts[sign] += 1
                checked += 1
                digest.update(f'{rank},{shift}:{sign}\n'.encode())
                if sign == 'negative' and first is None:
                    first = {'rank': rank, 'shift': shift,
                             'scaled_determinant': endpoints(d)}
            rows.append({'rank': rank, **counts})
            if rank % 10 == 0:
                print('rank', rank, counts, flush=True)
        return {'status': 'certified_bounded_DH_solid_minor_scan',
                'bits': 4096, 'max_rank': max_rank, 'max_shift': max_shift,
                'ordinary_coefficient_convention': 'mu_n=[z^(2n)]Lambda(1/2+z)/Lambda(1/2)',
                'positive_geometric_rescaling': 'mu_n -> 100^n*mu_n',
                'coefficients': [endpoints(x) for x in mu],
                'checked': checked, 'per_rank': rows,
                'first_negative_in_this_grid_order': first,
                'sign_digest_sha256': digest.hexdigest(),
                'source_sha256': {n: sha256(Path(__file__).with_name(n)) for n in
                                 ['dh_toeplitz_scan.py', 'davenport_heilbronn_control.py']},
                'scope': 'Only rows shift..shift+rank-1 and columns 0..rank-1. No assertion about untested minors, global first failure, or PF infinity.'}


if __name__ == '__main__':
    OUT.mkdir(parents=True, exist_ok=True)
    result = scan()
    (OUT/'dh_toeplitz_rank80_shift80.json').write_text(json.dumps(result, indent=2)+'\n')
    print('first failure in grid:', result['first_negative_in_this_grid_order'])
