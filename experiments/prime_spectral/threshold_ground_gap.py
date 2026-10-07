"""Full-operator gap bounds at C=2 and C=3, not finite simplicity claims.

Uses the analytic infinite-complement min--max reduction already recorded
for compact_window_certificate. Floating eigenvectors only choose trial
coefficients; every trial Rayleigh quotient is then enclosed with Arb.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import mpmath as mp
from flint import arb, ctx

from certified_weil import certified_matrix, endpoints, inertia
from compact_window_certificate import certify


def box(record):
    return arb(record['lo']).union(arb(record['hi']))


def minmax_second_bound(data, shift):
    eta = arb(shift)
    error = box(data['quadrature_operator_error'])
    coupling = box(data['infinite_coupling_bound'])
    tail = box(data['infinite_tail_deviation'])
    beta = box(data['beta'])
    if not beta > eta:
        raise ArithmeticError('complement below proposed second-eigenvalue bound')
    negatives, sectors = 0, []
    for sector in data['sectors']:
        matrix = [[box(e) for e in row] for row in sector['quadrature_matrix']]
        n, pivots = inertia(matrix, eta+error)
        negatives += n
        sectors.append({'parity':sector['parity'], 'negative_count':n,
                        'shifted_pivots':[endpoints(p) for p in pivots]})
    if negatives != 1:
        raise ArithmeticError(f'exactly one lower-block eigenvalue required, got {negatives}')
    return eta-coupling-tail, sectors


def trial_upper(prime, modes=8):
    _, even, _ = certified_matrix(prime, modes)
    with mp.workdps(65):
        def midpoint(x):
            r=x.mid().fmpq()
            return mp.mpf(str(r.numerator))/mp.mpf(str(r.denominator))
        _, vectors = mp.eigsy(mp.matrix([[midpoint(x) for x in row] for row in even]))
        decimals = [mp.nstr(vectors[j,0],55) for j in range(len(even))]
    # The decimal strings denote exact rational trial coefficients, not
    # intervals claimed to enclose the true infinite-dimensional state.
    coefficients = [arb(s) for s in decimals]
    norm_sq = sum((x*x for x in coefficients),arb(0))
    numerator = sum((coefficients[i]*even[i][j]*coefficients[j]
                     for i in range(len(even)) for j in range(len(even))),arb(0))
    quotient = numerator/norm_sq
    if not norm_sq > 0 or not quotient.is_finite():
        raise ArithmeticError('trial Rayleigh quotient unresolved')
    return quotient, decimals


def generate(output_dir, reuse_lower=False):
    output_dir.mkdir(parents=True,exist_ok=True)
    source3=Path('research/prime_spectral/window_positivity_exp_1p2.json')
    source2=output_dir/'threshold_two_lower_operator.json'
    with ctx.workprec(384):
        data2=(json.loads(source2.read_text()) if reuse_lower else
               certify('7/20',count=80,order=64,finite_lower='1e-6'))
        if data2['half_width'] != '7/20' or data2['polynomial_count'] != 80:
            raise ArithmeticError('unexpected prime-two comparison data')
        dependencies = [Path(__file__), *[Path(__file__).with_name(name) for name in
                        ('compact_window_certificate.py', 'certified_weil.py', 'weil_matrix.py')]]
        data2['source_hashes'] = {p.name:hashlib.sha256(p.read_bytes()).hexdigest()
                                  for p in dependencies[1:]}
        source2.write_text(json.dumps(data2,indent=2)+'\n')
        data3=json.loads(source3.read_text())
        results=[]
        for prime,data,shift,source in [(2,data2,'1/100',source2),(3,data3,'11/100000000',source3)]:
            second,sectors=minmax_second_bound(data,shift)
            upper,coefficients=trial_upper(prime)
            gap=second-upper
            if not gap > 0:
                raise ArithmeticError(f'full gap did not close at prime {prime}')
            results.append({'threshold_prime':prime,'comparison_half_width':data['half_width'],
                            'second_eigenvalue_lower':endpoints(second),
                            'trial_ground_eigenvalue_upper':endpoints(upper),
                            'spectral_gap_lower':endpoints(gap),
                            'trial_even_cosine_coefficients':coefficients,
                            'lower_operator_input':str(source),
                            'lower_operator_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
                            'shift':shift,'inertia_sectors':sectors})
            print('full threshold gap enclosed at',prime,flush=True)
        return {'status':'two_full_operator_threshold_gaps_enclosed','bits':384,
                'results':results,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                'scope':'Arb verification plus written analytic infinite-complement/min--max reduction. Not Lean verification of the operator, novelty, or RH.'}


if __name__ == '__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir',type=Path,required=True)
    parser.add_argument('--reuse-lower',action='store_true',
                        help='Reuse the saved prime-two quadrature; independently verify it separately.')
    args=parser.parse_args()
    result=generate(args.output_dir,args.reuse_lower)
    (args.output_dir/'threshold_ground_gaps.json').write_text(json.dumps(result,indent=2)+'\n')
