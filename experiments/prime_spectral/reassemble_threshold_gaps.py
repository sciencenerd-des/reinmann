"""Reassemble EVERY lower-operator matrix entry at different order/precision.

This reuses the existing generator and analytic bounds. It is an alternate
quadrature replay, not an independent implementation or an analytic proof.
It does not change a support endpoint or scan finite positivity minors.
"""
import argparse
import hashlib
import json
from pathlib import Path

from flint import arb, ctx

from certified_weil import endpoints
from compact_window_certificate import certify
from threshold_ground_gap import box, minmax_second_bound


def run(directory):
    witnesses = directory/'threshold_ground_gaps.json'
    rows = json.loads(witnesses.read_text())['results']
    output = []
    with ctx.workprec(512):
        for witness in rows:
            source = Path(witness['lower_operator_input'])
            if hashlib.sha256(source.read_bytes()).hexdigest() != witness['lower_operator_sha256']:
                raise ValueError('input certificate hash mismatch')
            original = json.loads(source.read_text())
            alternate = certify(original['half_width'], cutoff=original['cutoff'],
                                count=original['polynomial_count'],
                                order=original['gauss_order']+16, bits=512,
                                finite_lower=original['finite_lower'])
            allowance = (box(original['quadrature_operator_error'])+
                         box(alternate['quadrature_operator_error']))
            checks, largest = 0, arb(0)
            for old_sector, new_sector in zip(original['sectors'],alternate['sectors'],strict=True):
                if old_sector['parity'] != new_sector['parity']:
                    raise ValueError('parity mismatch')
                for old_row, new_row in zip(old_sector['quadrature_matrix'],
                                           new_sector['quadrature_matrix'],strict=True):
                    for old, new in zip(old_row,new_row,strict=True):
                        difference = abs(box(old)-box(new))
                        if not difference < allowance:
                            raise ArithmeticError('whole-entry quadrature comparison failed')
                        largest = max(largest, difference.upper())
                        checks += 1
            second, sectors = minmax_second_bound(alternate,witness['shift'])
            upper = box(witness['trial_ground_eigenvalue_upper'])
            gap = second-upper
            if not gap > (arb('857/100000') if witness['threshold_prime']==2 else arb('6e-9')):
                raise ArithmeticError('alternate full-gap witness did not close')
            output.append({'threshold_prime':witness['threshold_prime'],
                           'entries_compared':checks,'original_order':original['gauss_order'],
                           'alternate_order':alternate['gauss_order'],'alternate_bits':512,
                           'largest_entry_difference_upper':str(largest.fmpq()),
                           'combined_quadrature_allowance':endpoints(allowance),
                           'alternate_second_lower':endpoints(second),
                           'alternate_gap_lower':endpoints(gap),
                           'negative_counts':[s['negative_count'] for s in sectors],
                           'original_sha256':hashlib.sha256(source.read_bytes()).hexdigest()})
            print('all entries and full gap replayed at',witness['threshold_prime'],flush=True)
    sources = [Path(__file__), *[Path(__file__).with_name(p) for p in
               ['compact_window_certificate.py','threshold_ground_gap.py',
                'certified_weil.py','weil_matrix.py']]]
    return {'status':'all_lower_operator_entries_and_threshold_gaps_reassembled',
            'results':output,'source_hashes':{str(p):hashlib.sha256(p.read_bytes()).hexdigest()
                                             for p in sources},
            'witness_sha256':hashlib.sha256(witnesses.read_bytes()).hexdigest(),
            'scope':'Different quadrature orders and precision, same generator and analytic bounds. Not independent mathematical review, novelty clearance, or RH.'}


if __name__ == '__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--directory',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    result=run(args.directory)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
